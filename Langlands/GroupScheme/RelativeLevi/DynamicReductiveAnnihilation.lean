import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.PseudoReductiveCentralCocharacterProof
import Langlands.GroupScheme.Dynamic.ParabolicCharacters
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Surjections from dynamic parabolics kill their contracting subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

private theorem isIso_of_residueField_fibres
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (hf : ∀ s : S, IsIso ((Over.pullback (S.fromSpecResidueField s)).map f)) :
    IsIso f := by
  have : IsOpenImmersion f.left :=
    Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise f fun s => by
      let := hf s
      exact inferInstanceAs
        (IsOpenImmersion (((Over.forget _).map
          ((Over.pullback (S.fromSpecResidueField s)).map f))))
  have : Surjective f.left := by
    refine ⟨fun y => ?_⟩
    let s : S := Y.hom y
    obtain ⟨y', hy', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.hom) (g := S.fromSpecResidueField s) y
      (IsLocalRing.closedPoint (S.residueField s))
      (Scheme.fromSpecResidueField_apply _ _).symm
    let := hf s
    have : IsIso ((Over.pullback (S.fromSpecResidueField s)).map f).left :=
      Functor.map_isIso (Over.forget (Spec (S.residueField s)))
        ((Over.pullback (S.fromSpecResidueField s)).map f)
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (S.fromSpecResidueField s)).map f).left).surjective y'
    have hcomp : pullback.fst X.hom (S.fromSpecResidueField s) ≫ f.left =
        ((Over.pullback (S.fromSpecResidueField s)).map f).left ≫
          pullback.fst Y.hom (S.fromSpecResidueField s) :=
      (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst X.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx']
    change (pullback.fst X.hom (S.fromSpecResidueField s) ≫ f.left) x' =
      (((Over.pullback (S.fromSpecResidueField s)).map f).left ≫
        pullback.fst Y.hom (S.fromSpecResidueField s)) x'
    exact congrArg (fun a => a x') hcomp
  have : IsIso f.left :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have : IsIso ((Over.forget S).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Over.forget S)

private theorem range_eq_top_of_isIso_over
    {S : Scheme.{u}} {A H : GroupScheme S} (j : A ⟶ H) [IsIso j.hom.hom] :
    SubgroupFunctor.range j = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  refine iff_of_true ?_ (Subgroup.mem_top _)
  exact SubgroupFunctor.mem_range.mpr
    ⟨x ≫ inv j.hom.hom, by simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

private theorem isIso_over_of_range_eq_top
    {S : Scheme.{u}} {A H : GroupScheme S} (j : A ⟶ H)
    [Mono j.hom.hom] (hj : SubgroupFunctor.range j = ⊤) : IsIso j.hom.hom := by
  have hmem : 𝟙 H.X ∈ (SubgroupFunctor.range j).carrier H.X := by
    rw [hj]
    exact Subgroup.mem_top _
  obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp hmem
  refine ⟨⟨s, ?_, hs⟩⟩
  apply (cancel_mono j.hom.hom).mp
  rw [Category.assoc, hs, Category.comp_id, Category.id_comp]

/-- A surjective homomorphism whose image lies in a dynamic parabolic forces that
parabolic to be the full group, over an arbitrary base. -/
theorem parabolic_eq_top_of_surjective_range
    {S : Scheme.{u}} {P H : GroupScheme S} [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (ψ : (Gm S).toGrp ⟶ H) (f : P ⟶ H)
    (hf : Surjective f.hom.hom.left)
    (himage : SubgroupFunctor.range f ≤ parabolic ψ) : parabolic ψ = ⊤ := by
  obtain ⟨A, j, hjc, _, hj⟩ := (dynamicBaseRepresentability S H ψ).1
  have : Smooth A.X.hom := ((dynamicBaseSmoothConnected S H ψ A j).2.1 hj).1
  have hmem : f.hom.hom ∈ (SubgroupFunctor.range j).carrier P.X := by
    rw [hj.2]
    exact himage P.X (SubgroupFunctor.mem_range.mpr ⟨𝟙 P.X, Category.id_comp _⟩)
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp hmem
  have : Surjective j.hom.hom.left := by
    have hc : Surjective (a.left ≫ j.hom.hom.left) := by
      rw [← Over.comp_left, ha]
      exact hf
    exact Surjective.of_comp a.left j.hom.hom.left
  have : IsIso j.hom.hom := by
    apply isIso_of_residueField_fibres
    intro s
    let b := S.fromSpecResidueField s
    have : IsClosedImmersion (((Over.pullback b).map j.hom.hom).left) :=
      MorphismProperty.overPullbackMap (P := @IsClosedImmersion) b j.hom.hom hjc
    have : Surjective (((Over.pullback b).map j.hom.hom).left) :=
      MorphismProperty.overPullbackMap (P := @Surjective) b j.hom.hom inferInstance
    have : Smooth ((Over.pullback b).obj H.X).hom :=
      inferInstanceAs (Smooth (pullback.snd H.X.hom b))
    have : AlgebraicGeometry.IsReduced ((Over.pullback b).obj H.X).left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        (S.residueField s) _ ((Over.pullback b).obj H.X).hom
    have : IsIso (((Over.pullback b).map j.hom.hom).left) :=
      AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective _
    have : IsIso ((Over.forget (Spec (S.residueField s))).map
        ((Over.pullback b).map j.hom.hom)) := ‹IsIso (((Over.pullback b).map j.hom.hom).left)›
    exact isIso_of_reflects_iso _ (Over.forget (Spec (S.residueField s)))
  exact hj.2.symm.trans (range_eq_top_of_isIso_over j)

/-- A cocharacter of a reductive group whose dynamic parabolic is full centralizes
the whole group over the base, including its nilpotent structure. -/
theorem centralizer_eq_top_of_parabolic_eq_top
    {S : Scheme.{u}} {H : GroupScheme S} (hH : IsReductive H)
    (ψ : (Gm S).toGrp ⟶ H) (hψ : parabolic ψ = ⊤) : centralizer ψ = ⊤ := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  obtain ⟨Z, j, _, _, hj⟩ := (dynamicBaseRepresentability S H ψ).2.2
  have : Smooth Z.X.hom := ((dynamicBaseSmoothConnected S H ψ Z j).2.2 hj).1
  have : IsIso j.hom.hom := by
    apply isIso_of_residueField_fibres
    intro s
    let b := S.fromSpecResidueField s
    have hP : parabolic (baseChangeCocharacter b ψ) = ⊤ := by
      rw [parabolic_baseChange, hψ, SubgroupFunctor.top_baseChange]
    have hZ := (pseudoReductiveCentralCocharacter (S.residueField s)
      ((GroupScheme.baseChange b).obj H)
      (hH.isConnectedReductive_residueFiber s).isPseudoReductive
      (baseChangeCocharacter b ψ)).mp hP
    have hjb := isRepresentedBy_centralizer_baseChange b ψ hj
    have : Mono ((GroupScheme.baseChange b).map j).hom.hom := hjb.1
    exact isIso_over_of_range_eq_top ((GroupScheme.baseChange b).map j) (hjb.2.trans hZ)
  exact hj.2.symm.trans (range_eq_top_of_isIso_over j)

/-- In a reductive target, a full dynamic parabolic has trivial contracting
subgroup on every test scheme. -/
theorem unipotent_eq_one_of_parabolic_eq_top
    {S : Scheme.{u}} {H : GroupScheme S} (hH : IsReductive H)
    (ψ : (Gm S).toGrp ⟶ H) (hψ : parabolic ψ = ⊤)
    {T : Over S} {g : T ⟶ H.X} (hg : g ∈ (unipotent ψ).carrier T) : g = 1 := by
  let : IsAffineHom H.X.hom := hH.isAffineHom
  have hz : g ∈ (centralizer ψ).carrier T := by
    rw [centralizer_eq_top_of_parabolic_eq_top hH ψ hψ]
    exact Subgroup.mem_top _
  exact (hasLimit_of_mem_centralizer ψ hz).unique ψ hg

/-- A surjection from a group with full dynamic parabolic to a reductive group
kills every contracting point, as a morphism over the base. -/
theorem comp_eq_one_of_full_parabolic
    {S : Scheme.{u}} {P H : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ P) (hχ : parabolic χ = ⊤)
    (f : P ⟶ H) (hH : IsReductive H) (hf : Surjective f.hom.hom.left)
    {T : Over S} {g : T ⟶ P.X} (hg : g ∈ (unipotent χ).carrier T) :
    g ≫ f.hom.hom = 1 := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  have himage : SubgroupFunctor.range f ≤ parabolic (χ ≫ f) := by
    rintro T x ⟨p, rfl⟩
    apply parabolic_le_comap χ f T
    rw [hχ]
    exact Subgroup.mem_top _
  exact unipotent_eq_one_of_parabolic_eq_top hH (χ ≫ f)
    (parabolic_eq_top_of_surjective_range (χ ≫ f) f hf himage)
    (unipotent_le_comap χ f T hg)

/-- Every surjection from a represented dynamic parabolic of a smooth affine
group to a reductive group kills the supplied contracting subgroup. -/
theorem annihilates_contracting_subgroup
    {S : Scheme.{u}} {G P U H : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) {i : P ⟶ G} {r : U ⟶ P}
    (hP : (parabolic χ).IsRepresentedBy i)
    (hU : (unipotent χ).IsRepresentedBy (r ≫ i))
    (f : P ⟶ H) (hH : IsReductive H) (hf : Surjective f.hom.hom.left) :
    r ≫ f = 0 := by
  obtain ⟨A, j, hjc, _, hj⟩ := (dynamicBaseRepresentability S G χ).1
  have hic : IsClosedSubgroup i := by
    rw [← hP.isoOfIsRepresentedBy_hom_comp hj]
    exact (IsClosedSubgroup.of_iso (hP.isoOfIsRepresentedBy hj)).comp hjc
  let χP := cocharacterToParabolic hP
  have hχP : parabolic χP = ⊤ := by
    rw [parabolic_eq_comap_of_isClosedSubgroup χP i hic,
      cocharacterToParabolic_comp hP, ← hP.2]
    exact (SubgroupFunctor.range_le_iff_comap_eq_top).mp (fun _ _ h => h)
  have hr : r.hom.hom ∈ (unipotent χP).carrier U.X := by
    rw [unipotent_eq_comap_of_isClosedSubgroup χP i hic,
      cocharacterToParabolic_comp hP, SubgroupFunctor.mem_comap]
    change (r ≫ i).hom.hom ∈ (unipotent χ).carrier U.X
    rw [← hU.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 U.X, Category.id_comp _⟩
  apply Grp.hom_ext
  change r.hom.hom ≫ f.hom.hom = 1
  exact comp_eq_one_of_full_parabolic χP hχP f hH hf hr

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme

/-- The contracting subgroup of any represented dynamic parabolic in a reductive
group is killed by every scheme-surjective homomorphism to a reductive group. -/
def DynamicReductiveAnnihilationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (χ : (Gm S).toGrp ⟶ G)
    (i : P ⟶ G) (r : U ⟶ P),
    IsReductive G → (Dynamic.parabolic χ).IsRepresentedBy i →
      (Dynamic.unipotent χ).IsRepresentedBy (r ≫ i) →
        ∀ (H : GroupScheme S) (f : P ⟶ H),
          IsReductive H → Surjective f.hom.hom.left → r ≫ f = 0

/-- Dynamic reductive annihilation over every scheme. -/
theorem dynamicReductiveAnnihilation : DynamicReductiveAnnihilationStatement.{u} := by
  intro S G P U χ i r hG hP hU H f hH hf
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact Dynamic.annihilates_contracting_subgroup χ hP hU f hH hf

end Langlands.GroupScheme
