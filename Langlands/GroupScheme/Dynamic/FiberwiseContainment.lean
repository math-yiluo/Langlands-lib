import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion

/-! # Detection of dynamic parabolic containment on residue fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace DynamicContainment

/-- A morphism between families is an isomorphism if it is so on every residue fibre,
provided its source is flat and locally finitely presented and its target is locally
of finite type over the base. -/
theorem isIso_of_residueFibres {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [Flat X.hom] [LocallyOfFinitePresentation X.hom] [LocallyOfFiniteType Y.hom]
    (hf : ∀ s : S, IsIso ((Over.pullback (S.fromSpecResidueField s)).map f).left) :
    IsIso f.left := by
  have hopen : IsOpenImmersion f.left :=
    Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise f fun s => by
      have := hf s
      infer_instance
  have hsurj : Surjective f.left := by
    refine ⟨fun y => ?_⟩
    let s : S := Y.hom y
    obtain ⟨y', hy', -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Y.hom) (g := S.fromSpecResidueField s) y
      (IsLocalRing.closedPoint (S.residueField s))
      (Scheme.fromSpecResidueField_apply _ _).symm
    have := hf s
    obtain ⟨x', hx'⟩ :=
      (((Over.pullback (S.fromSpecResidueField s)).map f).left).surjective y'
    have key : pullback.fst X.hom (S.fromSpecResidueField s) ≫ f.left =
        ((Over.pullback (S.fromSpecResidueField s)).map f).left ≫
          pullback.fst Y.hom (S.fromSpecResidueField s) := by
      exact (pullback.lift_fst _ _ _).symm
    refine ⟨pullback.fst X.hom (S.fromSpecResidueField s) x', ?_⟩
    rw [← hy', ← hx']
    exact congrArg (fun z => z x') key
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hopen, hsurj⟩

/-- A monomorphic representing homomorphism with full functorial range is an
isomorphism on the underlying schemes over the base. -/
theorem isIso_of_range_eq_top {S : Scheme.{u}} {H K : GroupScheme S}
    (f : K ⟶ H) [Mono f.hom.hom]
    (hf : SubgroupFunctor.range f = ⊤) : IsIso f.hom.hom := by
  have hmem : 𝟙 H.X ∈ (SubgroupFunctor.range f).carrier H.X := by
    rw [hf]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := SubgroupFunctor.mem_range.mp hmem
  have : IsSplitEpi f.hom.hom := IsSplitEpi.mk' ⟨g, hg⟩
  exact isIso_of_mono_of_isSplitEpi _

end DynamicContainment

namespace Dynamic

/-- If the second cocharacter lies in the first dynamic parabolic, containment of
the two dynamic parabolics can be tested on all residue fibres of an arbitrary base.
The smoothness of the dynamic intersection is essential in this argument. -/
theorem parabolic_le_of_residueFibres {S : Scheme.{u}} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ χ' : (Gm S).toGrp ⟶ G)
    (hχ' : SubgroupFunctor.range χ' ≤ parabolic χ)
    (hf : ∀ s : S,
      parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ) ≤
        parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ')) :
    parabolic χ ≤ parabolic χ' := by
  obtain ⟨H, i, hic, hiL, hi⟩ :=
    (dynamicBaseRepresentability S G χ).1
  have : IsClosedImmersion i.hom.hom.left := hic
  have : Mono i.hom.hom := hi.1
  have : Smooth H.X.hom := (dynamicBaseSmoothConnected S G χ H i).2.1 hi |>.1
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let χH := hi.liftOfLE χ' hχ'
  have hχH : χH ≫ i = χ' := hi.liftOfLE_comp χ' hχ'
  obtain ⟨K, κ, hκc, hκL, hκ⟩ :=
    (dynamicBaseRepresentability S H χH).1
  have : Mono κ.hom.hom := hκ.1
  have : Smooth K.X.hom := (dynamicBaseSmoothConnected S H χH K κ).2.1 hκ |>.1
  have hP : parabolic χH = (parabolic χ').comap i := by
    rw [← hχH]
    exact parabolic_eq_comap_of_isClosedSubgroup χH i hic
  have hfκ : ∀ s : S,
      IsIso ((Over.pullback (S.fromSpecResidueField s)).map κ.hom.hom).left := by
    intro s
    let b := S.fromSpecResidueField s
    have hκb := hκ.baseChange b
    have hr : SubgroupFunctor.range ((GroupScheme.baseChange b).map κ) = ⊤ := by
      rw [hκb.2]
      ext U x
      refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
      change baseChangePointsEquiv b H U x ∈ (parabolic χH).carrier _
      rw [hP, SubgroupFunctor.mem_comap]
      have hx : x ≫ ((GroupScheme.baseChange b).map i).hom.hom ∈
          (parabolic (baseChangeCocharacter b χ)).carrier U := by
        rw [parabolic_baseChange, ← hi.2, ← SubgroupFunctor.range_baseChangeHom]
        exact SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
      have hx' := hf s U hx
      rw [parabolic_baseChange, SubgroupFunctor.mem_baseChange,
        baseChangePointsEquiv_comp] at hx'
      exact hx'
    have : Mono ((GroupScheme.baseChange b).map κ).hom.hom := hκb.1
    have : IsIso ((GroupScheme.baseChange b).map κ).hom.hom :=
      DynamicContainment.isIso_of_range_eq_top _ hr
    change IsIso ((Over.forget _).map ((GroupScheme.baseChange b).map κ).hom.hom)
    infer_instance
  have : IsIso κ.hom.hom.left :=
    DynamicContainment.isIso_of_residueFibres κ.hom.hom hfκ
  have : IsIso ((Over.forget S).map κ.hom.hom) :=
    inferInstanceAs (IsIso κ.hom.hom.left)
  have : IsIso κ.hom.hom := isIso_of_reflects_iso κ.hom.hom (Over.forget S)
  intro U g hg
  rw [← hi.2] at hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hx : x ∈ (parabolic χH).carrier U := by
    rw [← hκ.2]
    exact SubgroupFunctor.mem_range.mpr ⟨x ≫ inv κ.hom.hom, by simp⟩
  rw [hP, SubgroupFunctor.mem_comap] at hx
  exact hx

/-- The all-field-valued-point version of residue-fibre detection. -/
theorem parabolic_le_of_fieldBaseChange {S : Scheme.{u}} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ χ' : (Gm S).toGrp ⟶ G)
    (hχ' : SubgroupFunctor.range χ' ≤ parabolic χ)
    (hf : ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
      parabolic (baseChangeCocharacter b χ) ≤ parabolic (baseChangeCocharacter b χ')) :
    parabolic χ ≤ parabolic χ' :=
  parabolic_le_of_residueFibres χ χ' hχ' fun s =>
    hf (S.residueField s) (S.fromSpecResidueField s)

/-- The homomorphism between chosen representatives of two dynamic parabolics
constructed from containment on all residue fibres. -/
def parabolicContainmentHomOfResidueFibres {S : Scheme.{u}} {G H K : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ χ' : (Gm S).toGrp ⟶ G)
    (hχ' : SubgroupFunctor.range χ' ≤ parabolic χ)
    (hf : ∀ s : S,
      parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ) ≤
        parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ'))
    (i : H ⟶ G) (j : K ⟶ G)
    (hi : (parabolic χ).IsRepresentedBy i)
    (hj : (parabolic χ').IsRepresentedBy j) : H ⟶ K :=
  hj.liftOfLE i (hi.2.trans_le (parabolic_le_of_residueFibres χ χ' hχ' hf))

/-- The constructed containment homomorphism commutes with the inclusions. -/
theorem parabolicContainmentHomOfResidueFibres_comp
    {S : Scheme.{u}} {G H K : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ χ' : (Gm S).toGrp ⟶ G)
    (hχ' : SubgroupFunctor.range χ' ≤ parabolic χ)
    (hf : ∀ s : S,
      parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ) ≤
        parabolic (baseChangeCocharacter (S.fromSpecResidueField s) χ'))
    (i : H ⟶ G) (j : K ⟶ G)
    (hi : (parabolic χ).IsRepresentedBy i)
    (hj : (parabolic χ').IsRepresentedBy j) :
    parabolicContainmentHomOfResidueFibres χ χ' hχ' hf i j hi hj ≫ j = i :=
  hj.liftOfLE_comp i _

end Dynamic

end Langlands.GroupScheme
