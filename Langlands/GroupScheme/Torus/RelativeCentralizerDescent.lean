import Langlands.GroupScheme.Torus.RelativeCentralizerSmooth
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.SubgroupFunctor.ClosedCoverDescent
import Langlands.GroupScheme.SubgroupFunctor.EtaleLocality
import Langlands.GroupScheme.RelativeLevi.BorelEtaleTransport

/-! # Smooth closed centralizers of relative tori over arbitrary bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace SubgroupFunctor.CoverDescent

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The base changes of an actual subgroup satisfy all-test matching. -/
theorem isMatching_baseChange {K : Precoverage Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} K S) (F : SubgroupFunctor G) :
    IsMatching 𝒰 (fun k => F.baseChange (𝒰.f k)) := by
  intro i j V W a x hx
  rw [mem_baseChange, MulEquiv.apply_symm_apply]
  exact F.comp_mem a hx

/-- An actual subgroup is contained in the condition descended from its
base changes. -/
theorem le_subgroup_baseChange {K : Precoverage Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} K S) (F : SubgroupFunctor G) :
    F ≤ subgroup 𝒰 (fun k => F.baseChange (𝒰.f k)) := by
  intro U x hx i V a
  rw [mem_baseChange, MulEquiv.apply_symm_apply]
  exact F.comp_mem a hx

end SubgroupFunctor.CoverDescent

variable {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}

/-- Commutation on every test scheme is detected on an étale cover of the base. -/
theorem torusCentralizer_eq_coverDescent
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) (t : T.toGrp ⟶ G) :
    torusCentralizer t = SubgroupFunctor.CoverDescent.subgroup 𝒰
      (fun k => (torusCentralizer t).baseChange (𝒰.f k)) := by
  apply le_antisymm (SubgroupFunctor.CoverDescent.le_subgroup_baseChange 𝒰 _) ?_
  intro U x hx V a s
  let 𝒱 := 𝒰.pullback₁ V.hom
  let : EffectiveEpiFamily 𝒱.X 𝒱.f :=
    SubgroupFunctor.effectiveEpiFamily_etaleCover 𝒱
  apply Over.OverMorphism.ext
  apply EffectiveEpiFamily.hom_ext 𝒱.X 𝒱.f
  intro k
  let W : Over (𝒰.X k) := Over.mk (pullback.snd V.hom (𝒰.f k))
  let q : (Over.map (𝒰.f k)).obj W ⟶ V :=
    Over.homMk (pullback.fst V.hom (𝒰.f k)) pullback.condition
  have hm := hx k W (q ≫ a)
  rw [SubgroupFunctor.mem_baseChange, MulEquiv.apply_symm_apply] at hm
  have hc := hm _ (𝟙 _) (q ≫ s)
  simp only [Category.id_comp, Category.assoc] at hc
  have he := congrArg (fun f => f.left) hc.eq
  change (q ≫ ((a ≫ x) * (s ≫ t.hom.hom))).left =
    (q ≫ ((s ≫ t.hom.hom) * (a ≫ x))).left
  simpa only [MonObj.comp_mul, Category.assoc] using he

/-- Smooth closed representability of a torus centralizer descends along an
arbitrary étale cover. -/
theorem torusCentralizer_hasSmoothClosedRepresentative_of_etaleCover
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) (t : T.toGrp ⟶ G)
    (h : ∀ k, ((torusCentralizer t).baseChange (𝒰.f k)).HasSmoothClosedRepresentative) :
    (torusCentralizer t).HasSmoothClosedRepresentative := by
  let F := torusCentralizer t
  have hclosed : F.IsClosedRepresentable := by
    change (torusCentralizer t).IsClosedRepresentable
    rw [torusCentralizer_eq_coverDescent 𝒰 t]
    apply SubgroupFunctor.CoverDescent.isClosedRepresentable_subgroup_etale 𝒰 _
      (SubgroupFunctor.CoverDescent.isMatching_baseChange 𝒰 F)
    intro k
    obtain ⟨C, j, hj, _, hrep⟩ := h k
    exact ⟨C, j, hrep, hj⟩
  let C := SubgroupFunctor.ClosedRepresentative.ofIsClosedRepresentable hclosed
  refine ⟨C.group, C.hom, C.closed, ?_, C.represents⟩
  apply RelativeLevi.smooth_of_etale_cover_pullbacks 𝒰
  intro k
  obtain ⟨L, j, _, hL, hrep⟩ := h k
  exact smooth_of_over_iso
    ((Grp.forget _).mapIso ((C.represents.baseChange (𝒰.f k)).isoOfIsRepresentedBy hrep)) hL

/-- The centralizer of a split torus in a smooth relatively affine group is
smooth and closed over an arbitrary base scheme. -/
theorem splitTorusCentralizer_hasSmoothClosedRepresentative_of_relativelyAffine
    [IsAffineHom G.X.hom] (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hG : Smooth G.X.hom) :
    (torusCentralizer t).HasSmoothClosedRepresentative := by
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    S.affineOpenCover.openCover.changeProp (fun k => inferInstance)
  apply torusCentralizer_hasSmoothClosedRepresentative_of_etaleCover 𝒰 t
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
  change ((torusCentralizer t).baseChange b).HasSmoothClosedRepresentative
  rw [← torusCentralizer_baseChange b (T := T) t]
  exact splitTorusCentralizer_hasSmoothClosedRepresentative_overRing
    (R := S.affineOpenCover.X k) (T := (CommGroupScheme.baseChange b).obj T)
    (B.map t) (hT.baseChange b)
    (MorphismProperty.pullback_snd G.X.hom b hG)

/-- The all-test centralizer of any relative-torus homomorphism into a smooth
relatively affine group has a smooth closed representative over the original
arbitrary base. The torus map need not be an immersion. -/
theorem relativeTorusCentralizer_hasSmoothClosedRepresentative
    [IsAffineHom G.X.hom] (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (hG : Smooth G.X.hom) :
    (torusCentralizer t).HasSmoothClosedRepresentative := by
  obtain ⟨𝒰, h𝒰⟩ := hT
  apply torusCentralizer_hasSmoothClosedRepresentative_of_etaleCover 𝒰 t
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  change ((torusCentralizer t).baseChange b).HasSmoothClosedRepresentative
  rw [← torusCentralizer_baseChange b (T := T) t]
  exact splitTorusCentralizer_hasSmoothClosedRepresentative_of_relativelyAffine
    (T := (CommGroupScheme.baseChange b).obj T) (B.map t) (h𝒰 k)
    (MorphismProperty.pullback_snd G.X.hom b hG)

/-- The actual chosen smooth closed group scheme representing the centralizer,
with its inclusion and all-test representing property. -/
def relativeTorusCentralizerModel
    [IsAffineHom G.X.hom] (t : T.toGrp ⟶ G) (hT : RelativeTorus.IsTorus T.toGrp)
    (hG : Smooth G.X.hom) :
    Σ C : GroupScheme S, {c : C ⟶ G // IsClosedSubgroup c ∧ Smooth C.X.hom ∧
      (torusCentralizer t).IsRepresentedBy c} := by
  let h := relativeTorusCentralizer_hasSmoothClosedRepresentative t hT hG
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Langlands.GroupScheme
