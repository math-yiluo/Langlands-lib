import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionUniqueness
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Finite-fiber affine neighborhoods and the global Weil-restriction inverse -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

/-- The intrinsic condition that every finite set of scheme points lies in
one affine open. This is an explicit geometric hypothesis. -/
def HasFiniteAffineNeighborhoods (X : Scheme.{u}) : Prop :=
  ∀ s : Set X, s.Finite → ∃ U : X.affineOpens, s ⊆ U.val

/-- An affine scheme has the finite-set affine-neighborhood property. -/
theorem hasFiniteAffineNeighborhoods_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    HasFiniteAffineNeighborhoods X := by
  intro s _
  exact ⟨⟨⊤, isAffineOpen_top X⟩, Set.subset_univ s⟩

/-- Finite fibers and finite-set affine neighborhoods produce an open cover
of the base, each member forcing an entire fiber into one target affine. -/
theorem finiteAffineFactorizationOpens_cover
    {Z W X : Scheme.{u}} (π : Z ⟶ W) [IsFinite π] (e : Z ⟶ X)
    (hX : HasFiniteAffineNeighborhoods X) (w : W) :
    ∃ U : X.affineOpens, w ∈ universallyClosedFactorizationOpen π e U.val := by
  obtain ⟨U, hU⟩ := hX (e '' (π ⁻¹' {w}))
    ((π.finite_preimage_singleton w).image e)
  refine ⟨U, (mem_universallyClosedFactorizationOpen π e U.val w).mpr ?_⟩
  intro z hz
  exact hU ⟨z, hz, rfl⟩

/-- The actual open cover of a finite morphism's target obtained from
whole-fiber factorization into target affine opens. -/
def finiteAffineFactorizationOpenCover
    {Z W X : Scheme.{u}} (π : Z ⟶ W) [IsFinite π] (e : Z ⟶ X)
    (hX : HasFiniteAffineNeighborhoods X) : W.OpenCover :=
  W.openCoverOfIsOpenCover
    (fun U : X.affineOpens => universallyClosedFactorizationOpen π e U.val)
    (by
      apply IsOpenCover.mk
      apply top_unique
      intro w _
      exact Opens.mem_iSup.mpr (finiteAffineFactorizationOpens_cover π e hX w))

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- On a test scheme, the actual open locus where a given base-changed
morphism has its whole fiber in one specified affine open of the target. -/
def affineChartWeilRestrictionSourceOpen
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) : T.left.Opens := by
  let : IsFinite (Spec.algebraMap A B) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact universallyClosedFactorizationOpen
    (pullback.fst T.hom (Spec.algebraMap A B)) q.left U.val

/-- The actual finite-fiber affine-neighborhood cover of an arbitrary test
scheme for a given morphism from its base change. -/
def affineChartWeilRestrictionSourceCover
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y) :
    T.left.OpenCover := by
  let : IsFinite (Spec.algebraMap A B) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact finiteAffineFactorizationOpenCover
    (pullback.fst T.hom (Spec.algebraMap A B)) q.left hY

/-- A whole-fiber factorization neighborhood as a scheme over `Spec A`. -/
def affineChartWeilRestrictionSourceChart
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) : Over (Spec (CommRingCat.of A)) :=
  openOver A T (affineChartWeilRestrictionSourceOpen A B Y T q U)

/-- The actual inclusion of a whole-fiber factorization neighborhood. -/
def affineChartWeilRestrictionSourceChartι
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionSourceChart A B Y T q U ⟶ T :=
  openOverι A T (affineChartWeilRestrictionSourceOpen A B Y T q U)

omit [Module.Projective A B] [LocallyOfFiniteType Y.hom] in
/-- On the base change of each source neighborhood, the original morphism
really lands in its specified target affine open. -/
theorem affineChartWeilRestrictionSourceChart_range
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) :
    Set.range (((Over.pullback (Spec.algebraMap A B)).map
      (affineChartWeilRestrictionSourceChartι A B Y T q U)) ≫ q).left ⊆ U.val := by
  let : IsFinite (Spec.algebraMap A B) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  apply (range_subset_factorizationOpen_iff
    (pullback.fst T.hom (Spec.algebraMap A B)) q.left U.val
    (affineChartWeilRestrictionSourceChartι A B Y T q U).left _ _
    (ringBaseChange_map_isPullback A B
      (affineChartWeilRestrictionSourceChartι A B Y T q U))).mp
  rintro _ ⟨t, rfl⟩
  exact t.property

/-- The actual restriction of the given morphism into its target affine,
using the whole-fiber source neighborhood. -/
def affineChartWeilRestrictionSourceChartTarget
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) :
    ringBaseChange A B (affineChartWeilRestrictionSourceChart A B Y T q U) ⟶
      openOver B Y U.val :=
  relativeOpenLift B
    ((Over.pullback (Spec.algebraMap A B)).map
      (affineChartWeilRestrictionSourceChartι A B Y T q U) ≫ q) U.val
    (affineChartWeilRestrictionSourceChart_range A B Y T q U)

omit [Module.Projective A B] [LocallyOfFiniteType Y.hom] in
@[simp]
theorem affineChartWeilRestrictionSourceChartTarget_fac
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionSourceChartTarget A B Y T q U ≫ openOverι B Y U.val =
      (Over.pullback (Spec.algebraMap A B)).map
        (affineChartWeilRestrictionSourceChartι A B Y T q U) ≫ q :=
  relativeOpenLift_fac B _ U.val _

/-- The actual local inverse morphism into the glued scheme, obtained from
the established affine representing equivalence. -/
def affineChartWeilRestrictionLocalInverse
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionSourceChart A B Y T q U ⟶
      affineChartWeilRestriction A B Y :=
  (affineWeilRestrictionTestEquiv A B (openOver B Y U.val)
    (affineChartWeilRestrictionSourceChart A B Y T q U)).symm
      (affineChartWeilRestrictionSourceChartTarget A B Y T q U) ≫
    affineChartWeilRestrictionι A B Y U

/-- Applying the canonical comparison to the constructed local inverse is
exactly restriction of the given morphism to that source neighborhood. -/
theorem affineChartWeilRestrictionLocalInverse_comparison
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionComparison A B Y
        (affineChartWeilRestrictionSourceChart A B Y T q U)
        (affineChartWeilRestrictionLocalInverse A B Y T q U) =
      (Over.pullback (Spec.algebraMap A B)).map
        (affineChartWeilRestrictionSourceChartι A B Y T q U) ≫ q := by
  rw [affineChartWeilRestrictionLocalInverse,
    affineChartWeilRestrictionComparison_chart]
  change affineWeilRestrictionTestEquiv A B (openOver B Y U.val) _
    ((affineWeilRestrictionTestEquiv A B (openOver B Y U.val) _).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply, affineChartWeilRestrictionSourceChartTarget_fac]

variable [IsSeparated Y.hom]

/-- The constructed local inverse morphisms agree on the actual pairwise
pullbacks of source neighborhoods. -/
theorem affineChartWeilRestrictionLocalInverse_compatible
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U V : Y.left.affineOpens) :
    pullback.fst
        (affineChartWeilRestrictionSourceChartι A B Y T q U).left
        (affineChartWeilRestrictionSourceChartι A B Y T q V).left ≫
          (affineChartWeilRestrictionLocalInverse A B Y T q U).left =
      pullback.snd
        (affineChartWeilRestrictionSourceChartι A B Y T q U).left
        (affineChartWeilRestrictionSourceChartι A B Y T q V).left ≫
          (affineChartWeilRestrictionLocalInverse A B Y T q V).left := by
  let F := Over.pullback (Spec.algebraMap A B)
  let S := affineChartWeilRestrictionSourceChart A B Y T q
  let j := affineChartWeilRestrictionSourceChartι A B Y T q
  let p := affineChartWeilRestrictionLocalInverse A B Y T q
  let R : Over (Spec (CommRingCat.of A)) :=
    Over.mk (pullback.fst (j U).left (j V).left ≫ (S U).hom)
  let a : R ⟶ S U := Over.homMk (pullback.fst (j U).left (j V).left)
  let b : R ⟶ S V := Over.homMk (pullback.snd (j U).left (j V).left) (by
    change pullback.snd _ _ ≫ (S V).hom = pullback.fst _ _ ≫ (S U).hom
    rw [← Over.w (j U), ← Over.w (j V),
      ← Category.assoc, ← Category.assoc, pullback.condition])
  have hab : a ≫ j U = b ≫ j V := by
    apply Over.OverMorphism.ext
    exact pullback.condition
  have h : a ≫ p U = b ≫ p V := by
    apply affineChartWeilRestrictionComparison_injective A B Y R
    rw [affineChartWeilRestrictionComparison_natural,
      affineChartWeilRestrictionComparison_natural,
      affineChartWeilRestrictionLocalInverse_comparison,
      affineChartWeilRestrictionLocalInverse_comparison]
    change F.map a ≫ (F.map (j U) ≫ q) = F.map b ≫ (F.map (j V) ≫ q)
    erw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp, hab]
  exact congrArg (fun k => k.left) h

/-- The actual global inverse morphism, obtained by gluing the local
inverse morphisms over the finite-fiber affine-neighborhood cover. -/
def affineChartWeilRestrictionInverse
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y) :
    T ⟶ affineChartWeilRestriction A B Y := by
  let 𝒰 := affineChartWeilRestrictionSourceCover A B Y hY T q
  let p := affineChartWeilRestrictionLocalInverse A B Y T q
  let hcompat := affineChartWeilRestrictionLocalInverse_compatible A B Y T q
  let f := 𝒰.glueMorphisms (fun U => (p U).left) hcompat
  have hf : f ≫ (affineChartWeilRestriction A B Y).hom = T.hom := by
    apply 𝒰.hom_ext
    intro U
    dsimp only [f]
    rw [← Category.assoc, 𝒰.ι_glueMorphisms]
    exact Over.w (p U)
  exact Over.homMk f hf

/-- The global inverse restricts to each of the specified local inverse
morphisms, with the original source-neighborhood inclusions. -/
theorem affineChartWeilRestrictionInverse_restrict
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y)
    (U : Y.left.affineOpens) :
    affineChartWeilRestrictionSourceChartι A B Y T q U ≫
        affineChartWeilRestrictionInverse A B Y hY T q =
      affineChartWeilRestrictionLocalInverse A B Y T q U := by
  apply Over.OverMorphism.ext
  exact (affineChartWeilRestrictionSourceCover A B Y hY T q).ι_glueMorphisms
    _ (affineChartWeilRestrictionLocalInverse_compatible A B Y T q) U

/-- The canonical comparison applied to the glued inverse is the original
morphism on the whole base-changed test scheme. -/
theorem affineChartWeilRestrictionInverse_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) (q : ringBaseChange A B T ⟶ Y) :
    affineChartWeilRestrictionComparison A B Y T
        (affineChartWeilRestrictionInverse A B Y hY T q) = q := by
  let F := Over.pullback (Spec.algebraMap A B)
  let 𝒰 := affineChartWeilRestrictionSourceCover A B Y hY T q
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext (𝒰.pullbackCoverOfLeft T.hom (Spec.algebraMap A B))
  intro U
  change 𝒰.I₀ at U
  have h :
      F.map (affineChartWeilRestrictionSourceChartι A B Y T q U) ≫
          affineChartWeilRestrictionComparison A B Y T
            (affineChartWeilRestrictionInverse A B Y hY T q) =
        F.map (affineChartWeilRestrictionSourceChartι A B Y T q U) ≫ q := by
    erw [← affineChartWeilRestrictionComparison_natural,
      affineChartWeilRestrictionInverse_restrict,
      affineChartWeilRestrictionLocalInverse_comparison]
  exact congrArg (fun k => k.left) h

/-- The affine-chart gluing represents the actual base-changed Hom functor
on every test scheme under the explicit finite-set neighborhood condition. -/
def affineChartWeilRestrictionTestEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ affineChartWeilRestriction A B Y) ≃ (ringBaseChange A B T ⟶ Y) where
  toFun := affineChartWeilRestrictionComparison A B Y T
  invFun := affineChartWeilRestrictionInverse A B Y hY T
  left_inv p := by
    apply affineChartWeilRestrictionComparison_injective A B Y T
    exact affineChartWeilRestrictionInverse_comparison A B Y hY T _
  right_inv := affineChartWeilRestrictionInverse_comparison A B Y hY T

/-- The representing equivalence uses exactly the original counit comparison. -/
@[simp]
theorem affineChartWeilRestrictionTestEquiv_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionTestEquiv A B Y hY T p =
      affineChartWeilRestrictionComparison A B Y T p := rfl

/-- The all-test representing equivalence is natural in the test scheme. -/
theorem affineChartWeilRestrictionTestEquiv_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (p : S ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionTestEquiv A B Y hY T (f ≫ p) =
      (Over.pullback (Spec.algebraMap A B)).map f ≫
        affineChartWeilRestrictionTestEquiv A B Y hY S p :=
  affineChartWeilRestrictionComparison_natural A B Y f p

/-- The constructed inverse is also natural, despite its use of a source
cover chosen separately for each input morphism. -/
theorem affineChartWeilRestrictionInverse_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (q : ringBaseChange A B S ⟶ Y) :
    affineChartWeilRestrictionInverse A B Y hY T
        ((Over.pullback (Spec.algebraMap A B)).map f ≫ q) =
      f ≫ affineChartWeilRestrictionInverse A B Y hY S q := by
  apply affineChartWeilRestrictionComparison_injective A B Y T
  rw [affineChartWeilRestrictionComparison_natural,
    affineChartWeilRestrictionInverse_comparison,
    affineChartWeilRestrictionInverse_comparison]

end Langlands.AlgebraicGeometry.PointTopology
