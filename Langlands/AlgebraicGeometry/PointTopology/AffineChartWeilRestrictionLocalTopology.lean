import Langlands.AlgebraicGeometry.PointTopology.QuasiProjectiveWeilRestriction
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs

/-! # The local topology of the actual affine-chart Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- Tensor multiplication identifies the actual tensor-unit test spectrum
with the original test spectrum over `B`. -/
def weilRestrictionTensorUnitTestIso :
    ringTest B B ≅ ringTest B (B ⊗[A] A) where
  hom := ringTestMap B (Algebra.TensorProduct.rid A B B).toAlgHom
  inv := ringTestMap B (Algebra.TensorProduct.rid A B B).symm.toAlgHom
  hom_inv_id := by
    rw [← ringTestMap_comp, AlgEquiv.comp_symm, ringTestMap_id]
  inv_hom_id := by
    rw [← ringTestMap_comp, AlgEquiv.symm_comp, ringTestMap_id]

/-- Base change of the base-point test scheme is canonically the base-point
test scheme over the extension ring. -/
def weilRestrictionBaseTestIso :
    ringTest B B ≅ ringBaseChange A B (ringTest A A) :=
  weilRestrictionTensorUnitTestIso A B ≪≫ (ringBaseChangeSpectrumIso A B A).symm

@[simp]
theorem weilRestrictionBaseTestIso_hom_spectrum :
    (weilRestrictionBaseTestIso A B).hom ≫
        (ringBaseChangeSpectrumIso A B A).hom =
      ringTestMap B (Algebra.TensorProduct.rid A B B).toAlgHom := by
  simp [weilRestrictionBaseTestIso, weilRestrictionTensorUnitTestIso]

variable [Module.Finite A B] [Module.Projective A B]
variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

/-- The original counit comparison at the base ring, transported through the
actual canonical tensor-unit test isomorphism. -/
def affineChartWeilRestrictionBasePointComparison
    (p : RingPoint A (affineChartWeilRestriction A B Y) A) : RingPoint B Y B :=
  (weilRestrictionBaseTestIso A B).hom ≫
    affineChartWeilRestrictionComparison A B Y (ringTest A A) p

variable [IsSeparated Y.hom]

/-- The all-test representation gives the actual base-point equivalence. -/
def affineChartWeilRestrictionBasePointEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    RingPoint A (affineChartWeilRestriction A B Y) A ≃ RingPoint B Y B :=
  (affineChartWeilRestrictionTestEquiv A B Y hY (ringTest A A)).trans
    (weilRestrictionBaseTestIso A B).symm.homFromEquiv

@[simp]
theorem affineChartWeilRestrictionBasePointEquiv_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) A) :
    affineChartWeilRestrictionBasePointEquiv A B Y hY p =
      affineChartWeilRestrictionBasePointComparison A B Y p := rfl

omit [IsSeparated Y.hom] in
/-- A point over a local base ring factors through one of the actual open
Weil charts, by choosing a chart containing its closed-point image. -/
theorem exists_affineChartWeilRestrictionPoint [IsLocalRing A]
    (p : RingPoint A (affineChartWeilRestriction A B Y) A) :
    ∃ U : Y.left.affineOpens,
      ∃ q : RingPoint A (affineWeilRestriction A B (openOver B Y U.val)) A,
        q ≫ affineChartWeilRestrictionι A B Y U = p := by
  obtain ⟨U, z, hz⟩ := affineChartWeilRestrictionι_jointly_surjective A B Y
    (p.left (IsLocalRing.closedPoint A))
  let i := affineChartWeilRestrictionι A B Y U
  have hr : Set.range p.left ⊆ Set.range i.left := by
    change Set.range p.left ⊆ i.left.opensRange
    apply (range_subset_open_iff_closedPoint A
      (affineChartWeilRestriction A B Y) A i.left.opensRange p).mpr
    exact ⟨z, hz⟩
  let q := IsOpenImmersion.lift i.left p.left hr
  have hq : q ≫ i.left = p.left := IsOpenImmersion.lift_fac i.left p.left hr
  have hb : q ≫ (affineWeilRestriction A B (openOver B Y U.val)).hom =
      Spec.algebraMap A A := by
    rw [← Over.w i, ← Category.assoc, hq]
    exact Over.w p
  refine ⟨U, Over.homMk q hb, ?_⟩
  apply Over.OverMorphism.ext
  exact hq

variable [TopologicalSpace A] [IsTopologicalRing A]
  [TopologicalSpace B] [IsTopologicalRing B] [IsModuleTopology A B]

/-- On an affine target, tensor-unit transport of the actual comparison
is precisely the already constructed affine point homeomorphism. -/
theorem affineWeilRestrictionComparison_basePoint
    (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom]
    (p : RingPoint A (affineWeilRestriction A B X) A) :
    (weilRestrictionBaseTestIso A B).hom ≫
        affineWeilRestrictionComparison A B X (ringTest A A) p =
      affineWeilRestrictionPointHomeomorph A B X p := by
  rw [affineWeilRestrictionComparison_affine, ← Category.assoc,
    weilRestrictionBaseTestIso_hom_spectrum]
  apply (affineSchemePointEquiv B X B).injective
  change affineSchemePointEquiv B X B
      ((affineWeilRestrictionPointEquiv A B X A p).changeRing
        (Algebra.TensorProduct.rid A B B).toAlgHom) = _
  rw [affineSchemePointEquiv_changeRing,
    affineWeilRestrictionPointEquiv_coordinates,
    affineWeilRestrictionPointHomeomorph_apply]
  rfl

omit [IsSeparated Y.hom] in
/-- The canonical point comparison on every actual Weil chart is the affine
homeomorphism followed by the original target open inclusion. -/
theorem affineChartWeilRestrictionBasePointComparison_chart
    (U : Y.left.affineOpens)
    (p : RingPoint A (affineWeilRestriction A B (openOver B Y U.val)) A) :
    affineChartWeilRestrictionBasePointComparison A B Y
        (p ≫ affineChartWeilRestrictionι A B Y U) =
      openPointMap B Y B U.val
        (affineWeilRestrictionPointHomeomorph A B (openOver B Y U.val) p) := by
  rw [affineChartWeilRestrictionBasePointComparison,
    affineChartWeilRestrictionComparison_chart, ← Category.assoc,
    affineWeilRestrictionComparison_basePoint]
  rfl

variable [IsLocalRing A] [IsOpenUnits A] [IsLocalRing B] [IsOpenUnits B]

omit [IsSeparated Y.hom] in
/-- The original counit comparison is continuous for the independently
constructed scheme-point topologies on the two local rings. -/
theorem continuous_affineChartWeilRestrictionBasePointComparison :
    Continuous[schemePointTopology A (affineChartWeilRestriction A B Y) A,
      schemePointTopology B Y B]
      (affineChartWeilRestrictionBasePointComparison A B Y) := by
  let : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) A) :=
    schemePointTopology A (affineChartWeilRestriction A B Y) A
  let : TopologicalSpace (RingPoint B Y B) := schemePointTopology B Y B
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U, q, rfl⟩ := exists_affineChartWeilRestrictionPoint A B Y p
  let : IsAffine (openOver B Y U.val).left := U.property
  have hj := isOpenEmbedding_schemePointMap A A
    (affineChartWeilRestrictionι A B Y U)
  change @IsOpenEmbedding _ _
    (schemePointTopology A (affineWeilRestriction A B (openOver B Y U.val)) A)
    (schemePointTopology A (affineChartWeilRestriction A B Y) A) _ at hj
  rw [schemePointTopology_eq_affine] at hj
  apply hj.continuousAt_iff.mp
  have heq :
      affineChartWeilRestrictionBasePointComparison A B Y ∘
          (fun p => p ≫ affineChartWeilRestrictionι A B Y U) =
        openPointMap B Y B U.val ∘
          (affineWeilRestrictionPointHomeomorph A B (openOver B Y U.val)) := by
    funext r
    exact affineChartWeilRestrictionBasePointComparison_chart A B Y U r
  dsimp only [RingPoint] at q heq ⊢
  rw [heq]
  exact ((isOpenEmbedding_schemeAffineChart B B Y U).continuous.comp
    (affineWeilRestrictionPointHomeomorph A B (openOver B Y U.val)).continuous).continuousAt

omit [IsLocalRing A] [IsOpenUnits A] [IsLocalRing B] [IsOpenUnits B] in
/-- On an affine target chart, the inverse of the actual representing
equivalence is the inverse affine homeomorphism followed by the Weil chart. -/
theorem affineChartWeilRestrictionBasePointEquiv_symm_chart
    (hY : HasFiniteAffineNeighborhoods Y.left) (U : Y.left.affineOpens)
    (q : RingPoint B (openOver B Y U.val) B) :
    (affineChartWeilRestrictionBasePointEquiv A B Y hY).symm
        (openPointMap B Y B U.val q) =
      (affineWeilRestrictionPointHomeomorph A B (openOver B Y U.val)).symm q ≫
        affineChartWeilRestrictionι A B Y U := by
  apply (affineChartWeilRestrictionBasePointEquiv A B Y hY).injective
  rw [Equiv.apply_symm_apply, affineChartWeilRestrictionBasePointEquiv_apply,
    affineChartWeilRestrictionBasePointComparison_chart,
    Homeomorph.apply_symm_apply]

/-- The inverse equivalence is continuous for the independently constructed
scheme-point topologies, using the target's genuine affine open charts. -/
theorem continuous_affineChartWeilRestrictionBasePointEquiv_symm
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    Continuous[schemePointTopology B Y B,
      schemePointTopology A (affineChartWeilRestriction A B Y) A]
      (affineChartWeilRestrictionBasePointEquiv A B Y hY).symm := by
  let : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) A) :=
    schemePointTopology A (affineChartWeilRestriction A B Y) A
  let : TopologicalSpace (RingPoint B Y B) := schemePointTopology B Y B
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U, q, rfl⟩ := exists_affineOpenPoint B Y B p
  let : IsAffine (openOver B Y U.val).left := U.property
  apply (isOpenEmbedding_schemeAffineChart B B Y U).continuousAt_iff.mp
  have heq :
      (affineChartWeilRestrictionBasePointEquiv A B Y hY).symm ∘
          openPointMap B Y B U.val =
        (fun p => p ≫ affineChartWeilRestrictionι A B Y U) ∘
          (affineWeilRestrictionPointHomeomorph A B (openOver B Y U.val)).symm := by
    funext r
    exact affineChartWeilRestrictionBasePointEquiv_symm_chart A B Y hY U r
  dsimp only [RingPoint] at q heq ⊢
  rw [heq]
  have hj := isOpenEmbedding_schemePointMap A A
    (affineChartWeilRestrictionι A B Y U)
  change @IsOpenEmbedding _ _
    (schemePointTopology A (affineWeilRestriction A B (openOver B Y U.val)) A)
    (schemePointTopology A (affineChartWeilRestriction A B Y) A) _ at hj
  rw [schemePointTopology_eq_affine] at hj
  exact (hj.continuous.comp
    (affineWeilRestrictionPointHomeomorph A B (openOver B Y U.val)).symm.continuous).continuousAt

/-- The actual Weil-restriction comparison is a homeomorphism on points over
local topological rings, for their independently defined point topologies. -/
def affineChartWeilRestrictionPointHomeomorph
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) A) :=
      schemePointTopology A (affineChartWeilRestriction A B Y) A
    letI : TopologicalSpace (RingPoint B Y B) := schemePointTopology B Y B
    RingPoint A (affineChartWeilRestriction A B Y) A ≃ₜ RingPoint B Y B := by
  let : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) A) :=
    schemePointTopology A (affineChartWeilRestriction A B Y) A
  let : TopologicalSpace (RingPoint B Y B) := schemePointTopology B Y B
  exact
    { toEquiv := affineChartWeilRestrictionBasePointEquiv A B Y hY
      continuous_toFun := continuous_affineChartWeilRestrictionBasePointComparison A B Y
      continuous_invFun := continuous_affineChartWeilRestrictionBasePointEquiv_symm A B Y hY }

@[simp]
theorem affineChartWeilRestrictionPointHomeomorph_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) A) :
    affineChartWeilRestrictionPointHomeomorph A B Y hY p =
      affineChartWeilRestrictionBasePointComparison A B Y p := rfl

omit [IsSeparated Y.hom] in
/-- An actual projective immersion supplies both geometric hypotheses of the
local-ring point homeomorphism. -/
def projectiveImmersionWeilRestrictionPointHomeomorph
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) A) :=
      schemePointTopology A (affineChartWeilRestriction A B Y) A
    letI : TopologicalSpace (RingPoint B Y B) := schemePointTopology B Y B
    RingPoint A (affineChartWeilRestriction A B Y) A ≃ₜ RingPoint B Y B := by
  letI := isSeparated_of_projectiveImmersion B Y n i hi
  exact affineChartWeilRestrictionPointHomeomorph A B Y
    (hasFiniteAffineNeighborhoods_of_projectiveImmersion B n i)

omit [IsSeparated Y.hom] in
/-- The projective-immersion homeomorphism has the original counit map as
its forward function. -/
@[simp]
theorem projectiveImmersionWeilRestrictionPointHomeomorph_apply
    (n : ℕ) (i : Y.left ⟶ ProjectiveSpace B n) [IsImmersion i]
    (hi : i ≫ projectiveSpaceToSpec B n = Y.hom)
    (p : RingPoint A (affineChartWeilRestriction A B Y) A) :
    projectiveImmersionWeilRestrictionPointHomeomorph A B Y n i hi p =
      affineChartWeilRestrictionBasePointComparison A B Y p := rfl

end Langlands.AlgebraicGeometry.PointTopology
