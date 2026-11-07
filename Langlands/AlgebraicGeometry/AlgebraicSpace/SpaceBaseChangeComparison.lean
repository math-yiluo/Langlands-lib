import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers

/-!
# Iterated base change of algebraic spaces

Base change along `g : T ⟶ S` followed by base change along `g' : T' ⟶ T` is base change
along any morphism `g₁ : T' ⟶ S` equal to `g' ≫ g`. On points the comparison is pullback along
the identity of the test scheme, so it is compatible with the point identifications
`baseChangeRingPointsEquiv`. An isomorphism of algebraic spaces over a topological field is a
homeomorphism on rational points for the étale-chart topology.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap ringTestRestrictScalarsIso
  ringTestRestrictScalarsIso_inv_left)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace BaseChangeComparison

/-- Sections are pulled back equally along two morphisms over the base with the same
underlying scheme morphism. -/
theorem pullback_congr_left {S : Scheme.{u}} (X : AlgebraicSpace S) {T U : Over S}
    {f g : T ⟶ U} (h : f.left = g.left) (x : X.sections U) :
    X.pullback f x = X.pullback g x := by
  rw [Over.OverMorphism.ext h]

variable {S T T' : Scheme.{u}} (g : T ⟶ S) (g' : T' ⟶ T) (g₁ : T' ⟶ S)

/-- A scheme over `T'` viewed over `S` along `g₁` and along `g' ≫ g`. -/
def overIso (h : g' ≫ g = g₁) (W : Over T') :
    (Over.map g₁).obj W ≅ (Over.map g).obj ((Over.map g').obj W) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (W.hom ≫ g') ≫ g = W.hom ≫ g₁
    rw [Category.id_comp, Category.assoc, h])

@[simp]
theorem overIso_hom_left (h : g' ≫ g = g₁) (W : Over T') :
    (overIso g g' g₁ h W).hom.left = 𝟙 _ := rfl

@[simp]
theorem overIso_inv_left (h : g' ≫ g = g₁) (W : Over T') :
    (overIso g g' g₁ h W).inv.left = 𝟙 _ := rfl

/-- The comparison of restricted presheaves. -/
def presheafIso (h : g' ≫ g = g₁) (P : Presheaf S) :
    (restrictPresheaf g').obj ((restrictPresheaf g).obj P) ≅ (restrictPresheaf g₁).obj P :=
  NatIso.ofComponents (fun W => P.mapIso (overIso g g' g₁ h W.unop).op) (by
    intro W W' f
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1)

/-- **Iterated base change.** -/
def compIso (h : g' ≫ g = g₁) (X : AlgebraicSpace S) :
    baseChange g' (baseChange g X) ≅ baseChange g₁ X where
  hom := homMk (presheafIso g g' g₁ h X.presheaf).hom
  inv := homMk (presheafIso g g' g₁ h X.presheaf).inv
  hom_inv_id := (homEquiv _ _).injective (presheafIso g g' g₁ h X.presheaf).hom_inv_id
  inv_hom_id := (homEquiv _ _).injective (presheafIso g g' g₁ h X.presheaf).inv_hom_id

/-- On sections the comparison is pullback along the identity of the test scheme. -/
theorem mapSections_compIso_hom (h : g' ≫ g = g₁) (X : AlgebraicSpace S) (W : Over T')
    (y : (baseChange g' (baseChange g X)).sections W) :
    mapSections (compIso g g' g₁ h X).hom W y = X.pullback (overIso g g' g₁ h W).hom y := rfl

end BaseChangeComparison

section Homeomorph

variable {K : Type u} [Field K] [TopologicalSpace K]

/-- A morphism that is an isomorphism of algebraic spaces is continuous on rational points
for the étale-chart topologies: it carries charts to charts. -/
theorem continuous_ringPointsMap_of_iso {X Y : AlgebraicSpace (Spec (CommRingCat.of K))}
    (e : X ≅ Y) :
    @Continuous _ _ (etaleChartTopology K X) (etaleChartTopology K Y)
      (RingPoints.map (A := K) e.hom) := by
  let : TopologicalSpace (RingPoints K Y K) := etaleChartTopology K Y
  rw [etaleChartTopology_continuous_iff]
  intro c
  let d : EtaleFiniteTypeChart K Y :=
    { scheme := c.scheme
      hom := c.hom ≫ e.hom
      isEtale := IsEtale.comp_iso c.isEtale ((forgetToPresheaf _).mapIso e)
      locallyOfFiniteType := c.locallyOfFiniteType
      quasiCompact := c.quasiCompact }
  exact d.continuous_pointMap

/-- An isomorphism of algebraic spaces over `Spec K` is a homeomorphism on rational points for
the étale-chart topologies. -/
theorem isHomeomorph_ringPointsMap_of_iso {X Y : AlgebraicSpace (Spec (CommRingCat.of K))}
    (e : X ≅ Y) :
    @IsHomeomorph _ _ (etaleChartTopology K X) (etaleChartTopology K Y)
      (RingPoints.map (A := K) e.hom) := by
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints K Y K) := etaleChartTopology K Y
  let E : RingPoints K X K ≃ RingPoints K Y K :=
    { toFun := RingPoints.map e.hom
      invFun := RingPoints.map e.inv
      left_inv := fun x => by
        rw [← RingPoints.map_comp, e.hom_inv_id]
        rfl
      right_inv := fun y => by
        rw [← RingPoints.map_comp, e.inv_hom_id]
        rfl }
  exact (Homeomorph.mk E (continuous_ringPointsMap_of_iso e)
    (continuous_ringPointsMap_of_iso e.symm)).isHomeomorph

end Homeomorph

section Tower

open BaseChangeComparison

variable (C D A : Type u) [CommRing C] [CommRing D] [CommRing A] [Algebra C D] [Algebra D A]
  [Algebra C A] [IsScalarTower C D A]

theorem specAlgebraMap_comp :
    Spec.algebraMap D A ≫ Spec.algebraMap C D = Spec.algebraMap C A := by
  change Spec.map (CommRingCat.ofHom (algebraMap D A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C D)) = Spec.map (CommRingCat.ofHom (algebraMap C A))
  rw [← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq C D A).symm

/-- Base change along `C → D` followed by base change along `D → A` is base change along
`C → A`. -/
abbrev towerIso (X : AlgebraicSpace (Spec (CommRingCat.of C))) :
    baseChange (Spec.algebraMap D A) (baseChange (Spec.algebraMap C D) X) ≅
      baseChange (Spec.algebraMap C A) X :=
  compIso _ _ _ (specAlgebraMap_comp C D A) X

/-- The tower comparison is compatible with the point identifications. -/
theorem baseChangeRingPointsEquiv_towerIso (B : Type u) [CommRing B] [Algebra C B] [Algebra D B]
    [Algebra A B] [IsScalarTower C D B] [IsScalarTower D A B] [IsScalarTower C A B]
    (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    (y : RingPoints A (baseChange (Spec.algebraMap D A) (baseChange (Spec.algebraMap C D) X)) B) :
    baseChangeRingPointsEquiv C A B X (RingPoints.map (towerIso C D A X).hom y) =
      baseChangeRingPointsEquiv C D B X (baseChangeRingPointsEquiv D A B _ y) := by
  simp only [baseChangeRingPointsEquiv_apply]
  change X.pullback _ (X.pullback _ y) = X.pullback _ (X.pullback _ y)
  refine (pullback_comp X _ _ y).symm.trans (Eq.trans ?_ (pullback_comp X _ _ y))
  apply pullback_congr_left
  simp
  rfl

variable {C D} in
/-- The point identification of a base change is natural in the coefficient algebra. -/
theorem baseChangeRingPointsEquiv_changeRing (X : AlgebraicSpace (Spec (CommRingCat.of C)))
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra C B] [Algebra D B] [IsScalarTower C D B]
    [Algebra C B'] [Algebra D B'] [IsScalarTower C D B'] (ψ : B →ₐ[D] B')
    (y : RingPoints D (baseChange (Spec.algebraMap C D) X) B) :
    baseChangeRingPointsEquiv C D B' X (RingPoints.changeRing ψ y) =
      RingPoints.changeRing (ψ.restrictScalars C) (baseChangeRingPointsEquiv C D B X y) := by
  simp only [baseChangeRingPointsEquiv_apply, RingPoints.changeRing]
  change X.pullback _ (X.pullback _ y) = X.pullback _ (X.pullback _ y)
  refine (pullback_comp X _ _ y).symm.trans (Eq.trans ?_ (pullback_comp X _ _ y))
  apply pullback_congr_left
  simp
  rfl

end Tower

end Langlands.AlgebraicGeometry.AlgebraicSpace
