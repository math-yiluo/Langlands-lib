import Langlands.GroupScheme.SpecialLinearWeilPointModels
import Langlands.GroupScheme.SpecialLinearDynamicRoots

/-! # Actual cocharacters contracting Weil-restricted special-linear roots -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.SpecialLinear.WeilRoot

variable {n : Type} [Fintype n] [DecidableEq n]
  (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

attribute [local instance] specialLinear_affine specialLinear_finiteType
  vectorGroup_affine vectorGroup_finiteType

/-- The actual test-scheme scalar enters the tensor coefficients through the right factor. -/
def includeSections (T : Over (Spec (CommRingCat.of F))) :
    Γ(T.left, ⊤) →+* tensorAlgebra F E T :=
  (Algebra.TensorProduct.includeRight :
    sectionAlgebra F T →ₐ[F] E ⊗[F] sectionAlgebra F T).toRingHom

omit [FiniteDimensional F E] in
/-- Test-scheme pullback commutes with the actual scalar inclusion in the tensor algebra. -/
theorem tensorMap_includeSections {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (r : Γ(T.left, ⊤)) :
    tensorMap F E a (includeSections F E T r) =
      includeSections F E T' (a.left.appTop r) := by
  rfl

omit [FiniteDimensional F E] in
/-- Composing changes of test scheme composes the actual tensor coefficient pullbacks. -/
theorem tensorMap_comp {T T' T'' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T) (b : T'' ⟶ T') (r : tensorAlgebra F E T) :
    tensorMap F E b (tensorMap F E a r) = tensorMap F E (b ≫ a) r := by
  simp only [tensorMap, Functor.map_comp, unop_comp]
  rfl

/-- The contracting diagonal homomorphism on every actual relative point group. -/
def cocharacterPoints {i j : n} (hij : i ≠ j)
    (T : Over (Spec (CommRingCat.of F))) :
    (T ⟶ (Gm (Spec (CommRingCat.of F))).X) →*
      (T ⟶ (groupScheme (n := n) F E).X) :=
  (tensorMatrixEquiv F E T).symm.toMonoidHom.comp
    ((Root.contractingMatrixHom hij).comp
      ((Units.map (includeSections F E T).toMonoidHom).comp
        (Gm.pointsEquiv (Spec (CommRingCat.of F)) T).toMonoidHom))

/-- The contracting homomorphism has the prescribed scalar diagonal on every test. -/
theorem tensorMatrixEquiv_cocharacterPoints {i j : n} (hij : i ≠ j)
    (T : Over (Spec (CommRingCat.of F))) (x : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    tensorMatrixEquiv F E T (cocharacterPoints F E hij T x) =
      Root.contractingMatrix hij
        (Units.map (includeSections F E T).toMonoidHom
          (Gm.pointsEquiv (Spec (CommRingCat.of F)) T x)) :=
  (tensorMatrixEquiv F E T).apply_symm_apply _

/-- The diagonal homomorphisms are natural in every relative test scheme. -/
theorem cocharacterPoints_naturality {i j : n} (hij : i ≠ j)
    {T T' : Over (Spec (CommRingCat.of F))} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    cocharacterPoints F E hij T' (a ≫ x) = a ≫ cocharacterPoints F E hij T x := by
  apply (tensorMatrixEquiv F E T').injective
  rw [tensorMatrixEquiv_naturality, tensorMatrixEquiv_cocharacterPoints,
    tensorMatrixEquiv_cocharacterPoints, Root.map_contractingMatrix]
  congr 1

/-- The actual F-cocharacter contracting the chosen restricted coordinate root. -/
def cocharacter {i j : n} (hij : i ≠ j) :
    (Gm (Spec (CommRingCat.of F))).toGrp ⟶ groupScheme (n := n) F E :=
  homOfPoints (cocharacterPoints F E hij) (cocharacterPoints_naturality F E hij)

/-- The actual cocharacter has its prescribed scalar diagonal on every test scheme. -/
theorem tensorMatrixEquiv_cocharacter {i j : n} (hij : i ≠ j)
    {T : Over (Spec (CommRingCat.of F))}
    (x : T ⟶ (Gm (Spec (CommRingCat.of F))).X) :
    tensorMatrixEquiv F E T (x ≫ (cocharacter F E hij).hom.hom) =
      Root.contractingMatrix hij
        (Units.map (includeSections F E T).toMonoidHom
          (Gm.pointsEquiv (Spec (CommRingCat.of F)) T x)) := by
  rw [cocharacter, comp_homOfPoints]
  exact tensorMatrixEquiv_cocharacterPoints F E hij T x

/-- The polynomial restricted-root curve with tensor coefficient `s² x` on `T × A¹`. -/
def contraction {i j : n} (hij : i ≠ j)
    {T : Over (Spec (CommRingCat.of F))} (x : T ⟶ (additiveScheme F E).X) :
    T ⊗ AffineLine.scheme (Spec (CommRingCat.of F)) ⟶ (groupScheme (n := n) F E).X :=
  (tensorMatrixEquiv F E _).symm
    (Matrix.SpecialLinearGroup.transvection hij
      ((includeSections F E _
          ((snd T (AffineLine.scheme (Spec (CommRingCat.of F)))).left.appTop
            (AffineLine.coord (Spec (CommRingCat.of F))))) ^ 2 *
        tensorMap F E (fst T (AffineLine.scheme (Spec (CommRingCat.of F))))
          ((tensorRootCoordinates F E T x).toAdd 0)))

/-- Pulling back the actual curve pulls back exactly its tensor polynomial coefficient. -/
theorem tensorMatrixEquiv_comp_contraction {i j : n} (hij : i ≠ j)
    {T T' : Over (Spec (CommRingCat.of F))}
    (a : T' ⟶ T ⊗ AffineLine.scheme (Spec (CommRingCat.of F)))
    (x : T ⟶ (additiveScheme F E).X) :
    tensorMatrixEquiv F E T' (a ≫ contraction F E hij x) =
      Matrix.SpecialLinearGroup.transvection hij
        ((includeSections F E T'
            ((a ≫ snd T (AffineLine.scheme (Spec (CommRingCat.of F)))).left.appTop
              (AffineLine.coord (Spec (CommRingCat.of F))))) ^ 2 *
          tensorMap F E (a ≫ fst T (AffineLine.scheme (Spec (CommRingCat.of F))))
            ((tensorRootCoordinates F E T x).toAdd 0)) := by
  rw [tensorMatrixEquiv_naturality]
  simp only [contraction, MulEquiv.apply_symm_apply, Root.map_transvection,
    map_mul, map_pow, tensorMap_includeSections, tensorMap_comp,
    Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- The actual tensor polynomial curve extends the cocharacter conjugation orbit. -/
theorem contraction_isOrbitExtension {i j : n} (hij : i ≠ j)
    {T : Over (Spec (CommRingCat.of F))} (x : T ⟶ (additiveScheme F E).X) :
    Dynamic.IsOrbitExtension (cocharacter F E hij)
      (x ≫ (rootMap F E hij).hom.hom) (contraction F E hij x) := by
  apply (tensorMatrixEquiv F E _).injective
  rw [tensorMatrixEquiv_comp_contraction]
  simp only [Dynamic.orbit, map_mul, map_inv, tensorMatrixEquiv_cocharacter]
  rw [tensorMatrixEquiv_naturality, tensorMatrixEquiv_rootMap,
    Root.map_transvection, Root.contractingMatrix_conjugate]
  congr 1
  rw [whiskerLeft_snd, whiskerLeft_fst]
  rw [← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_unitInclusion]
  rfl

/-- The actual restricted-root curve takes the identity value at zero. -/
theorem contraction_evalZero {i j : n} (hij : i ≠ j)
    {T : Over (Spec (CommRingCat.of F))} (x : T ⟶ (additiveScheme F E).X) :
    Dynamic.evalZero (contraction F E hij x) = 1 := by
  apply (tensorMatrixEquiv F E _).injective
  rw [Dynamic.evalZero, tensorMatrixEquiv_comp_contraction, map_one]
  rw [lift_snd, ← AffineLine.homEquiv_apply, AffineLine.homEquiv_comp_zeroSection,
    map_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

/-- Every actual restricted coordinate-root point contracts under the actual F-cocharacter. -/
theorem root_range_le_dynamicUnipotent {i j : n} (hij : i ≠ j) :
    SubgroupFunctor.range (rootMap F E hij) ≤ Dynamic.unipotent (cocharacter F E hij) := by
  intro T g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  exact ⟨contraction F E hij x, contraction_isOrbitExtension F E hij x,
    contraction_evalZero F E hij x⟩

end Langlands.GroupScheme.SpecialLinear.WeilRoot
