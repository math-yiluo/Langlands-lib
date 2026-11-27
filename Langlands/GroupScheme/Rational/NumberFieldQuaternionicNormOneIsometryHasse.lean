import Langlands.GroupScheme.Rational.NumberFieldQuaternionicSpinHasseKernels
import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisHasse
import Langlands.GroupScheme.Quaternionic.QuaternionicSkewIsometryTransport
import Langlands.GroupScheme.Quaternionic.SymplecticAffineCoordinates
import Langlands.GroupScheme.Quaternionic.SymplecticPoints
import Langlands.GroupScheme.GaloisCocycleLocalTrivialization

/-! # The Hasse principle for quaternionic norm-one isometry groups

The affine points of the reduced-norm-one isometry group of a nondegenerate quaternionic
quadratic form `q` are, in matrix coordinates over `R ⊗ D`, exactly the special unitary
matrices of the skew-hermitian Gram matrix `conjugationSkewGram q` for the canonical
quaternion conjugation. A Galois cocycle of this group is therefore a special unitary crossed
homomorphism; triviality at the completions gives coboundary data there, and the Galois-level
Hasse principle gives a global primitive.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints SkewUnitary GaloisPoint

section Points

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] {n : ℕ} [NeZero n]

local notation "A" => Matrix (Fin n) (Fin n) D
local notation "Rₐ" R => CommAlgCat.of F R
local notation "unitEquiv[" R "]" =>
  FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)

variable (F D n) in
/-- The matrix over `R ⊗ D` of an affine point of the ambient unit group of `M_n(D)`. -/
def ambientMatrix (R : Type u) [CommRing R] [Algebra F R] :
    (CentralSimpleUnits.groupScheme F A).affinePoints (Rₐ R) →*
      (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ :=
  (Units.map (coefficientEquiv (m := Fin n) F D R).toRingEquiv.toMonoidHom).comp
    (unitEquiv[R]).toMonoidHom

omit [Algebra.IsCentral F D] [NeZero n] in
theorem ambientMatrix_val (R : Type u) [CommRing R] [Algebra F R]
    (x : (CentralSimpleUnits.groupScheme F A).affinePoints (Rₐ R)) :
    (ambientMatrix F D n R x : Matrix (Fin n) (Fin n) (R ⊗[F] D)) =
      coefficientEquiv F D R (unitEquiv[R] x : R ⊗[F] A) :=
  rfl

omit [Algebra.IsCentral F D] [NeZero n] in
theorem ambientMatrix_injective (R : Type u) [CommRing R] [Algebra F R] :
    Function.Injective (ambientMatrix F D n R) := by
  intro x y h
  apply (unitEquiv[R]).injective
  apply Units.ext
  apply (coefficientEquiv (m := Fin n) F D R).injective
  exact congrArg Units.val h

omit [Algebra.IsCentral F D] [NeZero n] in
theorem ambientMatrix_naturality {R S : Type u} [CommRing R] [CommRing S] [Algebra F R]
    [Algebra F S] (f : R →ₐ[F] S)
    (x : (CentralSimpleUnits.groupScheme F A).affinePoints (Rₐ R)) :
    ambientMatrix F D n S
        ((CentralSimpleUnits.groupScheme F A).affinePointMap (CommAlgCat.ofHom f) x) =
      unitMap f (ambientMatrix F D n R x) := by
  apply Units.ext
  rw [ambientMatrix_val, val_unitMap, ambientMatrix_val, GroupScheme.affinePointMap_apply,
    FiniteAlgebraUnits.affinePointsEquiv_naturality]
  change coefficientEquiv F D S (Algebra.TensorProduct.map f (AlgHom.id F A)
    (unitEquiv[R] x : R ⊗[F] A)) = _
  rw [coefficientEquiv_naturality, coeffMap_apply]

/-- The matrix point of the ambient unit is a unit of reduced norm one exactly when the
point lies in the kernel of the reduced-norm character. -/
theorem ambient_reducedNorm_eq_one_iff (R : Type u) [CommRing R] [Algebra F R]
    (x : (CentralSimpleUnits.groupScheme F A).affinePoints (Rₐ R)) :
    x ≫ (CentralSimpleUnits.reducedNormHom F A).hom.hom = 1 ↔
      matrixReducedNorm R (ambientMatrix F D n R x : Matrix (Fin n) (Fin n) (R ⊗[F] D)) = 1 := by
  rw [← (Gm.affinePointsEquiv ((algSpec (CommRingCat.of F)).obj (op (Rₐ R))).hom).injective.eq_iff,
    _root_.map_one, CentralSimpleUnits.reducedNormHom_affine_points, Units.ext_iff]
  change Langlands.CentralSimple.reducedNorm F A R (unitEquiv[R] x : R ⊗[F] A) = 1 ↔ _
  rw [ambientMatrix_val]
  change _ ↔ Langlands.CentralSimple.reducedNorm F A R ((coefficientEquiv F D R).symm
    (coefficientEquiv F D R (unitEquiv[R] x : R ⊗[F] A))) = 1
  rw [AlgEquiv.symm_apply_apply]

end Points

section NormOne

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)
  {n : ℕ} [NeZero n] (q : σ.QuadraticForms (Fin n))

local notation "A" => Matrix (Fin n) (Fin n) D
local notation "Rₐ" R => CommAlgCat.of F R
local notation "Tₐ" R => Functor.obj (algSpec (CommRingCat.of F)) (op R)
local notation "τ" => σ.quaternionConjugation hdim hsym
local notation "H" => σ.conjugationSkewGram q hdim hsym

/-- An ambient affine point lies in the norm-one isometry group exactly when its matrix is
special unitary for the skew-hermitian Gram matrix of `q`. -/
theorem mem_range_normOneIsometryAmbientι_affine_iff (R : Type u) [CommRing R] [Algebra F R]
    (x : (CentralSimpleUnits.groupScheme F A).affinePoints (Rₐ R)) :
    x ∈ (SubgroupFunctor.range (σ.normOneIsometryAmbientι q)).carrier (Tₐ (Rₐ R)) ↔
      ambientMatrix F D n R x ∈ suGroup τ H R := by
  rw [σ.mem_range_normOneIsometryAmbientι_iff q x]
  have hiso : x ∈ (SubgroupFunctor.range (σ.isometryGroupι q)).carrier (Tₐ (Rₐ R)) ↔
      x ∈ (SubgroupFunctor.range ((τ).unitaryGroupι H)).carrier (Tₐ (Rₐ R)) := by
    let e := σ.conjugationSkewIsometryIso q hdim hsym
    have he : e.hom ≫ (τ).unitaryGroupι H = σ.isometryGroupι q :=
      IsClosedSubgroup.sourceIsoOfRangeEq_hom_comp _ _ _
    rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y ≫ e.hom.hom.hom, by rw [← he, Grp.comp_hom_hom, Category.assoc]⟩
    · rintro ⟨y, rfl⟩
      refine ⟨y ≫ e.inv.hom.hom, ?_⟩
      rw [← he, Category.assoc, ← Grp.comp_hom_hom, ← Category.assoc e.inv, e.inv_hom_id,
        Category.id_comp]
  rw [hiso, (τ).mem_range_unitaryGroupι_affine_iff H (Rₐ R) x, IsometryCut.defect, sub_eq_zero,
    (τ).isometry_iff_coefficientEquiv R H, ambient_reducedNorm_eq_one_iff, mem_suGroup]
  rfl

/-- The matrix over `R ⊗ D` of an affine point of the norm-one isometry group. -/
def normOnePointMatrix (R : Type u) [CommRing R] [Algebra F R] :
    (σ.normOneIsometryGroup q).affinePoints (Rₐ R) →* (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ :=
  (ambientMatrix F D n R).comp
    ((σ.normOneIsometryGroup q).affinePointsTarget (σ.normOneIsometryAmbientι q) (Rₐ R))

omit [CharZero F] in
theorem normOnePointMatrix_injective (R : Type u) [CommRing R] [Algebra F R] :
    Function.Injective (σ.normOnePointMatrix q R) := by
  intro x y h
  have h' := ambientMatrix_injective R h
  simp only [GroupScheme.affinePointsTarget_apply] at h'
  exact (cancel_mono (σ.normOneIsometryAmbientι q).hom.hom).mp h'

omit [CharZero F] in
theorem normOnePointMatrix_naturality {R S : Type u} [CommRing R] [CommRing S] [Algebra F R]
    [Algebra F S] (f : R →ₐ[F] S) (x : (σ.normOneIsometryGroup q).affinePoints (Rₐ R)) :
    σ.normOnePointMatrix q S ((σ.normOneIsometryGroup q).affinePointMap (CommAlgCat.ofHom f) x) =
      unitMap f (σ.normOnePointMatrix q R x) := by
  change ambientMatrix F D n S (((algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom f).op ≫ x) ≫
    (σ.normOneIsometryAmbientι q).hom.hom) = _
  rw [Category.assoc]
  exact ambientMatrix_naturality f (x ≫ (σ.normOneIsometryAmbientι q).hom.hom)

theorem normOnePointMatrix_mem (R : Type u) [CommRing R] [Algebra F R]
    (x : (σ.normOneIsometryGroup q).affinePoints (Rₐ R)) :
    σ.normOnePointMatrix q R x ∈ suGroup τ H R :=
  (σ.mem_range_normOneIsometryAmbientι_affine_iff hdim hsym q R _).mp
    (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)

theorem exists_normOnePointMatrix_eq (R : Type u) [CommRing R] [Algebra F R]
    (y : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) (hy : y ∈ suGroup τ H R) :
    ∃ x, σ.normOnePointMatrix q R x = y := by
  let z := (FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)).symm
    (Units.map (coefficientEquiv (m := Fin n) F D R).symm.toRingEquiv.toMonoidHom y)
  have hz : ambientMatrix F D n R z = y := by
    apply Units.ext
    rw [ambientMatrix_val]
    change coefficientEquiv F D R ((FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A)
      (Rₐ R) ((FiniteAlgebraUnits.affinePointsEquiv (Module.finBasis F A) (Rₐ R)).symm
        (Units.map (coefficientEquiv (m := Fin n) F D R).symm.toRingEquiv.toMonoidHom y)) :
          R ⊗[F] A)) = _
    rw [MulEquiv.apply_symm_apply]
    exact (coefficientEquiv (m := Fin n) F D R).apply_symm_apply _
  have hmem := (σ.mem_range_normOneIsometryAmbientι_affine_iff hdim hsym q R z).mpr (hz ▸ hy)
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp hmem
  refine ⟨x, ?_⟩
  change ambientMatrix F D n R (x ≫ (σ.normOneIsometryAmbientι q).hom.hom) = y
  rw [hx, hz]

end NormOne

section Hasse

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)
  {n : ℕ} [NeZero n] (q : σ.QuadraticForms (Fin n))

include hdim hsym in
/-- A locally trivial Galois cocycle of the norm-one isometry group of a nondegenerate
quaternionic quadratic form over a number field is trivial. -/
theorem normOneIsometry_isTrivial_of_locallyTrivial (hq : σ.IsNondegenerateQuadratic q)
    (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle (σ.normOneIsometryGroup q) (GaloisCocycle.cover F L))
    (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  set τ := σ.quaternionConjugation hdim hsym
  set H := σ.conjugationSkewGram q hdim hsym
  let c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ :=
    fun s => σ.normOnePointMatrix q L (GaloisCocycle.value ξ s)
  have hconj : ∀ (s : L ≃ₐ[F] L) (x : (σ.normOneIsometryGroup q).affinePoints
      (CommAlgCat.of F L)), σ.normOnePointMatrix q L (conjugate F L _ s x) =
        unitMap s.toAlgHom (σ.normOnePointMatrix q L x) :=
    fun s x => σ.normOnePointMatrix_naturality q s.toAlgHom x
  have hc : IsCrossed c := by
    intro s t
    change σ.normOnePointMatrix q L (GaloisCocycle.value ξ (s * t)) = _
    rw [GaloisCocycle.value_mul, _root_.map_mul, hconj]
  have hsu : ∀ s, c s ∈ suGroup τ H L := fun s =>
    σ.normOnePointMatrix_mem hdim hsym q L _
  have key : ∀ (K : Type u) [Field K] [Algebra F K],
      (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial → IsCoboundaryAt τ H c K := by
    intro K _ _ h M _ _ _ _ _ _ _ _
    obtain ⟨a, ha⟩ := GaloisCocycle.exists_galois_coboundary_of_baseChange_isTrivial
      (K := K) (M := M) ξ h
    refine ⟨σ.normOnePointMatrix q M a, σ.normOnePointMatrix_mem hdim hsym q M a, fun s => ?_⟩
    have h1 := congrArg (σ.normOnePointMatrix q M) (ha s)
    rw [_root_.map_mul, _root_.map_inv] at h1
    have h2 := σ.normOnePointMatrix_naturality q (IsScalarTower.toAlgHom F L M)
      (GaloisCocycle.value ξ ((s.restrictScalars F).restrictNormal L))
    have h3 := σ.normOnePointMatrix_naturality q (s.restrictScalars F).toAlgHom a
    change σ.normOnePointMatrix q M (relativeExtend F L M _ _) = _ at h2
    change σ.normOnePointMatrix q M (conjugate F M _ (s.restrictScalars F) a) = _ at h3
    rw [h2, h3] at h1
    exact h1
  have hloc : IsLocallyCoboundary τ H c :=
    ⟨fun w => key _ (hξ (.inl w)), fun v => key _ (hξ (.inr v))⟩
  obtain ⟨a, ha, hcob⟩ := suHasse σ hdim hsym n H
    (σ.isAntihermitian_conjugationSkewGram q hdim hsym)
    (σ.isUnit_conjugationSkewGram q hdim hsym hq) L c hc hsu hloc
  obtain ⟨x, hx⟩ := σ.exists_normOnePointMatrix_eq hdim hsym q L a ha
  refine (GaloisCocycle.isTrivial_iff ξ).2 ⟨x, fun s => σ.normOnePointMatrix_injective q L ?_⟩
  rw [_root_.map_mul, _root_.map_inv, hconj, hx]
  exact hcob s

end Hasse

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

namespace Langlands.GroupScheme

/-- The Hasse principle for norm-one isometry groups of nondegenerate quaternionic quadratic
forms over number fields. -/
theorem numberFieldQuaternionicNormOneIsometryHasse :
    NumberFieldQuaternionicNormOneIsometryHasseStatement.{u} := by
  intro F _ _ D _ _ _ _ hdim σ hsym n _ q hq L _ _ _ _ ξ hξ
  exact σ.normOneIsometry_isTrivial_of_locallyTrivial hdim hsym q hq L ξ hξ

end Langlands.GroupScheme
