import Langlands.CommutativeAlgebra.FiniteSeparableNilradicalModel
import Mathlib.AlgebraicGeometry.ResidueField

/-! # The specified field at the generic prime of a nonreduced model -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped nonZeroDivisors TensorProduct

namespace Langlands.CommutativeAlgebra

/-- A surjective reduction into a domain identifies the residue field of its
kernel with the specified fraction field of that domain. -/
def residueFieldEquivOfSurjective
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [IsDomain D]
    (F : Type w) [Field F] [Algebra D F] [IsFractionRing D F]
    (f : A →+* D) (hf : Function.Surjective f)
    (p : Ideal A) [p.IsPrime] (hp : p = RingHom.ker f) : p.ResidueField ≃+* F := by
  let e := (Ideal.quotEquivOfEq hp).trans (f.quotientKerEquivOfSurjective hf)
  letI : Algebra (A ⧸ p) F := ((algebraMap D F).comp e.toRingHom).toAlgebra
  haveI : IsFractionRing (A ⧸ p) F :=
    IsFractionRing.of_ringEquiv_left e (fun _ => rfl)
  exact (IsLocalization.algEquiv (A ⧸ p)⁰ p.ResidueField F).toRingEquiv

@[simp]
theorem residueFieldEquivOfSurjective_algebraMap
    {A : Type u} {D : Type v} [CommRing A] [CommRing D] [IsDomain D]
    (F : Type w) [Field F] [Algebra D F] [IsFractionRing D F]
    (f : A →+* D) (hf : Function.Surjective f)
    (p : Ideal A) [p.IsPrime] (hp : p = RingHom.ker f) (a : A) :
    residueFieldEquivOfSurjective F f hf p hp (algebraMap A p.ResidueField a) =
      algebraMap D F (f a) := by
  let e := (Ideal.quotEquivOfEq hp).trans (f.quotientKerEquivOfSurjective hf)
  let : Algebra (A ⧸ p) F := ((algebraMap D F).comp e.toRingHom).toAlgebra
  have : IsFractionRing (A ⧸ p) F :=
    IsFractionRing.of_ringEquiv_left e (fun _ => rfl)
  unfold residueFieldEquivOfSurjective
  dsimp only
  change (IsLocalization.algEquiv (A ⧸ p)⁰ p.ResidueField F)
    (algebraMap (A ⧸ p) p.ResidueField (Ideal.Quotient.mk p a)) = _
  rw [AlgEquiv.commutes]
  rfl

/-- The actual spectrum of a specified fraction field identifies with the
scheme residue-field spectrum of the kernel of a surjective reduction. -/
def residueFieldSpecIsoOfSurjective
    {A D : Type u} [CommRing A] [CommRing D] [IsDomain D]
    (F : Type u) [Field F] [Algebra D F] [IsFractionRing D F]
    (f : A →+* D) (hf : Function.Surjective f)
    (p : PrimeSpectrum A) (hp : p.asIdeal = RingHom.ker f) :
    Spec (CommRingCat.of F) ≅ Spec ((Spec (CommRingCat.of A)).residueField p) :=
  Scheme.Spec.mapIso ((Scheme.Spec.residueFieldIso (CommRingCat.of A) p ≪≫
    (residueFieldEquivOfSurjective F f hf p.asIdeal hp).toCommRingCatIso).op)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem residueFieldSpecIsoOfSurjective_hom_fromSpecResidueField
    {A D : Type u} [CommRing A] [CommRing D] [IsDomain D]
    (F : Type u) [Field F] [Algebra D F] [IsFractionRing D F]
    (f : A →+* D) (hf : Function.Surjective f)
    (p : PrimeSpectrum A) (hp : p.asIdeal = RingHom.ker f) :
    (residueFieldSpecIsoOfSurjective F f hf p hp).hom ≫
      (Spec (CommRingCat.of A)).fromSpecResidueField p =
      Spec.map (CommRingCat.ofHom ((algebraMap D F).comp f)) := by
  change Spec.map ((Scheme.Spec.residueFieldIso (CommRingCat.of A) p).hom ≫
      (residueFieldEquivOfSurjective F f hf p.asIdeal hp).toCommRingCatIso.hom) ≫ _ = _
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [← Spec.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact residueFieldEquivOfSurjective_algebraMap F f hf p.asIdeal hp a

variable {R : Type u} {K : Type v} {L : Type w}
  [CommRing R] [IrreducibleSpace (PrimeSpectrum R)] [Field K] [Field L]

local instance genericNilradicalIsPrime : (nilradical R).IsPrime :=
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance

variable [Algebra (R ⧸ nilradical R) K] [IsFractionRing (R ⧸ nilradical R) K]
  [Algebra (R ⧸ nilradical R) L] [Algebra K L]
  [IsScalarTower (R ⧸ nilradical R) K L]

namespace FiniteSeparableNilradicalModel

/-- The specified extension is the fraction field of the actual domain
subalgebra that is the reduction of the lifted model. -/
instance reductionTargetFractionRing (d : FiniteSeparableNilradicalModel R K L)
    [Algebra.IsAlgebraic K L] : IsFractionRing d.quotientModel.Carrier L := by
  let M := Algebra.algebraMapSubmonoid d.quotientModel.Carrier (R ⧸ nilradical R)⁰
  have : IsLocalization M L := d.quotientModel.localized
  have hM : M ≤ d.quotientModel.Carrier⁰ :=
    map_le_nonZeroDivisors_of_injective _
      (algebraMap_injective_of_field_isFractionRing
        (R ⧸ nilradical R) d.quotientModel.Carrier K L) le_rfl
  exact IsLocalization.of_le M d.quotientModel.Carrier⁰ hM (by
    intro a ha
    apply isUnit_iff_ne_zero.mpr
    exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp ha) (Subtype.ext h))

/-- The residue field at the actual generic prime is the originally specified
extension field, including its reduction map. -/
def genericPrimeResidueFieldEquiv (d : FiniteSeparableNilradicalModel R K L)
    [Algebra.IsAlgebraic K L] : d.genericPrime.asIdeal.ResidueField ≃+* L :=
  residueFieldEquivOfSurjective L d.reductionMap
    (d.reductionMap_surjective Ideal.Quotient.mk_surjective) d.genericPrime.asIdeal rfl

omit [IrreducibleSpace (PrimeSpectrum R)] in
@[simp]
theorem genericPrimeResidueFieldEquiv_algebraMap
    (d : FiniteSeparableNilradicalModel R K L) [Algebra.IsAlgebraic K L]
    (a : d.Carrier) :
    d.genericPrimeResidueFieldEquiv (algebraMap d.Carrier d.genericPrime.asIdeal.ResidueField a) =
      (d.reductionMap a : L) := by
  exact residueFieldEquivOfSurjective_algebraMap L d.reductionMap
    (d.reductionMap_surjective Ideal.Quotient.mk_surjective) d.genericPrime.asIdeal rfl a

end FiniteSeparableNilradicalModel

section SchemeComparison

variable {R K L : Type u} [CommRing R]
  [IrreducibleSpace (PrimeSpectrum R)] [Field K] [Field L]
  [Algebra (R ⧸ nilradical R) K] [IsFractionRing (R ⧸ nilradical R) K]
  [Algebra (R ⧸ nilradical R) L] [Algebra K L]
  [IsScalarTower (R ⧸ nilradical R) K L]

namespace FiniteSeparableNilradicalModel

/-- The actual affine scheme of the potentially nonreduced monic model. -/
def modelScheme (d : FiniteSeparableNilradicalModel R K L) : Scheme :=
  Spec (CommRingCat.of d.Carrier)

/-- The original extension has the actual generic residue-field spectrum
of the lifted model. -/
def modelGenericResidueFieldIso (d : FiniteSeparableNilradicalModel R K L)
    [Algebra.IsAlgebraic K L] :
    Spec (CommRingCat.of L) ≅ Spec (d.modelScheme.residueField d.genericPrime) :=
  residueFieldSpecIsoOfSurjective L d.reductionMap
    (d.reductionMap_surjective Ideal.Quotient.mk_surjective) d.genericPrime rfl

omit [IrreducibleSpace (PrimeSpectrum R)] in
@[reassoc]
theorem modelGenericResidueFieldIso_hom_fromSpecResidueField
    (d : FiniteSeparableNilradicalModel R K L) [Algebra.IsAlgebraic K L] :
    d.modelGenericResidueFieldIso.hom ≫
      d.modelScheme.fromSpecResidueField d.genericPrime =
      Spec.map (CommRingCat.ofHom
        (d.quotientModel.Carrier.val.toRingHom.comp d.reductionMap)) :=
  residueFieldSpecIsoOfSurjective_hom_fromSpecResidueField L d.reductionMap
    (d.reductionMap_surjective Ideal.Quotient.mk_surjective) d.genericPrime rfl

/-- The map to the original possibly nonreduced affine base. -/
def toOriginalBase (d : FiniteSeparableNilradicalModel R K L) :
    d.modelScheme ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R d.Carrier))

/-- The generic map of the original base uses the specified fraction field
of its actual nilradical quotient. -/
def originalGenericBaseMap : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ nilradical R) K).comp
    (Ideal.Quotient.mk (nilradical R))))

omit [IrreducibleSpace (PrimeSpectrum R)] in
set_option backward.isDefEq.respectTransparency false in
/-- The spectrum comparison preserves the originally specified extension
and the actual coefficient map into the nonreduced base. -/
@[reassoc]
theorem modelGenericResidueFieldIso_hom_toOriginalBase
    (d : FiniteSeparableNilradicalModel R K L) [Algebra.IsAlgebraic K L] :
    d.modelGenericResidueFieldIso.hom ≫
      d.modelScheme.fromSpecResidueField d.genericPrime ≫ d.toOriginalBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        originalGenericBaseMap (R := R) (K := K) := by
  rw [← Category.assoc, d.modelGenericResidueFieldIso_hom_fromSpecResidueField]
  simp only [toOriginalBase, originalGenericBaseMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  change (d.reductionMap (AdjoinRoot.of d.polynomial r) : L) =
    algebraMap K L (algebraMap (R ⧸ nilradical R) K (Ideal.Quotient.mk _ r))
  rw [d.reductionMap_of]
  exact IsScalarTower.algebraMap_apply (R ⧸ nilradical R) K L _

end FiniteSeparableNilradicalModel

end SchemeComparison

end Langlands.CommutativeAlgebra
