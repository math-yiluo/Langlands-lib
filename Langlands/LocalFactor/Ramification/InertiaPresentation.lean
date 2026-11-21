import Langlands.LocalFactor.Ramification.Herbrand.Absolute
import Langlands.LocalFactor.Ramification.Descent
import Langlands.Weil.Local.AssemblyProof
import Langlands.Weil.Local.ExtensionWeil
import Langlands.Weil.Representation.Predicates

/-!
# Actual finite inertia restrictions and Weil representation presentations

The restriction maps use the actual field inclusions. A presentation supplies
its finite subextension and the kernel condition, with surjectivity an argument
to descent.
-/

noncomputable section

namespace Langlands.Ramification.Local

open IsLocalRing ValuativeRel
open Weil.Local.SepClosed

universe u₀ uK uΩ uV

section Restriction

variable (K : Type uK) (Ω : Type uΩ) [Field K] [Field Ω] [Algebra K Ω]
    {L M : FiniteGaloisIntermediateField K Ω}

/-- Restriction along an actual inclusion of finite Galois subfields. -/
def finiteGaloisRestriction (h : L ≤ M) : Gal(M/K) →ₜ* Gal(L/K) := by
  letI : Algebra L M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact { toMonoidHom := AlgEquiv.restrictNormalHom L
          continuous_toFun := continuous_of_discreteTopology }

/-- The finite restriction evaluates via the actual inclusion. -/
theorem finiteGaloisRestriction_apply (h : L ≤ M) (σ : Gal(M/K)) (x : L) :
    ((finiteGaloisRestriction K Ω h σ) x : Ω) =
      (σ (IntermediateField.inclusion h x) : Ω) := by
  let : Algebra L M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact congrArg (fun y : M => (y : Ω)) (σ.restrictNormal_commutes L x)

end Restriction

/-- The subextension and its presentation condition. Keeping the condition
as a parameter lets the constructor use just the algebraic field data. -/
structure FiniteInertiaPresentationData {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (condition : FiniteGaloisIntermediateField K Ω → Prop) where
  extension : FiniteGaloisIntermediateField K Ω
  kernel_le : condition extension

/-- The subextension and the inclusions of the two presented fields. -/
structure FiniteInertiaCommonRefinementData {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {condition : FiniteGaloisIntermediateField K Ω → Prop}
    (P Q : FiniteInertiaPresentationData condition) where
  extension : FiniteGaloisIntermediateField K Ω
  left_le : P.extension ≤ extension
  right_le : Q.extension ≤ extension

private theorem isLocalHom_integerRestriction {L E : Type*} [Field L] [Field E]
    (A : Subring L) (B : Subring E) (f : L →+* E)
    (hf : ∀ x, f x ∈ B ↔ x ∈ A) :
    IsLocalHom ((f.comp A.subtype).codRestrict B fun x => (hf x.val).mpr x.property) := by
  constructor
  intro x hx
  obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
  have hmul : f x.val * y.val = 1 := congrArg Subtype.val hy
  have hinv : f x.val⁻¹ = y.val := by
    rw [map_inv₀]
    exact inv_eq_of_mul_eq_one_right hmul
  have hm : x.val⁻¹ ∈ A := (hf _).mp (hinv.symm ▸ y.property)
  refine isUnit_iff_exists_inv.mpr ⟨⟨x.val⁻¹, hm⟩, Subtype.ext ?_⟩
  apply f.injective
  simpa only [Subring.coe_mul, Subring.coe_one, map_mul, hinv, map_one] using hmul

section Spectral

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
    [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
    (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω]
    (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ a ≤ᵥ b)

private instance presentationFiniteDimensional (L : FiniteGaloisIntermediateField K Ω) :
    FiniteDimensional K₀ L :=
  FiniteDimensional.trans K₀ K L

/-- The actual inclusion of the base into a finite Galois subextension. -/
def finiteBaseEmbedding (L : FiniteGaloisIntermediateField K Ω) :
    K →ₐ[K₀] L := IsScalarTower.toAlgHom K₀ K L

/-- The finite realization on the same spectral base as the absolute filtration. -/
abbrev finiteTopologicalData (L : FiniteGaloisIntermediateField K Ω) :
    LocalField.TopologicalData K₀ L :=
  LocalField.canonicalTopologicalData K₀ L hbase

private theorem mem_finiteIntegers_iff (E : Type*) [Field E] [Algebra K₀ E]
    [FiniteDimensional K₀ E] (x : E) :
    x ∈ (LocalField.canonicalTopologicalData K₀ E hbase).Integers ↔ spectralNorm K₀ E x ≤ 1 := by
  let := (LocalField.canonicalTopologicalData K₀ E hbase).valuativeRel
  let : (LocalField.canonicalValuation K₀ E).Compatible := Valuation.Compatible.ofValuation _
  change valuation E x ≤ 1 ↔ _
  rw [← map_one (valuation E), ← Valuation.Compatible.vle_iff_le (v := valuation E)]
  rw [Valuation.Compatible.vle_iff_le (v := LocalField.canonicalValuation K₀ E), map_one]
  exact Iff.rfl

section FiniteTower

variable {L M : FiniteGaloisIntermediateField K Ω}

private theorem mem_finiteIntegers_inclusion_iff (h : L ≤ M) (x : L) :
    IntermediateField.inclusion h x ∈ (finiteTopologicalData K₀ K Ω hbase M).Integers ↔
      x ∈ (finiteTopologicalData K₀ K Ω hbase L).Integers := by
  let : Algebra L M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower K₀ L M := IsScalarTower.to₁₃₄ K₀ K L M
  rw [mem_finiteIntegers_iff K₀ hbase M, mem_finiteIntegers_iff K₀ hbase L]
  change spectralNorm K₀ M (algebraMap L M x) ≤ 1 ↔ spectralNorm K₀ L x ≤ 1
  rw [← spectralNorm.eq_of_tower]

/-- The actual inclusion of integer rings along a finite subfield inclusion. -/
def finiteIntegerMap (h : L ≤ M) : (finiteTopologicalData K₀ K Ω hbase L).Integers →+*
    (finiteTopologicalData K₀ K Ω hbase M).Integers :=
  ((IntermediateField.inclusion h).toRingHom.comp
    (finiteTopologicalData K₀ K Ω hbase L).Integers.subtype).codRestrict _
    (fun x => (mem_finiteIntegers_inclusion_iff K₀ K Ω hbase h x.val).mpr x.property)

instance finiteIntegerMap_isLocalHom (h : L ≤ M) :
    IsLocalHom (finiteIntegerMap K₀ K Ω hbase h) :=
  isLocalHom_integerRestriction _ _ (IntermediateField.inclusion h).toRingHom
    (mem_finiteIntegers_inclusion_iff K₀ K Ω hbase h)

/-- Actual inclusions preserve the residue kernels under finite restriction. -/
theorem finiteGaloisRestriction_mem_inertia (h : L ≤ M)
    (σ : inertia (finiteTopologicalData K₀ K Ω hbase M) K) :
    finiteGaloisRestriction K Ω h σ ∈ inertia (finiteTopologicalData K₀ K Ω hbase L) K := by
  change residueHom (finiteTopologicalData K₀ K Ω hbase L) K
    (finiteGaloisRestriction K Ω h σ) = 1
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  apply (ResidueField.map (finiteIntegerMap K₀ K Ω hbase h)).injective
  have hs := DFunLike.congr_fun σ.property (residue _ (finiteIntegerMap K₀ K Ω hbase h x))
  change residue _ (integerAutomorphism (finiteTopologicalData K₀ K Ω hbase M) K σ.val
    (finiteIntegerMap K₀ K Ω hbase h x)) = residue _ (finiteIntegerMap K₀ K Ω hbase h x) at hs
  change residue _ (finiteIntegerMap K₀ K Ω hbase h
    (integerAutomorphism (finiteTopologicalData K₀ K Ω hbase L) K
      (finiteGaloisRestriction K Ω h σ) x)) = residue _ (finiteIntegerMap K₀ K Ω hbase h x)
  rw [← hs]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact finiteGaloisRestriction_apply K Ω h σ.val (x : L)

/-- Restriction between the two actual finite inertia groups. -/
def finiteInertiaRestriction (h : L ≤ M) :
    inertia (finiteTopologicalData K₀ K Ω hbase M) K →ₜ*
      inertia (finiteTopologicalData K₀ K Ω hbase L) K where
  toMonoidHom := ((finiteGaloisRestriction K Ω h).toMonoidHom.comp
    (inertia (finiteTopologicalData K₀ K Ω hbase M) K).subtype).codRestrict _
      (finiteGaloisRestriction_mem_inertia K₀ K Ω hbase h)
  continuous_toFun := ((finiteGaloisRestriction K Ω h).continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp] theorem finiteInertiaRestriction_coe (h : L ≤ M)
    (σ : inertia (finiteTopologicalData K₀ K Ω hbase M) K) :
    (finiteInertiaRestriction K₀ K Ω hbase h σ : Gal(L/K)) =
      finiteGaloisRestriction K Ω h σ := rfl

end FiniteTower

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra.IsAlgebraic K Ω]
    (hK : ∀ x : K, spectralNorm K₀ K x ≤ 1 ↔ valuation K x ≤ 1)

omit [ValuativeRel K₀] [LocallyCompactSpace K₀] in
include hK in
private theorem spectralNorm_le_one_iff (x : Ω) :
    spectralNorm K₀ Ω x ≤ 1 ↔ x ∈ LocalGalois.SepClosed.closureIntegers K Ω := by
  let := LocalGalois.localNormedField K
  let := LocalGalois.localNormedField_ultrametric K
  let := LocalGalois.localNormedField_complete K
  let : Algebra.IsAlgebraic K₀ Ω := Algebra.IsAlgebraic.trans K₀ K Ω
  let v₀ := NormedField.valuation (K := K₀)
  let v := NormedField.valuation (K := K)
  have hKv (y : K) : spectralNorm K₀ K y ≤ 1 ↔ v y ≤ 1 := by
    rw [hK y]
    change valuation K y ≤ 1 ↔ ‖y‖ ≤ 1
    simpa only [map_one, norm_one] using
      (LocalGalois.localNormedField_le K y 1).symm
  let : v₀.HasExtension v := ⟨by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro y
    change ‖y‖ ≤ 1 ↔ v (algebraMap K₀ K y) ≤ 1
    rw [← hKv, spectralNorm_extends]⟩
  let A₀ := LocalGalois.baseIntegers K₀
  let A := LocalGalois.baseIntegers K
  let : Algebra A₀ A := Valuation.HasExtension.instAlgebra_valuationSubring v₀ v
  let : IsScalarTower A₀ A K := Valuation.HasExtension.instIsScalarTower_valuationSubring' v₀ v
  let : IsScalarTower A₀ A Ω := IsScalarTower.of_algebraMap_eq fun y => by
    change algebraMap K₀ Ω y.val = algebraMap K Ω (algebraMap K₀ K y.val)
    exact IsScalarTower.algebraMap_apply K₀ K Ω y.val
  let : Algebra.IsIntegral A₀ A := ⟨fun y => by
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom A₀ A K) Subtype.val_injective).mp
    exact (LocalGalois.integral_iff_mem_spectralIntegers K₀ K (y : K)).mpr
      ((hKv y.val).mpr y.property)⟩
  change x ∈ LocalGalois.extensionIntegers K₀ Ω ↔ x ∈ LocalGalois.extensionIntegers K Ω
  rw [← LocalGalois.integral_iff_mem_spectralIntegers, ← LocalGalois.integral_iff_mem_spectralIntegers]
  exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans (A := A) x hx⟩

variable (L : FiniteGaloisIntermediateField K Ω)

include hK in
private theorem mem_closureIntegers_iff (x : L) :
    (x : Ω) ∈ LocalGalois.SepClosed.closureIntegers K Ω ↔
      x ∈ (finiteTopologicalData K₀ K Ω hbase L).Integers := by
  let : IsScalarTower K₀ L Ω := IsScalarTower.to₁₃₄ K₀ K L Ω
  rw [← spectralNorm_le_one_iff K₀ K Ω hK, mem_finiteIntegers_iff K₀ hbase L]
  change spectralNorm K₀ Ω (algebraMap L Ω x) ≤ 1 ↔ spectralNorm K₀ L x ≤ 1
  rw [← spectralNorm.eq_of_tower]

/-- The actual inclusion of finite integers into the integers of the closure. -/
def finiteClosureIntegerMap : (finiteTopologicalData K₀ K Ω hbase L).Integers →+*
    LocalGalois.SepClosed.closureIntegers K Ω :=
  (L.val.toRingHom.comp (finiteTopologicalData K₀ K Ω hbase L).Integers.subtype).codRestrict
    (LocalGalois.SepClosed.closureIntegers K Ω).toSubring
    (fun x => (mem_closureIntegers_iff K₀ K Ω hbase hK L x.val).mpr x.property)

@[simp] theorem finiteClosureIntegerMap_coe
    (x : (finiteTopologicalData K₀ K Ω hbase L).Integers) :
    (finiteClosureIntegerMap K₀ K Ω hbase hK L x : Ω) = (x : L) := rfl

instance finiteClosureIntegerMap_isLocalHom :
    IsLocalHom (finiteClosureIntegerMap K₀ K Ω hbase hK L) :=
  isLocalHom_integerRestriction _ _ L.val.toRingHom
    (mem_closureIntegers_iff K₀ K Ω hbase hK L)

include hK in
/-- Absolute inertia preserves the residue kernel when restricted to a finite subfield. -/
theorem absoluteFiniteRestriction_mem_inertia
    (σ : LocalGalois.SepClosed.absoluteInertia K Ω) :
    absoluteFiniteRestriction K Ω L σ ∈ inertia (finiteTopologicalData K₀ K Ω hbase L) K := by
  let := LocalGalois.localNormedField K
  let := LocalGalois.localNormedField_ultrametric K
  let := LocalGalois.localNormedField_complete K
  change residueHom (finiteTopologicalData K₀ K Ω hbase L) K
    (absoluteFiniteRestriction K Ω L σ) = 1
  ext y
  obtain ⟨x, rfl⟩ := residue_surjective y
  apply (ResidueField.map (finiteClosureIntegerMap K₀ K Ω hbase hK L)).injective
  have hs : LocalGalois.residueHom K Ω σ.val = 1 := σ.property
  have hx := DFunLike.congr_fun hs (residue _ (finiteClosureIntegerMap K₀ K Ω hbase hK L x))
  change residue _ (LocalGalois.integerAut K Ω σ.val
    (finiteClosureIntegerMap K₀ K Ω hbase hK L x)) =
      residue _ (finiteClosureIntegerMap K₀ K Ω hbase hK L x) at hx
  change residue _ (finiteClosureIntegerMap K₀ K Ω hbase hK L
    (integerAutomorphism (finiteTopologicalData K₀ K Ω hbase L) K
      (absoluteFiniteRestriction K Ω L σ) x)) = residue _ (finiteClosureIntegerMap K₀ K Ω hbase hK L x)
  rw [← hx]
  congr 1
  apply Subtype.ext
  exact σ.val.restrictNormal_commutes L (x : L)

/-- Actual restriction from absolute inertia, with its subgroup topologies. -/
def absoluteInertiaRestriction : LocalGalois.SepClosed.absoluteInertia K Ω →ₜ*
    inertia (finiteTopologicalData K₀ K Ω hbase L) K where
  toMonoidHom := ((absoluteFiniteRestriction K Ω L).toMonoidHom.comp
    (LocalGalois.SepClosed.absoluteInertia K Ω).subtype).codRestrict _
      (absoluteFiniteRestriction_mem_inertia K₀ K Ω hbase hK L)
  continuous_toFun := ((absoluteFiniteRestriction K Ω L).continuous.comp
    continuous_subtype_val).subtype_mk _

@[simp] theorem absoluteInertiaRestriction_coe
    (σ : LocalGalois.SepClosed.absoluteInertia K Ω) :
    (absoluteInertiaRestriction K₀ K Ω hbase hK L σ : Gal(L/K)) =
      absoluteFiniteRestriction K Ω L σ := rfl

/-- Evaluation is restriction of the original automorphism on the same element. -/
theorem absoluteInertiaRestriction_apply (σ : LocalGalois.SepClosed.absoluteInertia K Ω) (x : L) :
    ((absoluteInertiaRestriction K₀ K Ω hbase hK L σ).val x : Ω) =
      AlgEquiv.toAlgHom σ.val (x : Ω) :=
  σ.val.restrictNormal_commutes L x

variable [IsSepClosed Ω]

private theorem localProjection_mem_absoluteInertia (w : localInertia K Ω) :
    localProjection K Ω w ∈ LocalGalois.SepClosed.absoluteInertia K Ω := by
  rw [← localResidueDegree_ker K Ω]
  change localResidueDegree K Ω (localProjection K Ω w) = 1
  have hw : localDegree K Ω w = 1 := w.property
  rw [show localResidueDegree K Ω (localProjection K Ω w) =
    Weil.frobenius (localDegree K Ω w) from w.val.property, hw, map_one]

/-- The Weil projection restricted to the degree-zero subgroup. -/
def weilInertiaProjection : localInertia K Ω →ₜ* LocalGalois.SepClosed.absoluteInertia K Ω :=
  { toMonoidHom :=
      ((localProjection K Ω).toMonoidHom.comp (localInertia K Ω).subtype).codRestrict _
        (localProjection_mem_absoluteInertia K Ω)
    continuous_toFun :=
      ((localProjection K Ω).continuous.comp continuous_subtype_val).subtype_mk _ }

@[simp] theorem weilInertiaProjection_coe (w : localInertia K Ω) :
    (weilInertiaProjection K Ω w : Gal(Ω/K)) = localProjection K Ω w := rfl

/-- The actual arithmetic restriction used by finite-inertia presentations. -/
def weilInertiaRestriction : localInertia K Ω →ₜ*
    inertia (finiteTopologicalData K₀ K Ω hbase L) K :=
  (absoluteInertiaRestriction K₀ K Ω hbase hK L).comp (weilInertiaProjection K Ω)

@[simp] theorem weilInertiaRestriction_coe (w : localInertia K Ω) :
    (weilInertiaRestriction K₀ K Ω hbase hK L w : Gal(L/K)) =
      absoluteFiniteRestriction K Ω L (localProjection K Ω w) := rfl

theorem weilInertiaRestriction_apply (w : localInertia K Ω) (x : L) :
    ((weilInertiaRestriction K₀ K Ω hbase hK L w).val x : Ω) =
      AlgEquiv.toAlgHom (localProjection K Ω w) (x : Ω) :=
  absoluteInertiaRestriction_apply K₀ K Ω hbase hK L (weilInertiaProjection K Ω w) x

variable {L} {M : FiniteGaloisIntermediateField K Ω}

omit [IsSepClosed Ω] in
/-- The absolute restriction square commutes on the actual field carriers. -/
theorem finiteInertiaRestriction_absolute (h : L ≤ M)
    (σ : LocalGalois.SepClosed.absoluteInertia K Ω) :
    finiteInertiaRestriction K₀ K Ω hbase h (absoluteInertiaRestriction K₀ K Ω hbase hK M σ) =
      absoluteInertiaRestriction K₀ K Ω hbase hK L σ := by
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  exact (finiteGaloisRestriction_apply K Ω h _ x).trans
    ((absoluteInertiaRestriction_apply K₀ K Ω hbase hK M σ (IntermediateField.inclusion h x)).trans
      (absoluteInertiaRestriction_apply K₀ K Ω hbase hK L σ x).symm)

/-- The Weil inertia restriction square commutes as well. -/
theorem finiteInertiaRestriction_weil (h : L ≤ M) (w : localInertia K Ω) :
    finiteInertiaRestriction K₀ K Ω hbase h (weilInertiaRestriction K₀ K Ω hbase hK M w) =
      weilInertiaRestriction K₀ K Ω hbase hK L w :=
  finiteInertiaRestriction_absolute K₀ K Ω hbase hK h (weilInertiaProjection K Ω w)

/-- A larger actual finite subextension has a smaller restriction kernel. -/
theorem weilInertiaRestriction_ker_le (h : L ≤ M) :
    (weilInertiaRestriction K₀ K Ω hbase hK M).toMonoidHom.ker ≤
      (weilInertiaRestriction K₀ K Ω hbase hK L).toMonoidHom.ker := by
  intro w hw
  change weilInertiaRestriction K₀ K Ω hbase hK L w = 1
  rw [← finiteInertiaRestriction_weil K₀ K Ω hbase hK h,
    show weilInertiaRestriction K₀ K Ω hbase hK M w = 1 from hw, map_one]

variable (A : FiniteRepresentation.{0, uΩ, uV} ℂ (localWeilGroup K Ω))

/-- The genuine representation restricted to the actual local Weil inertia. -/
abbrev localInertiaRepresentation : Representation ℂ (localInertia K Ω) A :=
  A.representation.comp (localInertia K Ω).subtype

/-- A finite Galois subextension whose restriction kernel acts trivially on the representation. -/
abbrev FiniteInertiaPresentation :=
  FiniteInertiaPresentationData fun L =>
    (weilInertiaRestriction K₀ K Ω hbase hK L).toMonoidHom.ker ≤
    (localInertiaRepresentation K Ω A).ker

namespace FiniteInertiaPresentation

variable {K₀ K Ω hbase hK A} (P : FiniteInertiaPresentation K₀ K Ω hbase hK A)

/-- Descent along the specific arithmetic restriction, with surjectivity explicit. -/
def representation (hsurj : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension)) :
    Representation ℂ (inertia (finiteTopologicalData K₀ K Ω hbase P.extension) K) A :=
  descendInertiaRepresentation _ K (weilInertiaRestriction K₀ K Ω hbase hK P.extension).toMonoidHom
    hsurj (localInertiaRepresentation K Ω A) P.kernel_le

@[simp] theorem representation_apply
    (hsurj : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension))
    (w : localInertia K Ω) :
    P.representation hsurj (weilInertiaRestriction K₀ K Ω hbase hK P.extension w) =
      A.representation w :=
  descendInertiaRepresentation_apply _ _ _ _ _ _ w

/-- The existing Artin expression at this particular actual presentation. -/
def artinConductor
    (hsurj : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension)) : ℚ :=
  artinConductorOfQuotient _ K (weilInertiaRestriction K₀ K Ω hbase hK P.extension).toMonoidHom
    hsurj (localInertiaRepresentation K Ω A) P.kernel_le

/-- The existing Swan expression at this particular actual presentation. -/
def swanConductor
    (hsurj : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension)) : ℚ :=
  swanConductorOfQuotient _ K (weilInertiaRestriction K₀ K Ω hbase hK P.extension).toMonoidHom
    hsurj (localInertiaRepresentation K Ω A) P.kernel_le

/-- Enlarging the actual finite Galois subfield preserves the presentation condition. -/
def refine (M : FiniteGaloisIntermediateField K Ω)
    (h : P.extension ≤ M) : FiniteInertiaPresentation K₀ K Ω hbase hK A where
  extension := M
  kernel_le := (weilInertiaRestriction_ker_le K₀ K Ω hbase hK h).trans P.kernel_le

/-- Pull the descended action back along actual finite-inertia restriction. -/
def pullback (hsurj : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension))
    (M : FiniteGaloisIntermediateField K Ω) (h : P.extension ≤ M) :
    Representation ℂ (inertia (finiteTopologicalData K₀ K Ω hbase M) K) A :=
  (P.representation hsurj).comp (finiteInertiaRestriction K₀ K Ω hbase h).toMonoidHom

@[simp] theorem pullback_apply
    (hsurj : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension))
    (M : FiniteGaloisIntermediateField K Ω) (h : P.extension ≤ M) (w : localInertia K Ω) :
    P.pullback hsurj M h (weilInertiaRestriction K₀ K Ω hbase hK M w) = A.representation w :=
  (congrArg (P.representation hsurj) (finiteInertiaRestriction_weil K₀ K Ω hbase hK h w)).trans
    (representation_apply (K₀ := K₀) (hbase := hbase) (hK := hK) P hsurj w)

/-- When descent at the refinement is available, it is this actual pullback. -/
theorem representation_refine
    (hsurj : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension))
    (M : FiniteGaloisIntermediateField K Ω)
    (h : P.extension ≤ M) (hM : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK M)) :
    (P.refine M h).representation hM = P.pullback hsurj M h := by
  apply MonoidHom.ext
  exact hM.forall.mpr fun w =>
    (representation_apply (K₀ := K₀) (hbase := hbase) (hK := hK) (P.refine M h) hM w).trans
      (P.pullback_apply hsurj M h w).symm

end FiniteInertiaPresentation

/-- A common finite Galois subextension with actual inclusions of the two presentations. -/
abbrev FiniteInertiaCommonRefinement (P Q : FiniteInertiaPresentation K₀ K Ω hbase hK A) :=
  FiniteInertiaCommonRefinementData P Q

namespace FiniteInertiaCommonRefinement

/-- The compositum of the two actual finite Galois subfields is a common refinement. -/
def compositum (P Q : FiniteInertiaPresentation K₀ K Ω hbase hK A) :
    FiniteInertiaCommonRefinement K₀ K Ω hbase hK A P Q where
  extension := P.extension ⊔ Q.extension
  left_le := le_sup_left
  right_le := le_sup_right

variable {K₀ K Ω hbase hK A} {P Q : FiniteInertiaPresentation K₀ K Ω hbase hK A}
    (R : FiniteInertiaCommonRefinement K₀ K Ω hbase hK A P Q)

/-- The left descended action pulled to the actual common field. -/
def leftRepresentation
    (hP : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension)) :=
  P.pullback hP R.extension R.left_le

/-- The right descended action pulled to the actual common field. -/
def rightRepresentation
    (hQ : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK Q.extension)) :=
  Q.pullback hQ R.extension R.right_le

@[simp] theorem leftRepresentation_apply
    (hP : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension))
    (w : localInertia K Ω) :
    R.leftRepresentation hP (weilInertiaRestriction K₀ K Ω hbase hK R.extension w) =
      A.representation w :=
  P.pullback_apply hP R.extension R.left_le w

@[simp] theorem rightRepresentation_apply
    (hQ : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK Q.extension))
    (w : localInertia K Ω) :
    R.rightRepresentation hQ (weilInertiaRestriction K₀ K Ω hbase hK R.extension w) =
      A.representation w :=
  Q.pullback_apply hQ R.extension R.right_le w

/-- Surjectivity at the common field makes the two genuine pullbacks equal. -/
theorem representations_eq
    (hP : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK Q.extension))
    (hR : Function.Surjective (weilInertiaRestriction K₀ K Ω hbase hK R.extension)) :
    R.leftRepresentation hP = R.rightRepresentation hQ := by
  apply MonoidHom.ext
  exact hR.forall.mpr fun w =>
    (R.leftRepresentation_apply hP w).trans (R.rightRepresentation_apply hQ w).symm

end FiniteInertiaCommonRefinement

end Spectral

namespace SepClosed

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance : NontriviallyNormedField K := LocalGalois.localNormedField K
local instance : IsUltrametricDist K := LocalGalois.localNormedField_ultrametric K
local instance : CompleteSpace K := LocalGalois.localNormedField_complete K

private theorem localBaseNorm_compatible (a b : K) : ‖a‖ ≤ ‖b‖ ↔ a ≤ᵥ b :=
  (LocalGalois.localNormedField_le K a b).trans (valuation K).vle_iff_le.symm

private theorem localBaseIntegers_compatible (x : K) :
    spectralNorm K K x ≤ 1 ↔ valuation K x ≤ 1 := by
  rw [show spectralNorm K K x = ‖x‖ by simpa using (spectralNorm_extends (L := K) x)]
  simpa only [norm_one, map_one] using LocalGalois.localNormedField_le K x 1

variable (L : FiniteGaloisIntermediateField K Ω)

@[inherit_doc Local.finiteTopologicalData]
abbrev finiteTopologicalData : LocalField.TopologicalData K L :=
  localTopologicalData K L

@[inherit_doc Local.finiteBaseEmbedding]
abbrev finiteBaseEmbedding : K →ₐ[K] L := Local.finiteBaseEmbedding K K Ω L

@[inherit_doc Local.finiteClosureIntegerMap]
abbrev finiteClosureIntegerMap :
    (finiteTopologicalData K Ω L).Integers →+* LocalGalois.SepClosed.closureIntegers K Ω :=
  Local.finiteClosureIntegerMap K K Ω (localBaseNorm_compatible K) (localBaseIntegers_compatible K) L

@[inherit_doc Local.absoluteInertiaRestriction]
abbrev absoluteInertiaRestriction :
    LocalGalois.SepClosed.absoluteInertia K Ω →ₜ* inertia (finiteTopologicalData K Ω L) K :=
  Local.absoluteInertiaRestriction K K Ω
    (localBaseNorm_compatible K) (localBaseIntegers_compatible K) L

@[inherit_doc Local.weilInertiaProjection]
abbrev weilInertiaProjection :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.weilInertiaProjection K Ω

@[inherit_doc Local.weilInertiaRestriction]
abbrev weilInertiaRestriction :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.weilInertiaRestriction K K Ω (localBaseNorm_compatible K) (localBaseIntegers_compatible K) L

variable {L} {M : FiniteGaloisIntermediateField K Ω}

@[inherit_doc Local.finiteIntegerMap]
abbrev finiteIntegerMap (h : L ≤ M) :
    (finiteTopologicalData K Ω L).Integers →+* (finiteTopologicalData K Ω M).Integers :=
  Local.finiteIntegerMap K K Ω (localBaseNorm_compatible K) h

@[inherit_doc Local.finiteInertiaRestriction]
abbrev finiteInertiaRestriction (h : L ≤ M) :
    inertia (finiteTopologicalData K Ω M) K →ₜ* inertia (finiteTopologicalData K Ω L) K :=
  Local.finiteInertiaRestriction K K Ω (localBaseNorm_compatible K) h

variable (A : FiniteRepresentation.{0, uΩ, uV} ℂ
  (letI : IsSepClosed Ω := IsSepClosure.sep_closed K
   localWeilGroup K Ω))

@[inherit_doc Local.localInertiaRepresentation]
abbrev localInertiaRepresentation :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.localInertiaRepresentation K Ω A

@[inherit_doc Local.FiniteInertiaPresentation]
abbrev FiniteInertiaPresentation :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaPresentation K K Ω
    (localBaseNorm_compatible K) (localBaseIntegers_compatible K) A

namespace FiniteInertiaPresentation

variable {K Ω A} (P : FiniteInertiaPresentation K Ω A)

@[inherit_doc Local.FiniteInertiaPresentation.representation]
abbrev representation (hsurj : Function.Surjective (weilInertiaRestriction K Ω P.extension)) :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaPresentation.representation P hsurj

@[inherit_doc Local.FiniteInertiaPresentation.artinConductor]
abbrev artinConductor (hsurj : Function.Surjective (weilInertiaRestriction K Ω P.extension)) : ℚ :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaPresentation.artinConductor P hsurj

@[inherit_doc Local.FiniteInertiaPresentation.swanConductor]
abbrev swanConductor (hsurj : Function.Surjective (weilInertiaRestriction K Ω P.extension)) : ℚ :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaPresentation.swanConductor P hsurj

@[inherit_doc Local.FiniteInertiaPresentation.refine]
abbrev refine (M : FiniteGaloisIntermediateField K Ω) (h : P.extension ≤ M) :
    FiniteInertiaPresentation K Ω A :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaPresentation.refine P M h

@[inherit_doc Local.FiniteInertiaPresentation.pullback]
abbrev pullback (hsurj : Function.Surjective (weilInertiaRestriction K Ω P.extension))
    (M : FiniteGaloisIntermediateField K Ω) (h : P.extension ≤ M) :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaPresentation.pullback P hsurj M h

end FiniteInertiaPresentation

@[inherit_doc Local.FiniteInertiaCommonRefinement]
abbrev FiniteInertiaCommonRefinement (P Q : FiniteInertiaPresentation K Ω A) :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaCommonRefinement K K Ω
    (localBaseNorm_compatible K) (localBaseIntegers_compatible K) A P Q

namespace FiniteInertiaCommonRefinement

@[inherit_doc Local.FiniteInertiaCommonRefinement.compositum]
abbrev compositum (P Q : FiniteInertiaPresentation K Ω A) :
    FiniteInertiaCommonRefinement K Ω A P Q :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaCommonRefinement.compositum K K Ω
    (localBaseNorm_compatible K) (localBaseIntegers_compatible K) A P Q

variable {K Ω A} {P Q : FiniteInertiaPresentation K Ω A}
    (R : FiniteInertiaCommonRefinement K Ω A P Q)

@[inherit_doc Local.FiniteInertiaCommonRefinement.leftRepresentation]
abbrev leftRepresentation (hP : Function.Surjective (weilInertiaRestriction K Ω P.extension)) :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaCommonRefinement.leftRepresentation R hP

@[inherit_doc Local.FiniteInertiaCommonRefinement.rightRepresentation]
abbrev rightRepresentation (hQ : Function.Surjective (weilInertiaRestriction K Ω Q.extension)) :=
  letI : IsSepClosed Ω := IsSepClosure.sep_closed K
  Local.FiniteInertiaCommonRefinement.rightRepresentation R hQ

end FiniteInertiaCommonRefinement

end SepClosed
end Langlands.Ramification.Local


namespace Langlands.Ramification.Padic

open IsLocalRing
open scoped ValuativeRel
open Weil.Local

-- The published record eliminators take their motive universe first.
universe w u v
variable {p : ℕ} [inst : Fact p.Prime] (F : PadicField.{u} p)

local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField

private theorem padicBaseNorm_compatible (a b : Padic p) :
    ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b := by
  change ‖a‖ ≤ ‖b‖ ↔ Padic.mulValuation a ≤ Padic.mulValuation b
  simp only [← not_lt, Padic.norm_lt_norm_iff_mulValuation_lt]

private theorem padicBaseIntegers_compatible (x : F.Carrier) :
    spectralNorm (Padic p) F.Carrier x ≤ 1 ↔ ValuativeRel.valuation F.Carrier x ≤ 1 :=
  (Local.mem_finiteIntegers_iff (Padic p) (padicBaseNorm_compatible (p := p)) F.Carrier x).symm

variable (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))

@[inherit_doc Local.finiteBaseEmbedding]
def finiteBaseEmbedding : F.Carrier →ₐ[Padic p] (absoluteFiniteExtension F L).Carrier :=
  Local.finiteBaseEmbedding (Padic p) F.Carrier (AlgebraicClosure F.Carrier) L

@[inherit_doc Local.finiteClosureIntegerMap]
def finiteClosureIntegerMap :
    (absoluteFiniteExtension F L).canonicalTopologicalData.Integers →+*
      F.closureIntegers F.canonicalTopologicalData :=
  Local.finiteClosureIntegerMap (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L

@[simp] theorem finiteClosureIntegerMap_coe
    (x : (absoluteFiniteExtension F L).canonicalTopologicalData.Integers) :
    (finiteClosureIntegerMap F L x : AlgebraicClosure F.Carrier) = (x : L) :=
  Local.finiteClosureIntegerMap_coe (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L x

instance finiteClosureIntegerMap_isLocalHom : IsLocalHom (finiteClosureIntegerMap F L) :=
  Local.finiteClosureIntegerMap_isLocalHom (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L

@[inherit_doc Local.absoluteFiniteRestriction_mem_inertia]
theorem absoluteFiniteRestriction_mem_inertia
    (σ : F.absoluteInertia F.canonicalTopologicalData) :
    absoluteFiniteRestriction F L σ ∈
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier :=
  Local.absoluteFiniteRestriction_mem_inertia (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L σ

@[inherit_doc Local.absoluteInertiaRestriction]
def absoluteInertiaRestriction :
    F.absoluteInertia F.canonicalTopologicalData →ₜ*
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier :=
  Local.absoluteInertiaRestriction (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L

@[simp] theorem absoluteInertiaRestriction_coe
    (σ : F.absoluteInertia F.canonicalTopologicalData) :
    (absoluteInertiaRestriction F L σ : Gal(L/F.Carrier)) =
      absoluteFiniteRestriction F L σ :=
  Local.absoluteInertiaRestriction_coe (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L σ

@[inherit_doc Local.absoluteInertiaRestriction_apply]
theorem absoluteInertiaRestriction_apply
    (σ : F.absoluteInertia F.canonicalTopologicalData) (x : L) :
    ((absoluteInertiaRestriction F L σ).val x : AlgebraicClosure F.Carrier) =
      AlgEquiv.toAlgHom σ.val (x : AlgebraicClosure F.Carrier) :=
  Local.absoluteInertiaRestriction_apply (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L σ x

@[inherit_doc Local.weilInertiaProjection]
def weilInertiaProjection :
    localInertia F →ₜ* F.absoluteInertia F.canonicalTopologicalData :=
  Local.weilInertiaProjection F.Carrier (AlgebraicClosure F.Carrier)

@[simp] theorem weilInertiaProjection_coe (w : localInertia F) :
    (weilInertiaProjection F w : Field.absoluteGaloisGroup F.Carrier) =
      localProjection F w :=
  Local.weilInertiaProjection_coe F.Carrier (AlgebraicClosure F.Carrier) w

@[inherit_doc Local.weilInertiaRestriction]
def weilInertiaRestriction : localInertia F →ₜ*
    inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier :=
  Local.weilInertiaRestriction (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L

@[simp] theorem weilInertiaRestriction_coe (w : localInertia F) :
    (weilInertiaRestriction F L w : Gal(L/F.Carrier)) =
      absoluteFiniteRestriction F L (localProjection F w) :=
  Local.weilInertiaRestriction_coe (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L w

theorem weilInertiaRestriction_apply (w : localInertia F) (x : L) :
    ((weilInertiaRestriction F L w).val x : AlgebraicClosure F.Carrier) =
      AlgEquiv.toAlgHom (localProjection F w) (x : AlgebraicClosure F.Carrier) :=
  Local.weilInertiaRestriction_apply (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) L w x

variable {L} {M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}

@[inherit_doc Local.finiteGaloisRestriction]
def finiteGaloisRestriction (h : L ≤ M) : Gal(M/F.Carrier) →ₜ* Gal(L/F.Carrier) :=
  Local.finiteGaloisRestriction F.Carrier (AlgebraicClosure F.Carrier) h

@[inherit_doc Local.finiteGaloisRestriction_apply]
theorem finiteGaloisRestriction_apply (h : L ≤ M) (σ : Gal(M/F.Carrier)) (x : L) :
    ((finiteGaloisRestriction F h σ) x : AlgebraicClosure F.Carrier) =
      (σ (IntermediateField.inclusion h x) : AlgebraicClosure F.Carrier) :=
  Local.finiteGaloisRestriction_apply F.Carrier (AlgebraicClosure F.Carrier) h σ x

@[inherit_doc Local.finiteGaloisRestriction_mem_inertia]
theorem finiteGaloisRestriction_mem_inertia (h : L ≤ M)
    (σ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier) :
    finiteGaloisRestriction F h σ ∈
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier :=
  Local.finiteGaloisRestriction_mem_inertia (Padic p) F.Carrier (AlgebraicClosure F.Carrier)
    (padicBaseNorm_compatible (p := p)) h σ

@[inherit_doc Local.finiteInertiaRestriction]
def finiteInertiaRestriction (h : L ≤ M) :
    inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier →ₜ*
      inertia (absoluteFiniteExtension F L).canonicalTopologicalData F.Carrier :=
  Local.finiteInertiaRestriction (Padic p) F.Carrier (AlgebraicClosure F.Carrier)
    (padicBaseNorm_compatible (p := p)) h

@[simp] theorem finiteInertiaRestriction_coe (h : L ≤ M)
    (σ : inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier) :
    (finiteInertiaRestriction F h σ : Gal(L/F.Carrier)) = finiteGaloisRestriction F h σ :=
  Local.finiteInertiaRestriction_coe (Padic p) F.Carrier (AlgebraicClosure F.Carrier)
    (padicBaseNorm_compatible (p := p)) h σ

@[inherit_doc Local.finiteInertiaRestriction_absolute]
theorem finiteInertiaRestriction_absolute (h : L ≤ M)
    (σ : F.absoluteInertia F.canonicalTopologicalData) :
    finiteInertiaRestriction F h (absoluteInertiaRestriction F M σ) =
      absoluteInertiaRestriction F L σ :=
  Local.finiteInertiaRestriction_absolute (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) h σ

@[inherit_doc Local.finiteInertiaRestriction_weil]
theorem finiteInertiaRestriction_weil (h : L ≤ M) (w : localInertia F) :
    finiteInertiaRestriction F h (weilInertiaRestriction F M w) = weilInertiaRestriction F L w :=
  Local.finiteInertiaRestriction_weil (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) h w

@[inherit_doc Local.weilInertiaRestriction_ker_le]
theorem weilInertiaRestriction_ker_le (h : L ≤ M) :
    (weilInertiaRestriction F M).toMonoidHom.ker ≤
      (weilInertiaRestriction F L).toMonoidHom.ker :=
  Local.weilInertiaRestriction_ker_le (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) h

variable (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))

@[inherit_doc Local.localInertiaRepresentation]
abbrev localInertiaRepresentation : Representation ℂ (localInertia F) A :=
  Local.localInertiaRepresentation F.Carrier (AlgebraicClosure F.Carrier) A

private abbrev presentationCondition
    (L : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)) : Prop :=
  (weilInertiaRestriction F L).toMonoidHom.ker ≤ (localInertiaRepresentation F A).ker

@[inherit_doc Local.FiniteInertiaPresentation]
abbrev FiniteInertiaPresentation :=
  Local.FiniteInertiaPresentationData (presentationCondition F A)

namespace FiniteInertiaPresentation

variable {F A} (P : FiniteInertiaPresentation F A)

@[match_pattern]
abbrev mk (extension : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (kernel_le : (weilInertiaRestriction F extension).toMonoidHom.ker ≤
      (localInertiaRepresentation F A).ker) : FiniteInertiaPresentation F A :=
  ⟨extension, kernel_le⟩

abbrev extension (self : FiniteInertiaPresentation F A) :
    FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  Local.FiniteInertiaPresentationData.extension self

abbrev kernel_le (self : FiniteInertiaPresentation F A) :
    (weilInertiaRestriction F self.extension).toMonoidHom.ker ≤
    (localInertiaRepresentation F A).ker :=
  Local.FiniteInertiaPresentationData.kernel_le self

@[elab_as_elim]
abbrev rec {motive : FiniteInertiaPresentation F A → Sort w} :=
  Local.FiniteInertiaPresentationData.rec (motive := motive)

@[elab_as_elim]
abbrev recOn {motive : FiniteInertiaPresentation F A → Sort w} :=
  Local.FiniteInertiaPresentationData.recOn (motive := motive)

@[elab_as_elim]
abbrev casesOn {motive : FiniteInertiaPresentation F A → Sort w} :=
  Local.FiniteInertiaPresentationData.casesOn (motive := motive)

section

variable {inst}

abbrev ctorIdx (x : FiniteInertiaPresentation F A) : ℕ :=
  Local.FiniteInertiaPresentationData.ctorIdx x

instance _sizeOf_inst (F : PadicField.{u} p)
    (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)) :
    SizeOf (FiniteInertiaPresentation F A) :=
  inferInstanceAs (SizeOf (Local.FiniteInertiaPresentationData (presentationCondition F A)))

set_option linter.auxLemma false in
abbrev _sizeOf_1 (t : FiniteInertiaPresentation F A) : ℕ := sizeOf t

-- Partial application keeps the generated names of the constructor arguments.
theorem mk.inj :
    type_of% (@Local.FiniteInertiaPresentationData.mk.inj _ _ _ _ _ (presentationCondition F A)) :=
  @Local.FiniteInertiaPresentationData.mk.inj _ _ _ _ _ (presentationCondition F A)

abbrev mk.noConfusion :=
  @Local.FiniteInertiaPresentationData.mk.noConfusion.{w, u, u} _ _ _ _ _
    (presentationCondition F A)

end

abbrev mk._flat_ctor := @mk _ _ F A

@[simp]
theorem mk.injEq :
    type_of% (@Local.FiniteInertiaPresentationData.mk.injEq _ _ _ _ _ (presentationCondition F A)) :=
  @Local.FiniteInertiaPresentationData.mk.injEq _ _ _ _ _ (presentationCondition F A)

theorem mk.sizeOf_spec
    (extension : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (kernel_le : (weilInertiaRestriction F extension).toMonoidHom.ker ≤
      (localInertiaRepresentation F A).ker) :
    sizeOf (mk extension kernel_le) = 1 + sizeOf extension :=
  Local.FiniteInertiaPresentationData.mk.sizeOf_spec extension kernel_le

abbrev noConfusionType (P : Sort w) {p : ℕ} [inst : Fact p.Prime] {F : PadicField.{u} p}
    {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)} (t : FiniteInertiaPresentation F A)
    {p' : ℕ} [inst' : Fact p'.Prime] {F' : PadicField.{u} p'}
    {A' : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F')}
    (t' : FiniteInertiaPresentation F' A') : Sort w :=
  Local.FiniteInertiaPresentationData.noConfusionType P t t'

abbrev noConfusion {P : Sort w} {p : ℕ} {inst : Fact p.Prime} {F : @PadicField.{u} p inst}
    {A : FiniteRepresentation.{0, u, v} ℂ (@localWeilGroup p inst F)}
    {t : @FiniteInertiaPresentation p inst F A}
    {p' : ℕ} {inst' : Fact p'.Prime} {F' : @PadicField.{u} p' inst'}
    {A' : FiniteRepresentation.{0, u, v} ℂ (@localWeilGroup p' inst' F')}
    {t' : @FiniteInertiaPresentation p' inst' F' A'}
    (eq_1 : p = p') (eq_2 : HEq inst inst') (eq_3 : HEq F F') (eq_4 : HEq A A')
    (eq_5 : HEq t t') :
    @noConfusionType P p inst F A t p' inst' F' A' t' := by
  cases eq_1
  cases eq_2
  cases eq_3
  cases eq_4
  cases eq_5
  cases t
  exact fun k => k HEq.rfl

@[inherit_doc Local.FiniteInertiaPresentation.representation]
def representation (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) :
    Representation ℂ (inertia (absoluteFiniteExtension F P.extension).canonicalTopologicalData
      F.Carrier) A :=
  Local.FiniteInertiaPresentation.representation P hsurj

@[simp] theorem representation_apply
    (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) (w : localInertia F) :
    P.representation hsurj (weilInertiaRestriction F P.extension w) = A.representation w :=
  Local.FiniteInertiaPresentation.representation_apply P hsurj w

@[inherit_doc Local.FiniteInertiaPresentation.artinConductor]
def artinConductor (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) : ℚ :=
  Local.FiniteInertiaPresentation.artinConductor P hsurj

@[inherit_doc Local.FiniteInertiaPresentation.swanConductor]
def swanConductor (hsurj : Function.Surjective (weilInertiaRestriction F P.extension)) : ℚ :=
  Local.FiniteInertiaPresentation.swanConductor P hsurj

@[inherit_doc Local.FiniteInertiaPresentation.refine]
def refine (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) : FiniteInertiaPresentation F A :=
  Local.FiniteInertiaPresentation.refine P M h

@[inherit_doc Local.FiniteInertiaPresentation.pullback]
def pullback (hsurj : Function.Surjective (weilInertiaRestriction F P.extension))
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) :
    Representation ℂ (inertia (absoluteFiniteExtension F M).canonicalTopologicalData F.Carrier) A :=
  Local.FiniteInertiaPresentation.pullback P hsurj M h

@[simp] theorem pullback_apply
    (hsurj : Function.Surjective (weilInertiaRestriction F P.extension))
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) (w : localInertia F) :
    P.pullback hsurj M h (weilInertiaRestriction F M w) = A.representation w :=
  Local.FiniteInertiaPresentation.pullback_apply P hsurj M h w

@[inherit_doc Local.FiniteInertiaPresentation.representation_refine]
theorem representation_refine
    (hsurj : Function.Surjective (weilInertiaRestriction F P.extension))
    (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (h : P.extension ≤ M) (hM : Function.Surjective (weilInertiaRestriction F M)) :
    (P.refine M h).representation hM = P.pullback hsurj M h :=
  Local.FiniteInertiaPresentation.representation_refine P hsurj M h hM

end FiniteInertiaPresentation

@[inherit_doc Local.FiniteInertiaCommonRefinement]
abbrev FiniteInertiaCommonRefinement (P Q : FiniteInertiaPresentation F A) :=
  Local.FiniteInertiaCommonRefinementData P Q

namespace FiniteInertiaCommonRefinement

@[inherit_doc Local.FiniteInertiaCommonRefinement.compositum]
def compositum (P Q : FiniteInertiaPresentation F A) : FiniteInertiaCommonRefinement F A P Q :=
  Local.FiniteInertiaCommonRefinement.compositum (Padic p) F.Carrier (AlgebraicClosure F.Carrier) (padicBaseNorm_compatible (p := p))
    (padicBaseIntegers_compatible F) A P Q

variable {F A} {P Q : FiniteInertiaPresentation F A} (R : FiniteInertiaCommonRefinement F A P Q)

@[match_pattern]
abbrev mk (extension : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (left_le : P.extension ≤ extension) (right_le : Q.extension ≤ extension) :
    FiniteInertiaCommonRefinement F A P Q :=
  ⟨extension, left_le, right_le⟩

abbrev extension (self : FiniteInertiaCommonRefinement F A P Q) :
    FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  Local.FiniteInertiaCommonRefinementData.extension self

abbrev left_le (self : FiniteInertiaCommonRefinement F A P Q) : P.extension ≤ self.extension :=
  Local.FiniteInertiaCommonRefinementData.left_le self

abbrev right_le (self : FiniteInertiaCommonRefinement F A P Q) : Q.extension ≤ self.extension :=
  Local.FiniteInertiaCommonRefinementData.right_le self

@[elab_as_elim]
abbrev rec {motive : FiniteInertiaCommonRefinement F A P Q → Sort w} :=
  Local.FiniteInertiaCommonRefinementData.rec (motive := motive)

@[elab_as_elim]
abbrev recOn {motive : FiniteInertiaCommonRefinement F A P Q → Sort w} :=
  Local.FiniteInertiaCommonRefinementData.recOn (motive := motive)

@[elab_as_elim]
abbrev casesOn {motive : FiniteInertiaCommonRefinement F A P Q → Sort w} :=
  Local.FiniteInertiaCommonRefinementData.casesOn (motive := motive)

section

variable {inst}

abbrev ctorIdx (x : FiniteInertiaCommonRefinement F A P Q) : ℕ :=
  Local.FiniteInertiaCommonRefinementData.ctorIdx x

instance _sizeOf_inst (F : PadicField.{u} p)
    (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F))
    (P Q : FiniteInertiaPresentation F A) : SizeOf (FiniteInertiaCommonRefinement F A P Q) :=
  inferInstanceAs (SizeOf (Local.FiniteInertiaCommonRefinementData P Q))

set_option linter.auxLemma false in
abbrev _sizeOf_1 (t : FiniteInertiaCommonRefinement F A P Q) : ℕ := sizeOf t

theorem mk.inj : type_of% (@Local.FiniteInertiaCommonRefinementData.mk.inj _ _ _ _ _ _ P Q) :=
  @Local.FiniteInertiaCommonRefinementData.mk.inj _ _ _ _ _ _ P Q

abbrev mk.noConfusion :=
  @Local.FiniteInertiaCommonRefinementData.mk.noConfusion.{w, u, u} _ _ _ _ _ _ P Q

end

abbrev mk._flat_ctor := @mk _ _ F A P Q

@[simp]
theorem mk.injEq : type_of% (@Local.FiniteInertiaCommonRefinementData.mk.injEq _ _ _ _ _ _ P Q) :=
  @Local.FiniteInertiaCommonRefinementData.mk.injEq _ _ _ _ _ _ P Q

theorem mk.sizeOf_spec
    (extension : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
    (left_le : P.extension ≤ extension) (right_le : Q.extension ≤ extension) :
    sizeOf (mk extension left_le right_le) = 1 + sizeOf extension :=
  Local.FiniteInertiaCommonRefinementData.mk.sizeOf_spec extension left_le right_le

-- Both the result sort and the first presentation were named `P` by Lean.
abbrev noConfusionType (P : Sort w) {p : ℕ} [inst : Fact p.Prime] {F : PadicField.{u} p}
    {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)}
    {P Q : FiniteInertiaPresentation F A} (t : FiniteInertiaCommonRefinement F A P Q)
    {p' : ℕ} [inst' : Fact p'.Prime] {F' : PadicField.{u} p'}
    {A' : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F')}
    {P' Q' : FiniteInertiaPresentation F' A'} (t' : FiniteInertiaCommonRefinement F' A' P' Q') :
    Sort w :=
  Local.FiniteInertiaCommonRefinementData.noConfusionType ‹Sort w› t t'

abbrev noConfusion {P : Sort w} {p : ℕ} {inst : Fact p.Prime} {F : @PadicField.{u} p inst}
    {A : FiniteRepresentation.{0, u, v} ℂ (@localWeilGroup p inst F)}
    {P Q : @FiniteInertiaPresentation p inst F A}
    {t : @FiniteInertiaCommonRefinement p inst F A P Q}
    {p' : ℕ} {inst' : Fact p'.Prime} {F' : @PadicField.{u} p' inst'}
    {A' : FiniteRepresentation.{0, u, v} ℂ (@localWeilGroup p' inst' F')}
    {P' Q' : @FiniteInertiaPresentation p' inst' F' A'}
    {t' : @FiniteInertiaCommonRefinement p' inst' F' A' P' Q'}
    (eq_1 : p = p') (eq_2 : HEq inst inst') (eq_3 : HEq F F') (eq_4 : HEq A A')
    (eq_5 : HEq P P') (eq_6 : HEq Q Q') (eq_7 : HEq t t') :
    @noConfusionType ‹Sort w› p inst F A P Q t p' inst' F' A' P' Q' t' := by
  cases eq_1
  cases eq_2
  cases eq_3
  cases eq_4
  cases eq_5
  cases eq_6
  cases eq_7
  cases t
  exact fun k => k HEq.rfl

@[inherit_doc Local.FiniteInertiaCommonRefinement.leftRepresentation]
def leftRepresentation (hP : Function.Surjective (weilInertiaRestriction F P.extension)) :
    Representation ℂ (inertia (absoluteFiniteExtension F R.extension).canonicalTopologicalData
      F.Carrier) A :=
  Local.FiniteInertiaCommonRefinement.leftRepresentation R hP

@[inherit_doc Local.FiniteInertiaCommonRefinement.rightRepresentation]
def rightRepresentation (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)) :
    Representation ℂ (inertia (absoluteFiniteExtension F R.extension).canonicalTopologicalData
      F.Carrier) A :=
  Local.FiniteInertiaCommonRefinement.rightRepresentation R hQ

@[simp] theorem leftRepresentation_apply
    (hP : Function.Surjective (weilInertiaRestriction F P.extension)) (w : localInertia F) :
    R.leftRepresentation hP (weilInertiaRestriction F R.extension w) = A.representation w :=
  Local.FiniteInertiaCommonRefinement.leftRepresentation_apply R hP w

@[simp] theorem rightRepresentation_apply
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension)) (w : localInertia F) :
    R.rightRepresentation hQ (weilInertiaRestriction F R.extension w) = A.representation w :=
  Local.FiniteInertiaCommonRefinement.rightRepresentation_apply R hQ w

@[inherit_doc Local.FiniteInertiaCommonRefinement.representations_eq]
theorem representations_eq
    (hP : Function.Surjective (weilInertiaRestriction F P.extension))
    (hQ : Function.Surjective (weilInertiaRestriction F Q.extension))
    (hR : Function.Surjective (weilInertiaRestriction F R.extension)) :
    R.leftRepresentation hP = R.rightRepresentation hQ :=
  Local.FiniteInertiaCommonRefinement.representations_eq R hP hQ hR

end FiniteInertiaCommonRefinement

end Langlands.Ramification.Padic
