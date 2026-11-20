import Langlands.Geometry.FormalGroup.PointFactorization
import Langlands.Geometry.FormalGroup.RationalSectionComposition
import Langlands.Geometry.FormalGroup.IsogenyBaseChange
import Langlands.Geometry.FormalGroup.LocalQuasiIsogeny
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-! # Faithfulness of rationalization for scalar-divisible sources -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {π : O}

/-- A scalar power acts injectively on integral formal Hom out of a divisible source. -/
theorem IsPiDivisible.smul_pow_injective (hM : M.IsPiDivisible π) (n : ℕ) :
    Function.Injective (fun f : Hom M N => π ^ n • f) := by
  intro f g h
  apply (hM.scalarPower_locallySurjective n).comp_right_cancel
  simpa only [scalarHom, Hom.comp_smul, Hom.comp_id] using h

section FractionField

variable [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type w} [Field F] [Algebra O F] [IsFractionRing O F]

/-- Integral maps out of a divisible source embed into the actual fraction-field tensor Hom. -/
theorem RationalHom.ofHom_injective_of_isPiDivisible (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) :
    Function.Injective (ofHom (F := F) (M := M) (N := N)) := by
  let : IsLocalizedModule (nonZeroDivisors O) (ofHom (F := F) (M := M) (N := N)) :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors O) F
  intro f g heq
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors O)
    (ofHom (F := F) (M := M) (N := N))).mp heq
  have hs0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  obtain ⟨n, a, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπ
  change (s : O) • f = (s : O) • g at hs
  rw [ha, mul_smul, mul_smul] at hs
  apply hM.smul_pow_injective n
  have hinv := congrArg (fun x : Hom M N => (↑a⁻¹ : O) • x) hs
  simpa only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] using hinv

end FractionField

section OpenRestriction

variable [IsDomain O] [IsDiscreteValuationRing O]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {U : Opens (PrimeSpectrum R)}

/-- Equality of rationalized integral maps yields equality of the actual integral maps
on a neighbourhood of every point, when the source is scalar-divisible. -/
theorem RationalSection.exists_restrict_integral_eq (hπ : Irreducible π)
    (hM : M.IsPiDivisible π) (f g : OpenIntegralHom M N U)
    (h : (ofIntegral U f : RationalSection F M N U) = ofIntegral U g)
    (x : PrimeSpectrum R) (hx : x ∈ U) :
    ∃ (V : Opens (PrimeSpectrum R)) (_ : x ∈ V) (i : V ⟶ U),
      Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op) f =
        Hom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op) g := by
  let s : (rationalHomTypePresheaf F M N).obj (op U) := RationalHom.ofHom f
  let t : (rationalHomTypePresheaf F M N).obj (op U) := RationalHom.ofHom g
  have hc := Presheaf.equalizerSieve_mem
    (Opens.grothendieckTopology (PrimeSpectrum.Top R)) (rationalHomTypeUnit F M N) s t h
  obtain ⟨V, i, hi, hxV⟩ := hc x hx
  refine ⟨V, hxV, i, ?_⟩
  have hMV : (M.overAlgebra ((coefficientStructurePresheaf R).obj (op V))).IsPiDivisible π :=
    hM.map (IsScalarTower.toAlgHom O R _)
  apply RationalHom.ofHom_injective_of_isPiDivisible (F := F) hπ hMV
  change RationalHom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op)
      (RationalHom.ofHom f : RationalHom F _ _) =
    RationalHom.algebraMapLinear ((coefficientStructurePresheaf R).map i.op)
      (RationalHom.ofHom g : RationalHom F _ _) at hi
  simpa only [RationalHom.algebraMapLinear_ofHom] using hi

end OpenRestriction

end Langlands.FormalGroup.ModuleLaw
