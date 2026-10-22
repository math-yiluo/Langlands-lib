import Langlands.ClassFieldTheory.Local.CyclicClass
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Norm.Transitivity

/-! # Fixed units and the actual field norm

This is the field-specific bridge needed by the degree-zero Tate quotient.
It does not construct a reciprocity map.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]

/-- Inclusion of base-field units into the invariant part of the actual coefficient module. -/
def baseUnitsToInvariants :
    Additive Kˣ →+ (unitsRepresentation K L).ρ.invariants where
  toFun a := ⟨baseUnit K L a.toMul, baseUnit_fixed K L a.toMul⟩
  map_zero' := by
    apply Subtype.ext
    exact map_one (Units.map (algebraMap K L).toMonoidHom)
  map_add' a b := by
    apply Subtype.ext
    exact map_mul (Units.map (algebraMap K L).toMonoidHom) a.toMul b.toMul

theorem baseUnitsToInvariants_injective :
    Function.Injective (baseUnitsToInvariants K L) := by
  intro a b hab
  apply Units.ext
  apply (algebraMap K L).injective
  exact congrArg (fun x : (unitsRepresentation K L).ρ.invariants =>
    Units.val (Additive.toMul (x.val : Additive Lˣ))) hab

theorem baseUnitsToInvariants_surjective [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (baseUnitsToInvariants K L) := by
  intro x
  have hfixed : ∀ σ : Gal(L/K), σ (Units.val (Additive.toMul (x.val : Additive Lˣ))) = Units.val (Additive.toMul (x.val : Additive Lˣ)) := by
    intro σ
    exact congrArg (fun a : unitsRepresentation K L => Units.val (Additive.toMul (a : Additive Lˣ))) (x.property σ)
  obtain ⟨a, ha⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed (Units.val (Additive.toMul (x.val : Additive Lˣ)))).2 hfixed
  have ha0 : a ≠ 0 := by
    intro h
    have hzero : Units.val (Additive.toMul (x.val : Additive Lˣ)) = 0 := by simpa [h] using ha.symm
    exact Units.ne_zero (x.val : Additive Lˣ).toMul hzero
  refine ⟨Additive.ofMul (Units.mk0 a ha0), ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact ha

/-- Fixed units in a finite Galois extension are exactly base-field units. -/
def baseUnitsEquivInvariants [FiniteDimensional K L] [IsGalois K L] :
    Additive Kˣ ≃+ (unitsRepresentation K L).ρ.invariants :=
  AddEquiv.ofBijective (baseUnitsToInvariants K L)
    ⟨baseUnitsToInvariants_injective K L, baseUnitsToInvariants_surjective K L⟩

@[simp] theorem baseUnitsEquivInvariants_apply
    [FiniteDimensional K L] [IsGalois K L] (a : Kˣ) :
    (baseUnitsEquivInvariants K L (Additive.ofMul a)).val = baseUnit K L a := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient norm is the actual field norm, embedded back into the extension. -/
theorem unitsRepresentation_norm [FiniteDimensional K L] [IsGalois K L]
    [Fintype Gal(L/K)] (a : Lˣ) :
    (unitsRepresentation K L).ρ.norm (Additive.ofMul a) =
      baseUnit K L (Units.map (Algebra.norm K) a) := by
  simp only [Representation.norm, LinearMap.sum_apply]
  change (∑ σ : Gal(L/K), Additive.ofMul (σ • a)) = _
  rw [← ofMul_prod]
  change Additive.ofMul (∏ σ : Gal(L/K), σ • a) =
    Additive.ofMul (Units.map (algebraMap K L).toMonoidHom (Units.map (Algebra.norm K) a))
  apply congrArg Additive.ofMul
  apply Units.ext
  change (Units.coeHom L) (∏ σ : Gal(L/K), σ • a) =
    algebraMap K L (Algebra.norm K (a : L))
  rw [map_prod]
  have henum : (Finset.univ : Finset Gal(L/K)) =
      @Finset.univ Gal(L/K) (AlgEquiv.fintype K L) := by
    ext σ
    simp
  rw [henum]
  exact (Algebra.norm_eq_prod_automorphisms (K := K) (a : L)).symm

end Langlands.ClassFieldTheory.Local
