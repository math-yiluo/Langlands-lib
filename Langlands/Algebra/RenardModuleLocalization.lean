import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum

/-! The corrected linear-map interface for Renard A.III.1, example 4. -/

namespace Langlands.Renard.ModuleLocalization

universe u v x w

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Each denominator acts by a unit of the actual ring of module endomorphisms. -/
def IsSLocal (N : Type w) [AddCommGroup N] [Module R N] : Prop :=
  ∀ s : S, IsUnit (algebraMap R (Module.End R N) (s : R))

theorem isSLocal_iff_bijective (N : Type w) [AddCommGroup N] [Module R N] :
    IsSLocal S N ↔ ∀ s : S, Function.Bijective (fun n : N => (s : R) • n) := by
  constructor
  · intro h s
    exact (Module.End.isUnit_iff _).mp (h s)
  · intro h s
    exact (Module.End.isUnit_iff _).mpr (h s)

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Unique factorization through a concrete map into every local target in
the independent universe `w`. -/
def HasUniversalProperty {L : Type x} [AddCommGroup L] [Module R L]
    (ι : M →ₗ[R] L) : Prop :=
  ∀ (N : Type w) [AddCommGroup N] [Module R N], IsSLocal S N →
    ∀ f : M →ₗ[R] N, ∃! g : L →ₗ[R] N, g.comp ι = f

theorem localizedModule_isSLocal : IsSLocal S (LocalizedModule S M) :=
  IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M)

theorem divBy_scalar (s : S) (z : LocalizedModule S M) :
    LocalizedModule.divBy s ((s : R) • z) = z :=
  LocalizedModule.divBy_mul_by s z

theorem scalar_divBy (s : S) (z : LocalizedModule S M) :
    (s : R) • LocalizedModule.divBy s z = z :=
  LocalizedModule.mul_by_divBy s z

theorem divBy_mk (s t : S) (m : M) :
    LocalizedModule.divBy s (LocalizedModule.mk m t) =
      LocalizedModule.mk m (t * s) :=
  rfl

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The actual Mathlib lift, with the corrected locality predicate as input. -/
noncomputable def factor (hN : IsSLocal S N) (f : M →ₗ[R] N) :
    LocalizedModule S M →ₗ[R] N :=
  LocalizedModule.lift S f hN

theorem factor_mk (hN : IsSLocal S N) (f : M →ₗ[R] N) (m : M) (s : S) :
    factor S hN f (LocalizedModule.mk m s) = (hN s).unit⁻¹.val (f m) :=
  LocalizedModule.lift_mk S f hN m s

theorem factor_comp (hN : IsSLocal S N) (f : M →ₗ[R] N) :
    (factor S hN f).comp (LocalizedModule.mkLinearMap S M) = f :=
  LocalizedModule.lift_comp S f hN

theorem factor_unique (hN : IsSLocal S N) (f : M →ₗ[R] N)
    (g : LocalizedModule S M →ₗ[R] N)
    (hg : g.comp (LocalizedModule.mkLinearMap S M) = f) :
    g = factor S hN f :=
  (LocalizedModule.lift_unique S f hN g hg).symm

theorem canonical_hasUniversalProperty :
    HasUniversalProperty.{u, v, max u v, w} S (LocalizedModule.mkLinearMap S M) := by
  intro N _ _ hN f
  exact ⟨factor S hN f, factor_comp S hN f, fun g hg => factor_unique S hN f g hg⟩

section Comparison

variable {L : Type x} [AddCommGroup L] [Module R L]
variable (ι : M →ₗ[R] L) (κ : M →ₗ[R] N)
variable [IsLocalizedModule S ι] [IsLocalizedModule S κ]

/-- Mathlib's canonical comparison, without a new localization construction. -/
noncomputable abbrev comparison : L ≃ₗ[R] N :=
  IsLocalizedModule.linearEquiv S ι κ

theorem comparison_comp :
    (comparison S ι κ).toLinearMap.comp ι = κ := by
  ext m
  exact IsLocalizedModule.linearEquiv_apply S ι κ m

theorem comparison_symm_comp :
    (comparison S ι κ).symm.toLinearMap.comp κ = ι := by
  ext m
  exact IsLocalizedModule.linearEquiv_symm_apply S ι κ m

end Comparison

theorem localizedModule_subsingleton (h0 : (0 : R) ∈ S) :
    Subsingleton (LocalizedModule S M) :=
  LocalizedModule.subsingleton h0

section Counterexample

/-- Internal source diagnosis: rationals are local for powers of the integer 2. -/
theorem rationals_isSLocal : IsSLocal (Submonoid.powers (2 : ℤ)) ℚ := by
  rw [isSLocal_iff_bijective]
  intro s
  obtain ⟨n, hn⟩ := s.property
  have hs : (s : ℤ) ≠ 0 := by
    rw [← hn]
    exact pow_ne_zero n (by norm_num)
  have hsQ : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hs
  simpa only [zsmul_eq_mul] using
    (show Function.Bijective (fun q : ℚ => ((s : ℤ) : ℚ) * q) from
      (LinearEquiv.smulOfNeZero ℚ ℚ ((s : ℤ) : ℚ) hsQ).bijective)

theorem no_integer_inverse_two (t : ℤ) :
    (t * 2) • (1 : ℚ) ≠ 1 := by
  intro h
  have hi : t * 2 = (1 : ℤ) := by
    change ((t * 2 : ℤ) : ℚ) * 1 = 1 at h
    rw [mul_one] at h
    exact_mod_cast h
  omega

/-- The book's pointwise scalar-inverse parenthesis fails for a local module. -/
theorem scalar_inverse_parenthesis_counterexample :
    IsSLocal (Submonoid.powers (2 : ℤ)) ℚ ∧
      ¬ (∀ (s : Submonoid.powers (2 : ℤ)) (q : ℚ),
        ∃ t : ℤ, (t * (s : ℤ)) • q = q ∧ ((s : ℤ) * t) • q = q) := by
  refine ⟨rationals_isSLocal, ?_⟩
  intro h
  obtain ⟨t, ht, _⟩ := h ⟨2, Submonoid.mem_powers 2⟩ 1
  exact no_integer_inverse_two t ht

/-- Multiplication by one half, as an integer-linear endomorphism. -/
noncomputable def rationalHalf : Module.End ℤ ℚ :=
  (algebraMap ℚ (Module.End ℚ ℚ) (1 / 2)).restrictScalars ℤ

theorem rationalHalf_apply (q : ℚ) :
    rationalHalf q = (1 / 2 : ℚ) * q :=
  rfl

theorem rationalHalf_scalar_two (q : ℚ) :
    rationalHalf ((2 : ℤ) • q) = q := by
  rw [rationalHalf_apply, zsmul_eq_mul]
  norm_num [← mul_assoc]

theorem scalar_two_rationalHalf (q : ℚ) :
    (2 : ℤ) • rationalHalf q = q := by
  rw [rationalHalf_apply, zsmul_eq_mul]
  norm_num [← mul_assoc]

theorem rationalHalf_not_integer_scalar (t : ℤ) :
    rationalHalf ≠ algebraMap ℤ (Module.End ℤ ℚ) t := by
  intro h
  apply no_integer_inverse_two t
  calc
    (t * 2) • (1 : ℚ) = t • ((2 : ℤ) • (1 : ℚ)) := mul_smul t 2 1
    _ = rationalHalf ((2 : ℤ) • (1 : ℚ)) := by rw [h]; rfl
    _ = 1 := rationalHalf_scalar_two 1

end Counterexample

end Langlands.Renard.ModuleLocalization
