import Langlands.Algebra.HopfPointIntegralClosure
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Coefficient ideals of finite-type maps into monoid algebras -/

noncomputable section

universe u v w x

open scoped TensorProduct

namespace Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M]
  {B : Type w} [CommRing B] [Algebra R B]

/-- The ideal of all degree-`m` coefficients in the range of an algebra map. -/
def algebraCoefficientIdeal (φ : B →ₐ[R] AddMonoidAlgebra R M) (m : M) : Ideal R :=
  ((DiagonalCoalgebraImage.coefficient m).comp φ.toLinearMap).range

theorem mem_algebraCoefficientIdeal (φ : B →ₐ[R] AddMonoidAlgebra R M) (m : M) (r : R) :
    r ∈ algebraCoefficientIdeal φ m ↔ ∃ b : B, (φ b).coeff m = r :=
  Iff.rfl

/-- The coefficient ideal of a scalar extension is the extended ideal. -/
theorem algebraCoefficientIdeal_scalarExtension (φ : B →ₐ[R] AddMonoidAlgebra R M)
    (A : Type x) [CommRing A] [Algebra R A] (m : M) :
    algebraCoefficientIdeal (scalarExtension φ A) m =
      (algebraCoefficientIdeal φ m).map (algebraMap R A) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨z, rfl⟩ := (mem_algebraCoefficientIdeal (scalarExtension φ A) m a).mp ha
    clear ha
    induction z with
    | tmul a b =>
      rw [coeff_scalarExtension_tmul]
      exact Ideal.mul_mem_left _ a (Ideal.mem_map_of_mem _
        ((mem_algebraCoefficientIdeal φ m _).mpr ⟨b, rfl⟩))
    | add z z' hz hz' => simpa using Ideal.add_mem _ hz hz'
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨b, rfl⟩ := (mem_algebraCoefficientIdeal φ m r).mp hr
    exact (mem_algebraCoefficientIdeal (scalarExtension φ A) m _).mpr
      ⟨1 ⊗ₜ[R] b, by simp⟩

private theorem algebraCoefficientIdeal_eq_of_range_eq
    {C : Type x} [CommRing C] [Algebra R C]
    {φ : B →ₐ[R] AddMonoidAlgebra R M} {ψ : C →ₐ[R] AddMonoidAlgebra R M}
    (h : φ.range = ψ.range) (m : M) :
    algebraCoefficientIdeal φ m = algebraCoefficientIdeal ψ m := by
  apply SetLike.ext
  intro r
  let c := fun z : AddMonoidAlgebra R M => z.coeff m
  change r ∈ Set.range (c ∘ φ) ↔ r ∈ Set.range (c ∘ ψ)
  simp only [Set.range_comp, ← AlgHom.coe_range, h]

/-- Coefficient ideals of a finite-type algebra map are finitely generated
over an arbitrary commutative base ring. -/
theorem algebraCoefficientIdeal_fg [Algebra.FiniteType R B]
    (φ : B →ₐ[R] AddMonoidAlgebra R M) (m : M) :
    (algebraCoefficientIdeal φ m).FG := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType R B).out
  let C : Finset R := s.biUnion fun b => (φ b).coeff.support.image (φ b).coeff
  let R₀ := Algebra.adjoin ℤ (C : Set R)
  let : Algebra.FiniteType ℤ R₀ := Algebra.FiniteType.adjoin_of_finite C.finite_toSet
  let : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  let f := AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R₀ R)
  have lifts (b : s) : ∃ p : AddMonoidAlgebra R₀ M, f p = φ b := by
    have hmem (n : M) : (φ b).coeff n ∈ Set.range (algebraMap R₀ R) := by
      rw [Subalgebra.setRange_algebraMap]
      by_cases hn : n ∈ (φ b).coeff.support
      · exact Algebra.subset_adjoin (Finset.mem_biUnion.mpr
          ⟨b, b.property, Finset.mem_image_of_mem _ hn⟩)
      · rw [Finsupp.notMem_support_iff.mp hn]
        exact R₀.zero_mem
    have h : (φ b).coeff ∈ Set.range (Finsupp.mapRange (algebraMap R₀ R) (map_zero _)) := by
      rw [Finsupp.range_mapRange]
      exact hmem
    obtain ⟨p, hp⟩ := h
    exact ⟨AddMonoidAlgebra.ofCoeff p, AddMonoidAlgebra.coeff_injective hp⟩
  choose p hp using lifts
  let D : Subalgebra R₀ (AddMonoidAlgebra R₀ M) := Algebra.adjoin R₀ (Set.range p)
  let ψ := scalarExtension (R := R₀) (M := M) (B := D) D.val R
  have hD : D ≤ (φ.range.restrictScalars R₀).comap f := by
    apply Algebra.adjoin_le
    rintro _ ⟨b, rfl⟩
    change f (p b) ∈ φ.range
    rw [hp b]
    exact φ.mem_range_self _
  have hψ : φ.range = ψ.range := by
    apply le_antisymm
    · rw [← Algebra.map_top φ, ← hs, ← Algebra.adjoin_image]
      apply Algebra.adjoin_le
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨1 ⊗ₜ[R₀] (⟨p ⟨b, hb⟩, Algebra.subset_adjoin ⟨⟨b, hb⟩, rfl⟩⟩ : D), ?_⟩
      simpa [ψ] using hp ⟨b, hb⟩
    · rintro _ ⟨z, rfl⟩
      induction z with
      | tmul a d =>
        change (scalarExtension (R := R₀) (M := M) (B := D) D.val R)
          (a ⊗ₜ[R₀] d) ∈ φ.range
        rw [scalarExtension_tmul]
        exact φ.range.smul_mem (hD d.property) a
      | add z z' hz hz' =>
        rw [ψ.toRingHom.map_add]
        exact φ.range.add_mem hz hz'
  rw [algebraCoefficientIdeal_eq_of_range_eq hψ m]
  rw [show ψ = scalarExtension (R := R₀) (M := M) (B := D) D.val R from rfl,
    algebraCoefficientIdeal_scalarExtension]
  exact Ideal.FG.map (IsNoetherian.noetherian _) _

end Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus

namespace Langlands.Algebra.HopfPointIntegralClosure

open Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M]
  {B : Type w} [CommRing B] [Bialgebra R B] [Algebra.FiniteType R B]

/-- Over an arbitrary commutative base, every coefficient ideal of a finite-type
bialgebra map into a group algebra is generated by an idempotent. -/
theorem exists_idempotent_generator_coeffIdeal
    (φ : B →ₐc[R] AddMonoidAlgebra R M) (m : M) :
    ∃ e : R, IsIdempotentElem e ∧ coeffIdeal φ m = Ideal.span {e} :=
  ((coeffIdeal φ m).isIdempotentElem_iff_of_fg
    (algebraCoefficientIdeal_fg φ.toAlgHom m)).mp (isIdempotentElem_coeffIdeal φ m)

end Langlands.Algebra.HopfPointIntegralClosure
