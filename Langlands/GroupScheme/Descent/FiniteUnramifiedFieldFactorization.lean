import Langlands.Galois.Local.SeparableUnramifiedProof
import Mathlib.RingTheory.FiniteType

/-! # Factoring finite fields through unramified Galois stages -/

noncomputable section

universe u

open Langlands.LocalGalois Langlands.LocalGalois.Separable

namespace Langlands.GroupScheme.Descent.FiniteUnramified

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

/-- An actual factorization of a finite field embedding through a finite
Galois unramified subfield of the chosen separable closure. -/
structure FieldFactorization (K : Type u) [Field K] [Algebra F K]
    (a : K →ₐ[F] inertiaFixedField F) where
  field : IntermediateField F (SeparableClosure F)
  finite : FiniteDimensional F field
  galois : IsGalois F field
  inertia : field ≤ inertiaFixedField F
  unramified : ArithmeticUnramified F field
  embedding : K →ₐ[F] field
  factorization : (IntermediateField.inclusion inertia).comp embedding = a

/-- Every specified finite field embedding into the inertia fixed field
factors through a finite Galois arithmetically unramified stage. -/
theorem nonempty_fieldFactorization (K : Type u) [Field K] [Algebra F K]
    [FiniteDimensional F K] (a : K →ₐ[F] inertiaFixedField F) :
    Nonempty (FieldFactorization F K a) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out (R := F) (A := K))
  obtain ⟨E, hfin, hgal, hE, hunr, hcoeff⟩ :=
    (separableUnramified F).2 (s.image a)
  let b := (fixedFieldToSepClosure F).comp a
  have hb : ∀ x : K, b x ∈ E := by
    have htop : (⊤ : Subalgebra F K) ≤ E.toSubalgebra.comap b := by
      rw [← hs]
      apply Algebra.adjoin_le
      intro x hx
      exact hcoeff (a x) (Finset.mem_image_of_mem a hx)
    exact fun x => htop (Algebra.mem_top)
  refine ⟨{ field := E
            finite := hfin
            galois := hgal
            inertia := hE
            unramified := hunr
            embedding := b.codRestrict E.toSubalgebra hb
            factorization := ?_ }⟩
  ext x
  rfl

/-- Choose a finite unramified Galois factorization while retaining the
specified embedding into the inertia fixed field. -/
def fieldFactorization (K : Type u) [Field K] [Algebra F K]
    [FiniteDimensional F K] (a : K →ₐ[F] inertiaFixedField F) :
    FieldFactorization F K a :=
  Classical.choice (nonempty_fieldFactorization F K a)

end Langlands.GroupScheme.Descent.FiniteUnramified
