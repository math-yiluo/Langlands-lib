import Langlands.BaseChange.Norm
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Globalization of a cyclic extension of local fields

This statement formalizes the number-field globalization used by Arthur–Clozel (1989),
Chapter 1, §6.3 (printed pp. 54–55), with the split-place norm condition motivated by the
function-field analogue of Henniart–Lemaire (2011), §II.6.7 (printed p. 123).
The derived formulation allows any cyclic degree and requires both split and inert places
of arbitrarily large norm outside any finite set. See the paired Markdown for provenance
and the proposed proof route.
-/

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace Langlands.TraceFormula

open Langlands.BaseChange

universe u v

/-- The `K`-algebra `L` splits completely over `A` with `σ` acting as the cyclic shift.
An `A`-algebra isomorphism `e : A ⊗[K] L ≃ₐ[A] (Fin l → A)` carries `id ⊗ σ` to
`x ↦ x ∘ finRotate l`, so `e ((id ⊗ σ) y) i = e y (i + 1)` with indices modulo `l`. -/
def IsCyclicShiftSplit (K L A : Type*) [Field K] [Field L] [Algebra K L] [CommRing A]
    [Algebra K A] (σ : L ≃ₐ[K] L) (l : ℕ) : Prop :=
  ∃ e : A ⊗[K] L ≃ₐ[A] (Fin l → A),
    ∀ y : A ⊗[K] L,
      e (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) σ y) =
        fun i => e y (finRotate l i)

/-- For a nonarchimedean local field `F` of characteristic zero and a cyclic `F`-algebra `E`
of degree `l` with generator `σ` which is a field, there are number fields `K` and `L` with
a generator `σK` of a cyclic `K`-algebra structure of degree `l` on `L` satisfying the
following conditions.

* Every infinite place of `K` splits in `L`, with `σK` acting as the cyclic shift.
* There is a finite place `v₀` of `K` with a topological ring isomorphism `φ : K_{v₀} ≃+* F`
  and a ring isomorphism `ψ : K_{v₀} ⊗[K] L ≃+* E` extending `φ` and carrying `id ⊗ σK`
  to `σ`. The map `ψ` is a homeomorphism for the module topology over `K_{v₀}`.
* For any finite set of finite places and any lower bound on the absolute norm, a finite
  place outside the set meets the bound and splits in `L`, with `σK` acting as the cyclic shift.
* The same avoidance and norm bound can be imposed on a finite place `v` whose extended
  ideal `v 𝓞_L` is prime. -/
def CyclicFieldGlobalizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l → IsField E →
    ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : NumberField K) (_ : NumberField L)
      (_ : Algebra K L) (σK : L ≃ₐ[K] L),
      IsCyclicAlgebra σK l ∧
      (∀ w : InfinitePlace K, IsCyclicShiftSplit K L w.Completion σK l) ∧
      (∃ (v₀ : HeightOneSpectrum (𝓞 K)) (φ : v₀.adicCompletion K ≃+* F)
          (ψ : v₀.adicCompletion K ⊗[K] L ≃+* E),
        Continuous φ ∧ Continuous φ.symm ∧
        (∀ a : v₀.adicCompletion K, ψ (a ⊗ₜ[K] (1 : L)) = algebraMap F E (φ a)) ∧
        (∀ y : v₀.adicCompletion K ⊗[K] L,
          ψ (Algebra.TensorProduct.congr
              (AlgEquiv.refl : v₀.adicCompletion K ≃ₐ[v₀.adicCompletion K] _) σK y) =
            σ (ψ y)) ∧
        letI : TopologicalSpace (v₀.adicCompletion K ⊗[K] L) :=
          moduleTopology (v₀.adicCompletion K) (v₀.adicCompletion K ⊗[K] L)
        Continuous ψ ∧ Continuous ψ.symm) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ),
        ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ N ≤ Ideal.absNorm v.asIdeal ∧
          IsCyclicShiftSplit K L (v.adicCompletion K) σK l) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ),
        ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ N ≤ Ideal.absNorm v.asIdeal ∧
          (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.asIdeal).IsPrime)

end Langlands.TraceFormula
