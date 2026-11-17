import Mathlib.RepresentationTheory.Invariants

/-! # Averaging over a finite quotient of a group -/

noncomputable section

universe uk uG uV

namespace Langlands.FiniteQuotientAveraging

open Representation

variable {k : Type uk} [CommRing k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]

section Average

variable (ρ : Representation k G V) (N : Subgroup G) [N.Normal]
  [Fintype (G ⧸ N)] [Invertible (Fintype.card (G ⧸ N) : k)]

/-- Average an `N`-fixed vector over `G/N` to obtain a `G`-fixed vector. -/
def normalQuotientAverage :
    invariants (ρ.comp N.subtype) →ₗ[k] ρ.invariants where
  toFun v :=
    let τ := ρ.quotientToInvariants N
    let w := τ.averageMap v
    ⟨w.val, fun g => congrArg Subtype.val (τ.averageMap_invariant v (g : G ⧸ N))⟩
  map_add' v w := by
    apply Subtype.ext
    exact congrArg (fun z : invariants (ρ.comp N.subtype) => (z : V))
      ((ρ.quotientToInvariants N).averageMap.map_add v w)
  map_smul' c v := by
    apply Subtype.ext
    exact congrArg (fun z : invariants (ρ.comp N.subtype) => (z : V))
      ((ρ.quotientToInvariants N).averageMap.map_smul c v)

/-- The quotient average is the normalized sum over any coset section. -/
theorem normalQuotientAverage_apply
    (v : invariants (ρ.comp N.subtype)) (s : G ⧸ N → G)
    (hs : ∀ q, (s q : G ⧸ N) = q) :
    (normalQuotientAverage ρ N v).val =
      ⅟(Fintype.card (G ⧸ N) : k) • ∑ q : G ⧸ N, ρ (s q) v.val := by
  change (((ρ.quotientToInvariants N).averageMap v).val) = _
  simp only [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum,
    Representation.asAlgebraHom_single, MonoidAlgebra.of_apply,
    LinearMap.smul_apply, LinearMap.sum_apply, one_smul]
  rw [Submodule.coe_smul, Submodule.coe_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  nth_rw 1 [← hs q]
  rfl

/-- A quotient average remains in any subrepresentation containing its input. -/
theorem normalQuotientAverage_mem (U : Subrepresentation ρ)
    (v : invariants (ρ.comp N.subtype)) (hv : v.val ∈ U) :
    (normalQuotientAverage ρ N v).val ∈ U := by
  rw [normalQuotientAverage_apply ρ N v Quotient.out (fun q => Quotient.out_eq q)]
  exact U.toSubmodule.smul_mem _ (U.toSubmodule.sum_mem fun q _ =>
    U.apply_mem_toSubmodule q.out hv)

end Average

end Langlands.FiniteQuotientAveraging
