module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import StacksFrontier.RingTheory.Depth.Defs.Defs

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Nakayama's lemma for the maximal ideal of a local ring

For a nonzero finite module `M` over a local ring `(R, 𝔪)` one has `𝔪 • M ≠ M`.

## Main results

* `Module.maximalIdeal_smul_top_ne_top`: `𝔪 • M ≠ M` for a nonzero finite module `M` over a
  local ring `(R, 𝔪)`.
* `Module.one_le_depth_iff_exists_isSMulRegular`: for a finite module `M`, the depth of `M`
  along `I` is at least one exactly when some element of `I` acts regularly on `M`.

## References

* [Stacks Project, Tag 00LI](https://stacks.math.columbia.edu/tag/00LI)
-/

@[expose] public section

/-- Nakayama's lemma: the maximal ideal of a local ring does not saturate a nonzero finite
module. -/
public theorem Module.maximalIdeal_smul_top_ne_top {R : Type*} [CommRing R] [IsLocalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
  .symm <| Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator <| by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _
      (mt Module.annihilator_eq_top_iff.mp (not_subsingleton M))]

end
