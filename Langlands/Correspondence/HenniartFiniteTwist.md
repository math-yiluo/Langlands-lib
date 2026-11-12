# Finite-order twists of finite-image Weil classes

Author: Worker 4803. Module `Langlands.Correspondence.HenniartFiniteTwist`, namespace
`Langlands.Henniart.Extension`. A supporting module of `HenniartSurjectivityStepProof`;
it defines no statement.

## Content

Generic facts about finite-dimensional complex representations of a group `G`:

- `hasFiniteImage_of_equiv`: finite image transfers along an equivalence, because
  `B(g) = e ∘ A(g) ∘ e⁻¹`.
- `hasFiniteImage_twist`: if `A` has finite image and `χ` takes values in the `N`-th
  roots of unity, `N > 0`, then `χ ⊗ A` has finite image: its operators lie in the
  finite set `{ζ T}` with `ζ^N = 1` and `T` in the image of `A`.
- `determinant_pow_card_eq_one`: if an irreducible class `b` factors through a
  homomorphism `f : G → Q` with `Q` finite (`Weil.FactorsThrough`), its determinant
  character `det b` satisfies `(det b)(g)^|Q| = 1`, because `det b = det A ∘ f` and
  `f(g)^|Q| = 1`.

For the local Weil group of a p-adic field `K`:

- `factorsThrough_of_mem`: a unitary class whose generator lies in the span of the
  classes factoring through `q` factors through `q` composed with the projection to
  the absolute Galois group.
- `isFiniteFactoring_twist`: let `b₀` be a unitary class factoring through a finite
  quotient of the absolute Galois group, and `χ` a continuous character of the local
  Weil group with `χ^N = 1`, `N > 0`. Then `χ · b₀` factors through a finite quotient.
  A continuous representative `R` of `b₀` is equivalent to the inflation of a
  representation of the finite quotient, so it has finite image; `χ ⊗ R` is continuous
  with finite image, so it is of Galois type (`Weil.Local.localWeilGaloisTypeFor`) and
  factors through a finite quotient (`LocalWeil.exists_finiteQuotient_of_isLocalGaloisType`).

## Provenance

Internal; standard facts. The finite-quotient step follows the published proof of
`rankOne_isFiniteFactoring` (module `HenniartRankOneStageProof`).
