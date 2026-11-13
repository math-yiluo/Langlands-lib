# Identifying an irreducible head by a positive count

Author: Worker 4988. Module `Langlands.Representation.Classification.HeadDetectingCount`,
namespace `Langlands.Classification.HeadDetectingCount`. Internal helper for the proof of
Tadić's Corollary A.6(ii) (`IrreducibleLanglandsHeadProductProof`). It has no Library
statement and no literature counterpart; it is a general counting argument with
Jordan–Hölder multiplicities.

## Counting lemmas

For a field `k`, a monoid `H` and representations in Mathlib's `Rep k H`:

- `exists_count_le_of_injective`: if `i : A → B` is an injective intertwiner and `B` has
  Jordan–Hölder multiplicity `m_B` of a test representation `τ`, then `A` has a
  multiplicity `m_A ≤ m_B` of `τ`. Proof: the short exact sequence
  `0 → A → B → B/i(A) → 0` and the published additivity
  `jordanHolderShortExactDecomposition`.
- `exists_count_le_of_surjective`: the same for a surjective intertwiner `B → C`, with
  the short exact sequence `0 → ker q → B → C → 0`.

## Smooth representations

For smooth representations of a topological group `G` over `k`:

- `isSubquotient_of_haveSameJordanHolderFactors`: if `X` and `I` have finite length and
  the same composition factors, every irreducible subquotient of `X` is a subquotient of
  `I`. Proof: equality of classes in the finite-length Grothendieck group
  (`ofRepresentation_eq_of_haveSameJordanHolderFactors`) and
  `hasConstituentSupportIn_of_class_natural_multiple`.
- `isSubquotient_kernel_of_not_iso`: if `q : I ↠ L` with `L` irreducible and `P` is an
  irreducible subquotient of `I` that is not isomorphic to `L`, then `P` is a
  subquotient of `ker q`. Proof: additivity of composition multiplicities on
  `0 → ker q → I → L → 0` at the class of `P`, where the class of `L` contributes `0`.
- `false_of_kernel_count`: let `J` be a functor to `Rep k H` that preserves zero
  morphisms, injections and surjections. Suppose `J I` has multiplicity `m` of `τ` and
  `J L` has a multiplicity `c ≥ m`. Then the kernel of `J q` has multiplicity `0`. So no
  subquotient `P` of `ker q` can have a positive multiplicity of `τ` in `J P`. The
  argument: `J` maps a subquotient presentation `C ↪ ker q`, `C ↠ P` to an injection of
  `J C` into `ker (J q)` and a surjection `J C ↠ J P`. The two counting lemmas above then
  bound the count.
- `nonempty_iso_of_count` (the result used later), in the setting of
  `false_of_kernel_count`. Let `X` and `I` have finite length and the same composition
  factors, let `q : I ↠ L` with `L` irreducible, and let `r : X ↠ P` with `P`
  irreducible. If `J I` has multiplicity `m` of `τ`, `J L` has a multiplicity at least
  `m`, and `J P` has a positive multiplicity, then `P ≅ L`. Proof: otherwise `P` is a
  subquotient of `X`, hence of `I`, hence of `ker q`, contradicting
  `false_of_kernel_count`.
