# Existence of irreducible cuspidal representations of `GL_n(k)` over a finite field

Lean module: `Langlands.Representation.FiniteGeneralLinear.CuspidalExistence`, namespace
`Langlands.FiniteGeneralLinear`.

## Results

- `irreduciblePolynomialLabels_nonempty`: for a finite field `k` and `0 < n`, the set
  `irreduciblePolynomialLabels n k` (Bushnell–Kutzko's `𝔍(n, k)`: monic irreducible
  polynomials of degree `n`, with `X` removed) is nonempty.
- `natCard_cuspidalModelClass`: for a finite field `k` and `0 < n`,
  `Nat.card (CuspidalModelClass n k) = Nat.card (irreduciblePolynomialLabels n k)`.
- `cuspidalModelClass_nonempty`: for a finite field `k` and `0 < n`, the type
  `CuspidalModelClass n k` of finite-dimensional irreducible classes of `GL_n(k)` whose
  representatives are cuspidal is nonempty.
- `exists_irreducible_cuspidal_fdRep`: for a finite field `k` and `0 < n` there is
  `V : FDRep ℂ (GeneralLinear n k)` with `Representation.IsIrreducible V.ρ` and
  `IsCuspidal V.ρ` (the Library's Harish-Chandra cuspidality: no proper standard block
  parabolic has a nonzero vector fixed by its unipotent radical).

## Proofs

**Irreducible polynomials.** Let `p` be the characteristic of `k`. Mathlib's
`FiniteField.Extension k p n` is a field extension of degree `n`
(`FiniteField.finrank_extension`). By the primitive element theorem it is `k⟮α⟯`, and the
minimal polynomial of `α` is monic, irreducible and of degree `[k⟮α⟯ : k] = n`
(`IntermediateField.adjoin.finrank`). For `n ≠ 1` it differs from `X` because its degree is not
one. For `n = 1` the polynomial `X - 1` is used instead.

**The count.** The equality of cardinalities is the one established inside
`Langlands.Representation.FiniteGeneralLinear.CuspidalClassCountBoundProof` for
`cuspidalClassCountBound`, whose auxiliary declarations there are private; the argument is
reproduced here. Cuspidal multisets of total rank `m + 1` and polynomial factor
multisets of weight `m + 1` both have `Nat.card kˣ * Nat.card k ^ m` elements
(`card_cuspidalMultiset_succ`, from the Gelfand–Graev representation, and
`card_polynomialFactorMultiset_succ`), and both weight-zero fibres are singletons.
`WeightedMultiset.card_fiber_eq_of_card_eq` then gives equal numbers of labels of each weight,
and the label fibres are identified with `CuspidalModelClass n k` and with
`irreduciblePolynomialLabels n k`.

**Nonemptiness.** `irreduciblePolynomialLabels n k` is finite
(`irreduciblePolynomialLabels_finite`) and nonempty, so its `Nat.card` is positive; hence so is
`Nat.card (CuspidalModelClass n k)`, and the type is nonempty. A class `a` gives the
representative `FiniteRep.VirtualCharacter.rep a.1`, which is irreducible
(`FiniteRep.VirtualCharacter.isIrreducible_rep`) and cuspidal (the defining property `a.2`).

## Sources

The existence of cuspidal representations of `GL_n` over a finite field is part of Green's
parametrisation (Green, *The characters of the finite general linear groups*, Trans. AMS 80
(1955), `green-1955-characters-finite-general-linear`), as recorded in Bushnell–Kutzko,
*Simple types in GL(N): computing conjugacy classes* (1994),
`bushnell-kutzko-1994-simple-types-conjugacy-classes`, printed p. 125, after (3.6). The proof
here does not use Green's character theory: it derives existence from the Library's count of
cuspidal classes by Gelfand–Graev constituents.
