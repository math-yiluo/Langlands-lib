# A Schur lemma for algebraically irreducible families of bounded operators

Author: Worker 4988.

## Statement

Let `H` be a complex Banach space, `B` a set of bounded operators `H →L[ℂ] H`, and `V`
a subspace of `H`. `V` need not be closed. Assume:

* `V` is invariant under `B` (`hBV : ∀ b ∈ B, ∀ v ∈ V, b v ∈ V`);
* `B` acts transitively on `V`: for every nonzero `u ∈ V` and every `w ∈ V` there is
  `b ∈ B` with `b u = w` (`htrans`).

`CommutesOn B V e` says that a `ℂ`-linear endomorphism `e : V →ₗ[ℂ] V` commutes with `B`.
Explicitly, `e w = b (e v)` whenever `v, w ∈ V` and `w = b v`.
`exists_eq_smul_id_of_commutesOn` states that every such `e` is a scalar multiple
`μ • LinearMap.id`.

This is the bounded-operator form of Schur's lemma. No separability or countable-dimension
hypothesis is made, so Dixmier's version of Schur's lemma cannot be used. The completeness
of `H` and the nonemptiness of spectra in a complex Banach algebra do that job instead.

## Provenance

This is an internal helper for the proof of Renard IV.3.2, Remark
(`Langlands.Renard.CompactRepresentation.SingleCoefficientSquareIntegrabilityStatement`).
It establishes the admissibility of an irreducible smooth representation with one nonzero
square-integrable coefficient. The argument is a standard Gelfand–Mazur style
argument. It is not taken from Renard, who leaves the Remark to the reader.

## Lean proof

* `CommutesOn` is closed under `0`, the identity, composition, sums, scalar multiples and
  `e - μ • id`. The lemmas are `CommutesOn.zero`, `.id`, `.comp`, `.add`, `.smul` and
  `.sub_smul_id`.
* `bijective_of_commutesOn`: a nonzero commuting `e` is bijective. If `e v = 0` with
  `v ≠ 0`, then every `w = b v` satisfies `e w = b (e v) = 0`, so `e = 0`. For
  surjectivity, pick `v₀` with `e v₀ ≠ 0`. Given `w`, choose `b` with `b (e v₀) = w`; then
  `e (b v₀) = b (e v₀) = w`.
* `commutantOrbit B V u` is the subspace `{e u | e commutes with B}` of `H`.
* Main theorem. Suppose `d` is not a scalar. Then `d - μ` is a nonzero commuting map for
  every `μ`, hence bijective, and its inverse `f μ` also commutes with `B`. Fix `u ≠ 0`
  in `V`. By transitivity there are `b₀ ∈ B` with `b₀ u = d u` and, for each `μ`,
  `b μ ∈ B` with `b μ u = f μ u`. For a commuting `e`, `b₀ (e u) = e (d u)` and
  `b μ (e u) = e (f μ u)`. Hence `b₀` and every `b μ` map `M = commutantOrbit B V u`
  into itself. On `M` the operators `b₀ - μ` and `b μ` are mutually inverse. By
  continuity this persists on the closure `W` of `M`, which is a nonzero complete space
  since it contains `u`. The restriction `β` of `b₀` to `W`
  (`ContinuousLinearMap.restrict`) therefore has `μ - β` invertible in the complex Banach
  algebra `W →L[ℂ] W` for every `μ`. This means the spectrum of `β` is empty, which
  contradicts `spectrum.nonempty`.

The file imports only Mathlib.
