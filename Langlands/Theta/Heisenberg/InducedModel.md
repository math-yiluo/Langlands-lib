# The induced model of the Heisenberg representation over a nonarchimedean local field

**GKT §1.2.1** (the induced model `Ind_{H(A)}^{H(W)} ψ_A` of a self-dual subgroup `A`, Definition
1.6, p. 20; Corollary 1.4, p. 19; Corollary 1.10, p. 22; Proposition 1.12, p. 23, irreducibility;
the realization on functions on `W`, p. 29).

The module `Langlands.Theta.Heisenberg.InducedModel` constructs, for a non-degenerate alternating
form `B` on a finite-dimensional space `W` over a nonarchimedean local field `F` with `2 ≠ 0`
and a continuous non-trivial character `ψ` of `F`, a smooth irreducible representation of
`HeisenbergGroup B` with central character `ψ`: the induced model of an open self-dual subgroup.
It also provides the tools with which `Langlands.Theta.Heisenberg.StoneVonNeumann` proves that this
representation is unique, and with which the Schrödinger model is shown to be smooth and
irreducible.

## Content

**Self-dual data.** With the orthogonal `charOrthogonal B ψ T` of a set `T` for the pairing
`ψ ∘ B` (`Langlands.Theta.Heisenberg.SelfDual`), a `SelfDualDatum B ψ` consists of a subgroup
`A = subgroup` of `W` and a function `α = character : W → ℂ` (the extension `ψ_A` of GKT
Corollary 1.4, on `A`) such that

- `α` does not vanish on `A` and `α(a) α(b) = ψ(½ B(a, b)) α(a + b)` on `A`;
- `charOrthogonal B ψ A ⊆ A` (with the inclusion `A ⊆ charOrthogonal B ψ A`, which follows from
  the splitting, `A` is its own orthogonal);
- near `0`, the points are in `A` and `α = 1` (so `A` is open);
- every neighbourhood of `0` contains `charOrthogonal B ψ T` for a set `T` with
  `A / charOrthogonal B ψ T` finite.

`nonempty_selfDualDatum`: such data exist when `B` is non-degenerate and `ψ` continuous and
non-trivial. Choose a basis `b` of `W` and its `B`-dual basis; for `s ∈ F` let
`T(s) = {(s o) b_i : o ∈ 𝒪, i}`. The orthogonals of the `T(s)` are neighbourhoods of `0`
(continuity of `ψ`, compactness of `𝒪`), contained in dilates of the compact "cube" of the dual
basis (non-triviality of `ψ`); for a small `r` the pairing `ψ(½ B)` is trivial on the orthogonal
`L` of `T(t₀ / r)`. A maximal self-orthogonal subgroup `A ⊇ L` (Zorn) is then contained in a
compact set, hence finite modulo every open subgroup, and the cocycle is split on `A` by an `α`
equal to `1` on `L` (injectivity of `ℂˣ`).

**Eigenvectors and irreducibility.** Fix a datum `D`. For a representation `π` with central
character `ψ`, the elements `(x, 0)` act by a projective representation of `W` with cocycle
`ψ(½ B)` (`isProjectiveRep_of_hasCentralCharacter`).

- `eventually_apply_ofVec_eq_self`, `isSmooth_of_eventually`: `π` is smooth if and only if every
  vector is fixed by the `(u, 0)` with `u` near `0` (with continuous `ψ`, which is `1` near `0`).
- `SelfDualDatum.exists_eigenvector_mem`: every non-zero subrepresentation of a smooth `π`
  contains a non-zero `α`-eigenvector of `A` (`π(a, 0) e = α(a) e` for `a ∈ A`).
- `translatesSpan hπ e`: the span of the translates `π(x, 0) e`, a subrepresentation.
- `SelfDualDatum.isSmooth_of_span_eq_top`, `SelfDualDatum.isIrreducible_of_span_eq_top`,
  `SelfDualDatum.isSmooth_translatesSpan`, `SelfDualDatum.isIrreducible_translatesSpan`: the
  span of the translates of a non-zero `α`-eigenvector `e` is smooth and irreducible. A non-zero
  subrepresentation contains an `α`-eigenvector, which is a multiple of `e`, and so contains the
  whole span.

**The induced model.** `inducedModel D` is `translatesSpan` of `characterVector D = α · 1_A` in
`regular B ψ`: the induced model `Ind_{H(A)}^{H(W)} ψ_A` realized on functions on `W`. It contains
`α · 1_A ≠ 0`, has central character `ψ` (`hasCentralCharacter_inducedModel`), and is smooth and
irreducible (`isSmooth_inducedModel`, `isIrreducible_inducedModel`; GKT Proposition 1.12):
`α · 1_A` is an `α`-eigenvector of `A` (`SelfDualDatum.regularFun_characterVector`). The proof of
irreducibility is not the book's (which uses Lemma 1.11 and the Fourier transform on `A`); it is
the eigenvector argument above.

**Closed self-dual subgroups.** An `InducingDatum B ψ` is a closed subgroup `A = subgroup` of
`W` with `charOrthogonal B ψ A = A` and a function `ψ_A = character` splitting the cocycle
`ψ(½ B)` on `A` (GKT Lemma 1.2, the definition of self-dual and Corollary 1.4, p. 19; no
continuity of `ψ_A` is required). Its induced model (Definition 1.6, p. 20) is realized on functions
on `W` as on p. 29:

- `InducingDatum.inducedSubmodule D`: the functions `f` with
  `f(a + w) = ψ_A(a) ψ(½ B(w, a)) f(w)` for `a ∈ A`, locally constant, and vanishing off `A + K`
  for a compact `K` (compactly supported modulo `A`, Corollary 1.10). The equivariance is the first
  display of p. 29 (the restriction of `f` with `f(k h) = ψ_A(k) f(h)` to `W`, by (1.1)).
- `InducingDatum.inducedSpace D hB hψ hBc : Subrepresentation (regular B ψ)` for alternating `B`,
  locally constant `ψ` and continuous `z ↦ B(z, v)`: the space is stable under the right
  translations `regularFun B ψ v` (`InducingDatum.regularFun_mem`; the phases combine because
  `B(a, v) + B(v, a) = 0`); `hasCentralCharacter_inducedSpace`.
- `SelfDualDatum.toInducingDatum hB D`: an open self-dual datum is a closed one (an open subgroup is
  closed; `A ⊆ A^⊥` follows from the splitting, `SelfDualDatum.le_charOrthogonal`), and
  `SelfDualDatum.inducedModel_le_inducedSubmodule`: the span of the translates of `α · 1_A` lies in
  the induced space of the closed datum (`characterVector_mem_inducedSubmodule`).

For a Lagrangian subspace the induced space is the Schrödinger model
(`Langlands.Theta.Heisenberg.SchrodingerInduced`, GKT Theorem 1.13), hence smooth and irreducible;
irreducibility (Proposition 1.12) and the equality with `inducedModel` (Lemma 1.11) for an
arbitrary closed self-dual subgroup are not formalized.

The construction is that of Mœglin–Vignéras–Waldspurger, *Correspondances de Howe sur un corps
p-adique* (Lecture Notes in Math. 1291, Springer 1987), chapter 2, I.3, pp. 28–30, which allows any
closed subgroup `A = A^⊥` of `W`; self-dual lattices are their example I.4 (2), p. 30. Here `A` is a
self-orthogonal subgroup with the stated properties.

## Source and licence

This file and `Langlands.Theta.Heisenberg.SelfDual` hold the text of lines 357–541 and 555–646 of
`src/Development/AbelianVarietyTheory/PublishedTheorems/GlobalTheta/PlaneFormNondegenerate.lean`
of <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65` (section
`Local`: `finite_quot`, `isCompact_int`, `exists_ne_zero`, `eventually_psi`, `eventually_psi'`,
`alt_psi`, `psi_sq`, `exists_data`; section `Group`: `ops_of_central`, `funRep`, `eventually_fix`,
`isSmooth_of_eventually`, `exists_eigen_mem`, `irr_of_span`, `exists_irr_sub`; `funRep`, `alt_psi`,
`psi_sq` and `ops_of_central` are in `SelfDual`). The repository has
no licence file; the text is used with attribution, see
`licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.Published.SvN` → `Langlands.HeisenbergGroup`; `(2 : F) ≠ 0` and `/ 2`
  → `[Invertible (2 : F)]` and `⅟2 *`.
- Smoothness is the Library's `Langlands.IsSmooth` (an open subgroup fixes each vector) in place
  of the source's `PRep.IsSmooth` (open stabilizers, `Definitions/Foundations/SmoothPartStable.lean`,
  line 73). The source's `eq_one_of_pow_near` (a wrapper of `EqOneOfPowClose.eq_one_of_pow_close`)
  is replaced by the Library's `Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt`, which has
  the same statement.
- The five outputs of `exists_data` are bundled in the structure `SelfDualDatum`, stated through
  `charOrthogonal B ψ T` in place of the orthogonal for the internal bicharacter (`alt_psi hB ψ`),
  which coincides with it (`orthogonal_psi_eq`); the fifth output (`ψ(B(u, w)/2)² = 1` near `0`) is
  the lemma `eventually_psi_apply_eq_one`. `exists_data` → `nonempty_selfDualDatum`.
- `exists_irr_sub` is split into the definition `translatesSpan` and the theorems
  `SelfDualDatum.isSmooth_translatesSpan`, `SelfDualDatum.isIrreducible_translatesSpan`;
  `irr_of_span` into `isSmooth_of_span_eq_top` and `isIrreducible_of_span_eq_top`. The source's
  `IsIrrSmoothOf` is dissolved into `IsSmooth`, `Representation.IsIrreducible` and
  `HasCentralCharacter`.
- `characterVector`, `inducedModel` and its four lemmas are new (the source applied
  `exists_irr_sub` to `funRep` in the proof of its theorem).
- `Heisenberg.isTopologicalGroup` (lines 543–554) is in `Theta/Heisenberg/Basic`; `apply_eq`
  (523–526) is `HasCentralCharacter.apply_eq` in `Theta/Heisenberg/Representation`.
- Universes of `F`, `W` and the representation spaces are arbitrary (the source: `Type`).
- The section on closed self-dual subgroups (`InducingDatum` and what follows it) is new.

## Declarations

- `SelfDualDatum` (structure; fields `subgroup`, `character`, `character_ne_zero`,
  `character_mul`, `charOrthogonal_le`, `eventually_mem`, `exists_finite`),
  `SelfDualDatum.splitsOn`, `SelfDualDatum.characterVector`, `SelfDualDatum.characterVector_ne_zero`,
  `SelfDualDatum.regularFun_characterVector`.
- `eventually_psi_apply_eq_one`, `nonempty_selfDualDatum`.
- `translatesSpan`, `mem_translatesSpan`, `hasCentralCharacter_translatesSpan`,
  `span_translatesSpan_eq_top`.
- `eventually_apply_ofVec_eq_self`, `isSmooth_of_eventually`.
- `SelfDualDatum.exists_eigenvector_mem`, `SelfDualDatum.isSmooth_of_span_eq_top`,
  `SelfDualDatum.isIrreducible_of_span_eq_top`, `SelfDualDatum.isSmooth_translatesSpan`,
  `SelfDualDatum.isIrreducible_translatesSpan`.
- `inducedModel`, `characterVector_mem_inducedModel`, `hasCentralCharacter_inducedModel`,
  `isSmooth_inducedModel`, `isIrreducible_inducedModel`.
- `InducingDatum` (structure; fields `subgroup`, `isClosed`, `charOrthogonal_eq`, `character`,
  `character_ne_zero`, `character_mul`), `InducingDatum.inducedSubmodule`,
  `InducingDatum.mem_inducedSubmodule`, `InducingDatum.regularFun_mem`,
  `InducingDatum.inducedSpace`, `InducingDatum.hasCentralCharacter_inducedSpace`.
- `SelfDualDatum.isOpen_subgroup`, `SelfDualDatum.le_charOrthogonal`,
  `SelfDualDatum.toInducingDatum`, `SelfDualDatum.toInducingDatum_subgroup`,
  `SelfDualDatum.toInducingDatum_character`, `SelfDualDatum.characterVector_mem_inducedSubmodule`,
  `SelfDualDatum.inducedModel_le_inducedSubmodule`.
- Deprecated aliases (since 2026-11-23): `PolarizingDatum` and its fields and lemmas (`splitting`
  for `character`, `latticeVector…` for `characterVector…`), `latticeModel`,
  `latticeVector_mem_latticeModel`, `hasCentralCharacter_latticeModel`, `isSmooth_latticeModel`,
  `isIrreducible_latticeModel`, `nonempty_polarizingDatum`.

## Dependencies

`Langlands.Theta.Heisenberg.SelfDual`, `Langlands.HarmonicAnalysis.AdditiveCharacterExists`,
`Langlands.Representation.Smooth.Definitions` (`IsSmooth`); through `AdditiveCharacterExists`,
`Langlands.Representation.Twist.ContinuousCharacterProof`
(`complex_eq_one_of_forall_norm_pow_sub_one_lt`). Mathlib: `NumberTheory.LocalField.Basic`,
`RepresentationTheory.Irreducible`, `Topology.Algebra.OpenSubgroup`.
