# Annihilating vectors for proper `U(n)`-stable subspaces of complex principal series

Lean module: `Langlands.Representation.Archimedean.ComplexPrincipalSeriesAnnihilator`.

This module was written for the proof of `ComplexStandardLanglandsQuotientStatement`. It is the
complex counterpart of the concrete part of the Library module `PrincipalSeriesAnnihilator` (for
`GL_n(ℝ)`), whose abstract theorem it uses, followed by one extra step through the Library's
partner construction of `ComplexDuality.GramWeight`.

Let `W` be a subspace of the `U(n)`-finite functions of a principal series of `GL_n(ℂ)`, stable
under right translation by `U(n)`, and suppose `W` is not all of that space. The module produces
a `U(n)`-finite function `u` of the principal series of the inverse characters, not identically
zero on `U(n)`, that annihilates `W` in the integration pairing `∫_{U(n)} w u`. The statement is
`Langlands.Archimedean.ComplexStandardAnnihilatorStatement`, proved as
`Langlands.Archimedean.complexStandardAnnihilator`. In the proof of
`ComplexStandardLanglandsQuotientStatement` the set of such `u` is the nonzero `(𝔤, K)`-submodule
of the dual standard module that the Langlands lemma is applied to.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ` and `U(n)` is the subgroup
`unitaryCompact ℂ n`. `principalSeries ℂ n χ`, `complexStandardModule`, `kFiniteFunctions` and
`Whittaker.rightTranslation` (`(R(k) f)(x) = f(x k)`) are the Library's.
`ComplexDuality.unitaryHaar n` is the Library's Haar probability measure on `U(n)` for its Borel
σ-algebra. `complexCharacterDataInv` (Library, `ComplexLanglandsQuotientReduction`) inverts a
complex character: `d ↦ d.character⁻¹`, weight `-d.weight`, exponent `-d.exponent`. Declarations
without a prefix are in the namespace `Langlands.Archimedean.ComplexPrincipalSeriesAnnihilator`.

## The statement

`ComplexStandardAnnihilatorStatement`: let `n` be a natural number, `ds` a list of complex
characters, `W` a submodule of the functions on `GL_n(ℂ)` and `f` a function on `GL_n(ℂ)`, with

* `W ≤ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`;
* `R(k) w ∈ W` for every `k ∈ U(n)` and `w ∈ W`;
* `f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` and `f ∉ W`.

Then there is
`u ∈ kFiniteFunctions (complexStandardModule n (ds.map complexCharacterDataInv)) (unitaryCompact ℂ n)`
with `u(k) ≠ 0` for some `k ∈ U(n)` and `∫_{U(n)} w(k) u(k) d(unitaryHaar n)(k) = 0` for every
`w ∈ W`.

No condition on `ds` is needed, and only stability under `U(n)` is assumed, not under the Lie
algebra.

Provenance. Derived, internal infrastructure without a literature source. The underlying facts
are standard for admissible representations of compact groups: finite-dimensional unitary
representations are completely reducible and every finite-dimensional representation occurs with
finite multiplicity in a principal series. The proof is self-contained.

## Definitions

* `KFin n χ`: the `U(n)`-finite functions of the principal series of `χ`, as a type synonym of the
  submodule, with the `L²(U(n))` inner product `⟪x, y⟫ = ∫ conj(x(k)) y(k) d(unitaryHaar n)(k)`
  (`l2Inner`; instances built with `InnerProductSpace.ofCore`). It is positive definite because a
  principal-series function vanishing on `U(n)` vanishes (Library
  `ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`, through the Iwasawa decomposition) and
  Haar measure charges every nonempty open set.
* `rho`: right translation by `U(n)` on `KFin n χ`, an isometric representation (`rho_isometry`,
  right invariance of `unitaryHaar n`).

## Proof

1. **Abstract orthogonal vectors** (Library `PrincipalSeriesAnnihilator.exists_ne_zero_inner_eq_zero`):
   in a unitary representation in which every vector generates a finite-dimensional stable
   subspace and every finite-dimensional stable subspace has a finite-dimensional space of
   equivariant maps into the space, every proper stable subspace has a nonzero orthogonal vector.
2. **The hypotheses for `KFin n χ`.** Orbits are finite-dimensional because the functions are
   `U(n)`-finite (`finiteDimensional_orbit`). An equivariant map `T` from a finite-dimensional
   stable `F` is determined by the functional `x ↦ (T x)(1)` on `F`, since
   `(T x)(k) = (T(ρ(k) x))(1)` and a principal-series function vanishing on `U(n)` is `0`
   (`finiteDimensional_equivariantMaps`). So step 1 gives `exists_ne_zero_inner_eq_zero_kfin` and,
   back on functions, `exists_orthogonal`: some `v` in the principal series of `χ`, nonzero on
   `U(n)`, with `∫ w conj(v) = 0` for all `w ∈ W`.
3. **Partner** (`exists_dual_annihilator`). Let `χ'` be inverse to `χ` (`χ'ᵢ χᵢ = 1`) with
   `|χ'ᵢ(z)|² = |z|^(2 sᵢ)`. The Library's `ComplexDuality.partner s v = ψ_s · conj v` lies in the
   `U(n)`-finite principal series of `χ'` (`partner_mem_principalSeries`,
   `partner_mem_kFiniteVectors`), and equals `conj v` on `U(n)` because the Gram weight `ψ_s` is
   `1` there (`gramWeight_unitary`). Hence `u = partner s v` is nonzero on `U(n)` and
   `∫ w u = ∫ w conj(v) = 0` for all `w ∈ W`.
4. **Standard modules** (`complexStandardAnnihilator`). For `ds` the position characters of
   `ds.map complexCharacterDataInv` and of `ds` multiply to `1` (Library
   `complexPositionCharacter_map_inv_mul`), and their norms are real powers
   (`ComplexDuality.exists_normSq_complexPositionCharacter`), so step 3 applies.
