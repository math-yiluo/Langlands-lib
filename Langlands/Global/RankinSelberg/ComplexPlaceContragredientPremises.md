# Premises for the contragredient-parameter reduction at a complex place

Module: `Langlands.Global.RankinSelberg.ComplexPlaceContragredientPremises` (namespace
`Langlands.Global.RankinSelbergGlobal`).

This module states two premises and a reduction statement. It proves none of them.
The reduction is proved in `Langlands.Global.RankinSelberg.ComplexPlaceContragredientReduction`.
The two premises are left open.

The reduction concerns the contragredient premise `ComplexPlaceContragredientParameterStatement`
of `ComplexPlaceFunctionalEquationReductionStatement`, stated in
`Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationReduction`. That premise says the
following. Let `F` be a number field with compact adele quotient, and let `T`, `Td` be actual
cuspidal realizations of `GL_(r+1)` over `F` with `Td` contragredient to `T`
(`Td.realization.IsContragredientOf T.realization`). Let `w` be a complex place. If `T` has the
parameter `d` at `w` and `Td` has the parameter `dd` at `w`, then `dd` is a permutation of
`d.map ComplexCharacterData.inv`, the list of inverse characters.

Throughout, `complexStandardKFinite n ds` is the Library's space of `U(n)`-finite functions in
the complex standard module `complexStandardModule n ds`. This module is the principal series
`principalSeries ℂ n (complexPositionCharacter ds)`: smooth `f` on `GL_n(ℂ)` with
`f(diag(a) u g) = ∏_i χ_i(a_i) |a_i|_ℂ^((n-1)/2 - i) f(g)` for `u` upper unipotent. The
factor `|a_i|_ℂ^((n-1)/2 - i)` is the square root of the modulus character, so this is
normalized induction from the upper triangular Borel subgroup.

## Local objects

- `complexStandardTranslate n ds k f`: right translation of `f ∈ complexStandardKFinite n ds` by
  `k ∈ U(n)` (`unitaryCompact ℂ n`), that is, `g ↦ f(g k)`. The membership proof is the Library
  lemma `rightTranslation_mem_kFiniteFunctions_complexStandardModule`.
- `complexStandardDerivative n ds X f`: the right derivative
  `rightDerivative (matrixModel ℂ n) X f` along a real direction `X ∈ M_n(ℂ) = 𝔤𝔩_n(ℂ)`, that is,
  `g ↦ d/dt f(g exp(tX))` at `t = 0`. The membership proof is
  `rightDerivative_mem_kFiniteFunctions_complexStandardModule`.
  These two operations are the `U(n)`-action and the action of the real Lie algebra
  `𝔤𝔩_n(ℂ)` that make `complexStandardKFinite n ds` a `(𝔤, K)`-module, with `K = U(n)`. They
  are the same operations as in the Library predicate
  `OperatorRealization.HasComplexPlaceParameter`, which (up to the membership proofs) is stated with
  the raw functions `Whittaker.rightTranslation` and `Archimedean.rightDerivative`.
- `IsComplexStandardIrreducible n ds`: `complexStandardKFinite n ds` is nonzero (`Nontrivial`),
  and every `ℂ`-subspace stable under all `complexStandardTranslate n ds k` and all
  `complexStandardDerivative n ds X` is `⊥` or `⊤`. A complex subspace stable under the real
  directions is stable under the complexified Lie algebra. So this is irreducibility of the
  standard module as a `(𝔤, K)`-module, for `GL_n(ℂ)` viewed as a real group.
- `IsComplexStandardInvariantPairing n d dd P`: the bilinear form
  `P : complexStandardKFinite n d → complexStandardKFinite n dd → ℂ` is `(𝔤, K)`-invariant:
  `P(k·f, k·f') = P(f, f')` for every `k ∈ U(n)`, and `P(X·f, f') + P(f, X·f') = 0` for every
  `X ∈ 𝔤𝔩_n(ℂ)`.

## The premises

### `ComplexPlaceParameterIrreducibleStatement` (global premise G)

For every number field `F` with compact adele quotient, every `r`, every actual cuspidal
realization `T` of `GL_(r+1)` over `F`, every complex place `w` and every list `d` of complex
characters: if `T.realization.HasComplexPlaceParameter w d`, then
`IsComplexStandardIrreducible (r + 1) d`.

The parameter hypothesis gives an injective linear map from `complexStandardKFinite (r+1) d`
into the space of `T` that intertwines right translation by `U(r+1)` and the right derivatives with
the compact and Lie actions of `T` at `w`.

Why it is true (standard theory, not proved here). The Library's automorphic forms are
`K_∞`-finite (`IsAutomorphicForm` includes `IsInfiniteFinite` for the standard infinite compact
group). So the space of the irreducible cuspidal `T` is an irreducible admissible
`(𝔤_∞, K_∞) × GL_(r+1)(𝔸_f)`-module; admissibility of cusp forms is due to Harish-Chandra. By
the tensor product theorem (Flath; see Borel–Jacquet 1979, §4) it is a restricted tensor product
`⊗'_v π_v`. As a `(𝔤_w, K_w)`-module it is therefore a direct sum of copies of the irreducible
`π_w`. The image of the parameter map is a submodule, so the standard module of `d` is isomorphic
to a direct sum of copies of `π_w`. The principal series of `GL_(r+1)(ℂ)` contains its minimal
`U(r+1)`-type with multiplicity one (Zhelobenko's theory of principal series of complex groups;
see Knapp 1986). So there is exactly one copy, and the standard module is isomorphic to `π_w`,
hence irreducible.

### `ComplexStandardPairingParameterStatement` (local premise L)

For every `n` and all lists `d`, `dd` of complex characters of length `n`: if
`IsComplexStandardIrreducible n d` and `IsComplexStandardIrreducible n dd`, and some bilinear form
`P` with `IsComplexStandardInvariantPairing n d dd P` is nonzero, then
`dd.Perm (d.map ComplexCharacterData.inv)`.

Why it is true (standard theory, not proved here). Write `I(d)` for the `U(n)`-finite standard
module.

1. The left and right kernels of `P` are submodules. Since `P ≠ 0` and both modules are
   irreducible, both kernels are zero.
2. `f' ↦ P(·, f')` is then an injective `(𝔤, K)`-map from `I(dd)` into the `K`-finite dual of
   `I(d)`. Its image is `K`-finite because `P(·, k f') = k·P(·, f')`.
3. Because the induction is normalized, `(f, f') ↦ ∫_{U(n)} f(k) f'(k) dk` is a nondegenerate
   invariant pairing of `I(d)` and `I(d⁻¹)`. So the `K`-finite dual of `I(d)` is `I(d⁻¹)`. This
   is the description of the contragredient of an induced representation; see Knapp 1986. It
   is irreducible because `I(d)` is.
4. So `I(dd) ≅ I(d⁻¹)` are isomorphic irreducible principal series of `GL_n(ℂ)`. By Zhelobenko's
   classification (see Knapp 1986, and Vogan 1986 for `GL(n)`), two irreducible principal series
   of a complex group are isomorphic only if their inducing characters are conjugate under the
   Weyl group `S_n`. So `dd` is a permutation of `d⁻¹`.
5. A `ComplexCharacterData` is determined by its character: the weight is the restriction to the
   unit circle and the exponent is read off on positive reals. So a permutation of the
   characters is a permutation of the data.

### `ComplexPlaceContragredientParameterReductionStatement`

`ComplexPlaceParameterIrreducibleStatement.{u} → ComplexStandardPairingParameterStatement →
ComplexPlaceContragredientParameterStatement.{u}`: premises G and L imply the contragredient
premise. The reduction module proves this (`complexPlaceContragredientParameterReduction`). Its
proof builds, from the contragredient pairing of `T` and `Td`, a nonzero invariant pairing of the
two standard modules. Then L applies, with irreducibility from G for both `T` and `Td`.

## Provenance and status

All definitions and statements here are internal. They split
`ComplexPlaceContragredientParameterStatement` into a global and a local input.

- The local objects follow the Library's definitions of the complex standard module and of
  `HasComplexPlaceParameter`.
- G and L are standard facts. They are recorded as open premises, not as claims proved in the
  Library.
- The fact that the contragredient of a generic irreducible representation has the inverse
  Langlands parameter is used in Jacquet 2009 (H. Jacquet, *Archimedean Rankin-Selberg
  integrals*, Contemp. Math. 489, 2009, §2). This is where the target's functional equation with
  the contragredient comes from.
- Sources for the arguments above:
  - Borel–Jacquet 1979 (Corvallis), for admissibility and the tensor product theorem.
  - A. W. Knapp, *Representation Theory of Semisimple Groups* (1986), and D. Vogan, *The unitary
    dual of GL(n) over an archimedean field* (1986), for principal series of complex groups.
  - D. P. Zhelobenko's classification of irreducible representations of complex semisimple
    groups (1974). This original is not in the project literature.

  The retained copy of Knapp 1986 has no text layer. The citations above are to the subject
  matter, not to theorem numbers.
