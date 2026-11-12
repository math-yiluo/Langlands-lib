# Archimedean Langlands parameters of actual automorphic realizations

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.Automorphic`. The module attaches the archimedean blocks of Worker 35's published
standard modules (`Langlands.Representation.Archimedean.StandardModule`) to the archimedean
components of actual automorphic operator realizations. These are Worker 2's
`OperatorRealization F n` and the actual cuspidal classes built on them, at a real or complex
infinite place `v`. The attachment is a property, with no choice of parameter. It does not
assert that a parameter exists or is unique.

## Setting

`F : Type u` is a number field and `n` a natural rank. `S : OperatorRealization F n` is an actual
realization on `S.Space`. At an infinite place `v` the published place actions give
`S.Space` the structure of a `(𝔤_v, K_v)`-module:

- at a real place `v`, `S.realPlaceCompactRepresentation v` of the orthogonal group
  `Matrix.unitaryGroup (Fin n) ℝ = O(n)`, and the complex Lie action
  `S.realPlaceLieAction v` of `ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ)`;
- at a complex place `v`, `S.complexPlaceCompactRepresentation v` of `U(n)` and
  `S.complexPlaceLieAction v` of `ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)`, where `𝔤𝔩_n(ℂ)` is viewed as a real Lie algebra.

These actions are the restrictions of the global compact translation and of the global
differential action. The differential of a real direction `X` is the derivative of
`t ↦ f(g · exp(tX))` at the place, as in the published `ArchimedeanEnvelopingAction`. The
identification of `F_v` with `ℝ` or `ℂ` is the representative-embedding convention of the
published place coordinates.

On the local side, Worker 35's module gives, for a list `ds` of the Library's archimedean
blocks (`RealBlock` over `ℝ`, `ComplexCharacterData` over `ℂ`), the standard module
`realStandardModule n ds` or `complexStandardModule n ds`. This is a space of smooth functions on
`GL_n(ℝ)` or `GL_n(ℂ)` in a principal series. On it `K` acts by right translation and the real Lie
algebra by `Archimedean.rightDerivative`.

## Declarations

- `realStandardKFinite n ds` and `complexStandardKFinite n ds` are the `K`-finite functions of
  these standard modules (`Archimedean.kFiniteFunctions` for `K = O(n)` or `U(n)`), that is,
  their `(𝔤, K)`-modules.
- `OperatorRealization.HasRealPlaceParameter S v ds`, for a real place
  `v : {v // v.IsReal}` and `ds : List RealBlock`, holds when:
  1. `realRank ds = n`;
  2. there is an injective complex linear map `A : realStandardKFinite n ds → S.Space` such
     that for every `k ∈ O(n)` and every `K`-finite function `f`, the right translate `R(k)f` is
     again in `realStandardKFinite n ds` and
     `A(R(k)f) = S.realPlaceCompactRepresentation v k (A f)`;
  3. for every `X ∈ 𝔤𝔩_n(ℝ)` and every `f`, the right derivative of `f` along `X` is again in
     `realStandardKFinite n ds` and `A(R(X)f) = S.realPlaceLieAction v (1 ⊗ X) (A f)`.

  The membership conditions are bundled as `∃ hf`, as in Worker 35's
  `IsInfinitesimallyEquivalent`.
- `OperatorRealization.HasComplexPlaceParameter S v ds`, for a complex place and
  `ds : List ComplexCharacterData`, is the same with `ds.length = n`, `U(n)`, the complex
  standard module and real directions `X ∈ 𝔤𝔩_n(ℂ)`.
- `equivalence_realPlaceCompact`, `equivalence_complexPlaceCompact`,
  `equivalence_realPlaceLie` and `equivalence_complexPlaceLie`: a full equivalence of
  realizations carries each place action. These are the published place restrictions of
  intertwiners.
- `HasRealPlaceParameter.of_equiv` and `HasComplexPlaceParameter.of_equiv`: the properties are
  transported along full equivalences, by composing `A` with the equivalence.
- `OperatorRealization.IsoClass.HasRealPlaceParameter` and `HasComplexPlaceParameter` are the
  descended properties of isomorphism classes (`isoClass_hasRealPlaceParameter`,
  `isoClass_hasComplexPlaceParameter`).
- `CuspidalOperatorRealization.IsoClass.HasRealPlaceParameter` and `HasComplexPlaceParameter`,
  for an actual cuspidal class of `GL_{r+1}` under `[CompactSpace (AdeleQuotient F)]`, are the
  properties of its operator class, with the corresponding `isoClass_…` lemmas.

## Source correspondence

- A. W. Knapp, *Local Langlands correspondence: the archimedean case*, in *Motives*, Proc.
  Sympos. Pure Math. 55, Part 2 (1994), 393–410, literature ID `knapp-1994-archimedean-llc`,
  SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`. The PDF page is
  the printed page plus ten.
  - Printed p.399 (PDF p.409): admissible representations, `K = O(n)`, the `(𝔤, K)`-module
    `V_K` of `K`-finite vectors, infinitesimal equivalence as isomorphism of `(𝔤, K)`-modules,
    and Harish-Chandra's correspondence between closed invariant subspaces and
    `(𝔤, K)`-submodules.
  - Printed p.400 (PDF p.410): the building blocks (2.2), the standard representations
    `I(σ_1, …, σ_r)` (2.4), and Theorem 1. Under the ordering (2.5), `I` has a unique
    irreducible quotient `J`. These exhaust the irreducible admissible representations, and
    they are determined by the blocks up to permutation.
  - Printed p.403 (PDF p.413): Theorem 2, the correspondence (3.4)–(3.5) with semisimple
    representations of `W_ℝ`. Theorems 4–5 on pp.405–406 treat `GL_n(ℂ)`.
- D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math.
  33, Part 1 (1979), 179–183, literature ID `flath-1979-tensor-products`, SHA256
  `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`, §3, printed pp.181–182
  (PDF pp.177–178). Every admissible irreducible representation of `G(𝔸)` factors as a
  restricted tensor product, uniquely up to equivalence, with admissible `(𝔤_v, K_v)`-modules at
  the archimedean places.

### Derived formulation

1. **Local component through the place action.** There is no separate local carrier for the
   archimedean factor `π_v`. If `S` is irreducible, Flath's Theorem 3 gives
   `S ≅ π_v ⊗ (⊗_{w ≠ v} π_w)`. So as a `(𝔤_v, K_v)`-module, `S` is a direct sum of copies of
   `π_v`. For an irreducible `(𝔤, K)`-module `W`, an injective equivariant map `W → S` therefore
   exists exactly when `W ≅ π_v`. The predicate states the existence of such a map from the
   standard module, and needs neither the factorization nor a choice of factor. The
   factorization theorem is used only in this explanation, and is not proved or assumed.
2. **Generic components and parameters.** If `π_v` is generic, its standard module is
   irreducible: Vogan's theorem, as recorded in Worker 35's `StandardModule.md`. The predicate
   then says that `π_v` is infinitesimally equivalent to the standard module of `ds`. By
   Knapp's Theorems 1–2 (resp. 4–5), this means that the Langlands parameter of `π_v` is the sum
   of the Weil representations of the blocks, in any order. This is exactly the meaning of
   Worker 35's `HasRealParameter` and `HasComplexParameter` for Banach representations, now
   for the `(𝔤_v, K_v)`-module of an automorphic realization. Archimedean components of cuspidal
   representations are generic, by the global Whittaker model. That is the intended use, and it
   is not proved here.
3. **Non-generic components.** For non-generic `π_v`, the standard module is reducible and
   indecomposable. It then has no injective equivariant map into a `π_v`-isotypic module, so
   the predicate fails, exactly as Worker 35's predicates fail for non-generic
   representations. No parameter is attached to such components.
4. **Injectivity instead of isomorphism.** Worker 35 compares a representation with the
   standard module by a linear isomorphism of `(𝔤, K)`-modules. The automorphic carrier is a
   global space, so the comparison is an injective equivariant map into it.

## Scope and remaining obligations

The module does not prove:

- existence of parameters for actual cuspidal classes at every infinite place (archimedean
  local Langlands for generic components, with the factorization and genericity of cuspidal
  components);
- uniqueness of the parameter up to permutation of blocks (Knapp's Theorem 1(c));
- any relation to Weil-side archimedean components or to local factors.

Pair `L`- and `ε`-factors of parameters are separate constructions.
