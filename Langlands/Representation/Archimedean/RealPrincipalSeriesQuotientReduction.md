# Reduction of Casselman's theorem in quotient form for `GL_n(ℝ)`

Worker 378 wrote this module for Task 6746 (`262dea19-8ca2-4a4d-87d7-f1002ea208d0`). That task's
target is the Library's `Langlands.Archimedean.RealPrincipalSeriesQuotientStatement` (module
`Langlands.Representation.Archimedean.RealLanglandsQuotientReduction`). The target says: every
irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` on a complex vector space `V` receives
a nonzero `(𝔤, K)`-intertwiner `B` (`IsRealStandardIntertwiner n ρ π (cs.map RealBlock.character) B`)
from the `O(n)`-finite functions of the Library's standard module
`realStandardModule n (cs.map RealBlock.character)`, for some list `cs` of `n` real characters.
No order condition is imposed on `cs`.

The module states three results, S1, S2 and S3, and one predicate. It proves that S1, S2 and S3
together imply the target. The route is the usual passage from a subrepresentation statement
to a quotient statement: dualize, embed the dual, and transpose along an invariant pairing. It
is the real counterpart of the Library's `ComplexLanglandsQuotientReduction` (Worker 375, Task
6310). The differences: here there is no order condition, the group is `GL_n(ℝ)` with
`K = O(n)`, and the characters are those of `ℝ^×`.

All declarations are in the namespace `Langlands.Archimedean`. The Lean names
`IsRealGKModule`, `IsIrreducibleGKModule`, `IsAdmissibleGKModule`, `kFiniteFunctions`,
`realStandardModule`, `realPositionCharacter`, `principalSeries`, `unitaryCompact`,
`rightDerivative`, `matrixModel` and `Whittaker.rightTranslation` are the Library's; see
`GKModule.md` and `StandardModule.md`. `IsRealStandardIntertwiner` is defined in
`RealGenericParameterReduction.md`. `RealBlock` and `RealCharacterData` are in
`Langlands.LocalFactor.Archimedean`. A `c : RealCharacterData` is the character
`x ↦ sgn(x)^ε |x|^t` of `ℝ^×`, where `ε = c.parity ∈ {0, 1}` and `t = c.exponent ∈ ℂ`
(`c.character_eq`).

Throughout, `𝔤 = ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ)` and `K = O(n)`. In Lean, `K` appears both as
`Matrix.unitaryGroup (Fin n) ℝ`, which `ρ` is defined on, and as the subgroup
`unitaryCompact ℝ n` of `GL_n(ℝ)`. As explained in `RealLanglandsQuotientReduction.md`,
`realStandardModule n (cs.map RealBlock.character)` imposes no Fourier condition. It is the
smooth principal series `principalSeries ℝ n (realPositionCharacter (cs.map RealBlock.character))`:
the `C^∞` functions `f` on `GL_n(ℝ)` with

`f(diag(a) u g) = ∏ᵢ cᵢ(aᵢ) |aᵢ|^((n-1)/2 - i) f(g)`

for `u` upper unipotent (`i` counted from `0`; `cᵢ` is the `i`-th entry of `cs` for
`i < cs.length` and the trivial character beyond). The extra factor is `δ_B^{1/2}` for the upper
triangular Borel subgroup `B`, so the induction is normalized. `GL_n(ℝ)` acts by right
translation `R(g)`, and a real matrix `X` acts by the right derivative
`R(X) f(g) = d/ds f(g exp(sX))|_{s=0}`.

## Definition: `IsRealStandardEmbedding n ρ π ds B`

Let `(ρ, π)` be a `(𝔤, K)`-module on `V`, `ds : List RealBlock`, and
`B : V →ₗ[ℂ] kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` a complex-linear
map. The predicate says:

* for every `k ∈ unitaryCompact ℝ n` and `v ∈ V`, the function `B (ρ(k) v)` equals the right
  translate `R(k) (B v)` (here `k` is read as an element of `Matrix.unitaryGroup` to apply `ρ`);
* for every real matrix `X` and `v ∈ V`, the function `B (π(1 ⊗ X) v)` equals
  `rightDerivative (matrixModel ℝ n) X (B v)`.

So `B` is a `(𝔤, K)`-intertwining map *into* the `O(n)`-finite functions. This is the mirror
image of the Library's `IsRealStandardIntertwiner`, which is for maps *out of* them. In this
direction the image lies in the space by the typing of `B`, so no existence clause is needed.
As in the Library, only the real directions `1 ⊗ X` are imposed; `π` is complex linear on
`ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ)`, so they determine all of `π`. The predicate is stated for any list of real
blocks; this module uses it only for lists of characters.

## Statement S1: `RealPrincipalSeriesSubrepresentationStatement`

Fix `n`, `V : Type uV`, `ρ` and `π` with `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π`
and `IsAdmissibleGKModule ρ`. Then there are a list `cs : List RealCharacterData` with
`cs.length = n` and a nonzero
`B : V →ₗ[ℂ] kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n)`
with `IsRealStandardEmbedding n ρ π (cs.map RealBlock.character) B`. No order condition is
imposed on `cs`.

This is Casselman's subrepresentation theorem for `GL_n(ℝ)`. Source: Wallach 1979
(`wallach-1979-representations-reductive-lie-groups`), Theorem 4.18, pp. 77–78 (PDF 80–81): an
irreducible admissible `(𝔤, K)`-module is isomorphic to a `(𝔤, K)`-submodule of `V(P₀, ξ)` for
an appropriate irreducible representation `ξ` of `M₀`. Two representations of `M₀` occur in
the construction of 4.16 (p. 77, PDF 80), and they must be kept apart:

- `σ`, an irreducible quotient of the finite-dimensional module `V/𝔫₀V`, on which `M₀` acts;
- `ξ = δ_{P₀}^{-1/2} σ`, the representation that is induced. The map `C(v)(k) = μ(k⁻¹ v)`,
  with `μ : V → H_σ` the quotient map, takes values in `H_{P₀,ξ}`, and Lemma 4.17 makes it a
  `(𝔤, K)`-map into `V(P₀, ξ)`. The proof of 4.18 uses this `C`.

The twist is needed. Heuristically, if `V` came from a representation of `G`, then
`C(v)(g) = μ(g⁻¹ v)` would satisfy `C(v)(kp) = μ(p⁻¹ k⁻¹ v) = σ(p)^{-1} C(v)(k)`, since `N₀`
acts trivially on `V/𝔫₀V`. For this to have the form `δ_{P₀}(p)^{-1/2} ξ(p)^{-1} C(v)(k)` of
4.8, one needs `ξ = δ_{P₀}^{-1/2} σ`. On `°M₀ = K ∩ M₀` the two agree, since `δ_{P₀}` is
trivial there.

For `GL_n(ℝ)`, `𝔞₀` (4.2) is the diagonal subalgebra, and for a suitable choice of `h₀` the
group `N₀` is the upper unipotent subgroup. Then `P₀` is the upper triangular Borel subgroup
`B`. Wallach's `M₀`, the centralizer of `A₀ = exp 𝔞₀`, is the full diagonal subgroup `(ℝ^×)ⁿ`.
It is not compact. Its part `°M₀ = M₀ ∩ K` (4.4, 4.15) is the finite group `{±1}ⁿ` of diagonal
sign matrices. The split component `A₀` is `(ℝ_{>0})ⁿ`, the positive diagonal matrices, and
`M₀ = °M₀ × A₀`. The representation `σ` is finite-dimensional, since `V/𝔫₀V` is. It is irreducible
for the abelian group `M₀`, so it is a character. The modular function `δ_{P₀}` is also a
character of `M₀`, `δ_B(diag(a)) = ∏ᵢ |aᵢ|^{n-1-2i}` (positions `i = 0, …, n-1`). So the inducing
representation `ξ = δ_B^{-1/2} σ` is again a character of `(ℝ^×)ⁿ`, that is a list of `n`
characters `aᵢ ↦ sgn(aᵢ)^{εᵢ} |aᵢ|^{tᵢ}` of `ℝ^×`, which is what a list of `RealCharacterData`
records. The exponents `tᵢ` of `ξ` are those of `σ` shifted by `-(n-1)/2 + i`.

Wallach's model (4.8) of `V(P₀, ξ)` is right-equivariant,
`f(kp) = δ_{P₀}(p)^{-1/2} ξ(p)^{-1} f(k)`, with `G` acting by left translation. The map
`f ↦ f' = (g ↦ f(g⁻¹))` gives `f'(p g) = δ_{P₀}(p)^{1/2} ξ(p) f'(g)`. This is the Library's
left-equivariant normalized model (`principalSeries`, with the factor `δ_B^{1/2}` built in) for
the list of characters `ξ`, and left translation becomes right translation. So `cs` in S1
records `ξ`, not `σ`. The `K`-finite vectors of Wallach's `I(P₀, ξ)` are smooth (4.12), so
`V(P₀, ξ)` corresponds to the `O(n)`-finite functions of `principalSeries`. For example, for
the trivial module of `GL_2(ℝ)`, `σ` is trivial, `ξ = δ_B^{-1/2}` has exponents `-1/2, 1/2`, and
the embedding is by the constant functions.

The specialization to `GL_n(ℝ)` and the change of model are standard derivations, not
quotations. Since S1 quantifies `cs` existentially, the statement is the same whichever
character one records, but the source's inducing character is `ξ`. S1 is also equivalent to
the target given S2 and S3: the proof below, run in the other direction, turns the target into
S1.

## Statement S2: `RealContragredientStatement`

Fix `n`, `V : Type uV`, `ρ` and `π` with `IsRealGKModule n ρ π`, `IsIrreducibleGKModule ρ π`
and `IsAdmissibleGKModule ρ`. Then there are a type `W : Type uV` (with its additive group and
complex module structures), a `(𝔤, K)`-module `(ρ', π')` on `W` with `IsRealGKModule n ρ' π'`,
`IsIrreducibleGKModule ρ' π'` and `IsAdmissibleGKModule ρ'`, and a bilinear form
`P : W →ₗ[ℂ] V →ₗ[ℂ] ℂ` such that:

1. `P (ρ'(k) w) (ρ(k) v) = P w v` for all `k ∈ O(n)`, `w`, `v`;
2. `P (π'(Y) w) v + P w (π(Y) v) = 0` for all `Y ∈ ℂ ⊗[ℝ] 𝔤𝔩_n(ℝ)`, `w`, `v`;
3. `P` separates the points of `V`: if `P w v = 0` for all `w`, then `v = 0`;
4. every linear functional `ℓ` on `W` that is a finite vector
   (`FiniteVectors.IsFiniteVector`, finite-dimensional orbit span) for the dual representation
   `Representation.dual ρ'`, `k ↦ (ℓ ↦ ℓ ∘ ρ'(k⁻¹))`, is `P(·, v)` for some `v ∈ V`.

It is word for word the Library's `ComplexContragredientStatement` with `ℂ` replaced by `ℝ` in
the group (`IsRealGKModule`, `O(n)`, `𝔤𝔩_n(ℝ)`). The intended witness is the `K`-finite
contragredient `W = Hom_ℂ(V, ℂ)_K` with `ρ'(k) w = w ∘ ρ(k⁻¹)`, `π'(Y) w = -w ∘ π(Y)` and
`P(w, v) = w(v)`. Knapp–Vogan 1995 (`knapp-vogan-1995-cohomological-induction`), Chapter II,
remark after (2.42), p. 118 (PDF 140), defines it and shows it is a `(𝔤, K)`-module. For
admissible `V`, each `K`-isotypic component of `W` is the dual of the corresponding
finite-dimensional component of `V`. Admissibility, clause 3, clause 4 (`V` is the `K`-finite
dual of `W`) and irreducibility of `W` follow. These consequences are standard and are not quoted
from the source.

## Statement S3: `RealPrincipalSeriesDualityStatement`

Fix `n` and lists `cs`, `cs' : List RealCharacterData` whose position characters are pointwise
inverse:
`realPositionCharacter (cs.map RealBlock.character) i x * realPositionCharacter (cs'.map RealBlock.character) i x = 1`
for all `i : ℕ` and `x : ℝˣ`. Write `PS(cs)` for
`kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n)`.
Then there is a bilinear form `Q : PS(cs) →ₗ[ℂ] PS(cs') →ₗ[ℂ] ℂ` such that:

1. `Q (R(k) f) (R(k) h) = Q f h` for `k ∈ unitaryCompact ℝ n` (the translates are given with
   their proofs of membership);
2. `Q (R(X) f) h + Q f (R(X) h) = 0` for every real matrix `X` (again with membership proofs);
3. `Q` is nondegenerate in its second argument: for every `h ≠ 0` some `f` has `Q f h ≠ 0`.

The membership proofs that clauses 1 and 2 take as hypotheses always exist. The Library's
`rightTranslation_mem_kFiniteFunctions_realStandardModule` and
`rightDerivative_mem_kFiniteFunctions_realStandardModule` (module `RealStandardModuleGKModule`)
supply them.

The intended witness is `Q(f, h) = ∫_{O(n)} f(k) h(k) dk`. Since the characters are inverse, the
product `f h` satisfies `(f h)(b g) = δ_B(b) (f h)(g)`. Integration over `K` of such functions is
right `GL_n(ℝ)`-invariant (Iwasawa decomposition `GL_n(ℝ) = B O(n)`). Clause 2 is the derivative
of this invariance along `exp(sX)`, using the integral formula on all smooth functions. For
clause 3 take `f(b k) = δ_B^{1/2}(b) χ(b) conj(h(k))`, where `χ` is the character of `cs`. It is
well defined because `B ∩ O(n)` is the group of diagonal sign matrices, on which `χ` takes values
`±1`. Then `f` is `O(n)`-finite with `h`, and `Q(f, h) = ∫ |h|² > 0`. This is the standard duality
of principal series; it is not quoted from a registered source.

The hypothesis is about position characters, so `cs` and `cs'` need not have length `n`.
Positions beyond a list's length carry the character `1` in `realPositionCharacter`. Only lists
of characters are covered: for induction blocks, `realStandardModule` imposes Fourier conditions,
and the statement is not claimed for them.

## Statement of the reduction

`RealPrincipalSeriesQuotientReductionStatement` (universe `uV`) is the proposition

  `RealPrincipalSeriesSubrepresentationStatement → RealContragredientStatement →
    RealPrincipalSeriesDualityStatement → RealPrincipalSeriesQuotientStatement`.

## Auxiliary lemma: `realPositionCharacter_map_inverse_mul cs i x`

For `cs : List RealCharacterData`, the position characters of
`(cs.map RealCharacterData.inverse).map RealBlock.character` and of `cs.map RealBlock.character`
multiply to `1` at every position `i` and every `x : ℝˣ`. Here `RealCharacterData.inverse`
(Library module `Langlands.LocalFactor.ArchimedeanGamma`) is the character `d.character⁻¹` with
the same parity and exponent `-d.exponent`. The proof is by induction on the list. Beyond the
end both characters are `1`. At position `0` the product is `(c x)⁻¹ · c x = 1` in `ℂˣ`.

## Proof of the reduction: `realPrincipalSeriesQuotientReduction`

Take an irreducible admissible `(𝔤, K)`-module `(ρ, π)` on `V`.

1. S2 gives `(ρ', π')` on `W` and the pairing `P`.
2. S1 applied to `W` gives `cs'` of length `n` and a nonzero embedding `B` of `W` into `PS(cs')`.
3. Put `cs = cs'.map RealCharacterData.inverse`. S3, applied to `cs` and `cs'` with
   `realPositionCharacter_map_inverse_mul cs'`, gives `Q`.
4. Let `Λ = Q.compl₂ B`, so `Λ f w = Q f (B w)`. From the `K`-clause of `B` and clause 1 of
   `Q`: `Λ (R(k) f) (ρ'(k) w) = Λ f w`.
5. Each `Λ f` is a finite vector for `Representation.dual ρ'`. The span `S` of the right
   translates of `f` by `K` is finite-dimensional because `f` is `K`-finite. Its preimage `S'`
   in `kFiniteFunctions` injects into `S`, so `S'` and its image `Λ(S')` are
   finite-dimensional. Each orbit element `Λ f ∘ ρ'(u⁻¹)` (for `u ∈ O(n)`) equals `Λ(R(u) f)`,
   by step 4 applied to `k = u⁻¹` and `g = R(u) f`, whose translate `R(u⁻¹) g` is `f`. And
   `R(u) f ∈ S'`. So the orbit span of `Λ f` lies in `Λ(S')`.
6. By clause 3 of S2, `P.flip : V → Dual W` is injective. By clause 4 and step 5, every `Λ f`
   lies in its range. So `A = (P.flip)⁻¹ ∘ Λ` (through `LinearEquiv.ofInjective` and
   `LinearMap.codRestrict`) is a linear map with `P w (A f) = Q f (B w)` for all `f`, `w`.
7. The conclusion: `cs.length = n` by `List.length_map`. `A ≠ 0`: pick `w` with `B w ≠ 0` and,
   by clause 3 of S3, `f` with `Q f (B w) ≠ 0`; then `P w (A f) ≠ 0`.
8. Both clauses of `IsRealStandardIntertwiner` are proved by separating points with `P`.
   `rightTranslation_mem_kFiniteFunctions_realStandardModule` and
   `rightDerivative_mem_kFiniteFunctions_realStandardModule` supply the membership proofs. For
   `k ∈ K`, write `w' = ρ'(k)(ρ'(k⁻¹) w')`. By clause 1 of S2,
   `P w' (ρ(k) (A f)) = P (ρ'(k⁻¹) w') (A f) = Λ f (ρ'(k⁻¹) w')`. By step 4 this equals
   `Λ (R(k) f) w' = P w' (A (R(k) f))`. For `X`, clause 2 of S2 gives
   `P w (π(1⊗X) (A f)) = -P (π'(1⊗X) w) (A f) = -Q f (B (π'(1⊗X) w)) = -Q f (R(X) (B w))`.
   By clause 2 of S3 this equals `Q (R(X) f) (B w) = P w (A (R(X) f))`. The last step is
   `linear_combination`.

## Dependencies and scope

The module imports `Langlands.Representation.Archimedean.RealLanglandsQuotientReduction` (the
target), `Langlands.Representation.Archimedean.RealStandardModuleGKModule` (the two membership
lemmas) and `Langlands.LocalFactor.ArchimedeanGamma` (`RealCharacterData.inverse`). All are in the
Library. The statements S1–S3 use only Library definitions.

None of S1, S2 or S3 is proved here; each needs its own proof. Like the target, they are stated
for the Library's algebraic `(𝔤, K)`-modules and its `realStandardModule`. Their truth relies on
identifying `kFiniteFunctions (realStandardModule n (cs.map RealBlock.character)) (unitaryCompact ℝ n)`
with the Harish-Chandra module of the classical principal series. The Library module
`RealStandardModuleGKModule` proves that these functions form a `(𝔤, K)`-module in the Library's
sense.
