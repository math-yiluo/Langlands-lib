# Reduction of the complex Langlands quotient statement

Worker 375 wrote this module for task `512e06d6-c86e-472a-b953-50625f03af0d` (Task 6310). That
task's target is the Library's `Langlands.Archimedean.ComplexLanglandsQuotientStatement`
(module `Langlands.Representation.Archimedean.ComplexGenericParameterReduction`). The target
says: every irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module `(ρ, π)` receives a nonzero
intertwining map `A` (`IsComplexStandardIntertwining`) from the `U(n)`-finite functions of
`complexStandardModule n ds`, for some list `ds` of `n` complex characters in the Langlands
order `IsComplexLanglandsOrdered ds`, i.e. `Re t₁ ≥ Re t₂ ≥ ⋯ ≥ Re t_n`. This is the quotient
form of the Langlands classification for `GL_n(ℂ)` (Knapp 1994, Theorem 4 (a)–(b), p. 405, due to
Želobenko and Naimark).

The module states three results, S1, S2 and S3, and one predicate. It proves that S1, S2 and S3
together imply the target. The route is the usual passage from the subrepresentation form to
the quotient form: dualize, embed the dual, and transpose along an invariant pairing.

All declarations are in the namespace `Langlands.Archimedean`. The Lean names
`IsComplexGKModule`, `IsIrreducibleGKModule`, `IsAdmissibleGKModule`, `kFiniteFunctions`,
`complexStandardModule`, `complexPositionCharacter`, `principalSeries`, `unitaryCompact`,
`rightDerivative`, `matrixModel` and `Whittaker.rightTranslation` are the Library's; see
`GKModule.md` and `StandardModule.md`. `IsComplexLanglandsOrdered` and
`IsComplexStandardIntertwining` are defined, and their conventions explained, in
`ComplexGenericParameterReduction.md`. `ComplexCharacterData` (module
`Langlands.LocalFactor.ArchimedeanAttachment`) is a continuous character `z ↦ (z/|z|)^l |z|^{2t}` of
`ℂˣ` with its weight `l` and exponent `t`.

Throughout, `𝔤 = ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)`, and `K = U(n)`. A function `f` in
`principalSeries ℂ n χ` is a smooth function on `GL_n(ℂ)` with
`f(diag(a) u g) = ∏ᵢ χᵢ(aᵢ) |aᵢ|_ℂ^{(n-1)/2 - i} f(g)` for `u` upper unipotent (`i` counted
from `0`, `|z|_ℂ = |z|²`). The extra factor is `δ_B^{1/2}` for the upper triangular Borel
subgroup `B`: the induction is normalized. `GL_n(ℂ)` acts by right translation `R(g)`, and a
matrix `X` acts by the right derivative `R(X) f(g) = d/ds f(g exp(sX))|_{s=0}`.

**Conventions for the two forms.** In this left-equivariant model, the trivial representation
of `GL_2(ℂ)` (the constant functions) lies in `principalSeries` of `χ = δ_B^{-1/2}`, that is of
the exponents `t = (-1/2, 1/2)`. It is a quotient of the principal series of the exponents
`(1/2, -1/2)` (by integration over `K`). So the subrepresentation form of the classification
uses non-decreasing real parts of the exponents, and the quotient form (the target) uses
non-increasing ones. Inverting all characters exchanges the two orders.

## Definition: `IsComplexStandardEmbedding n ρ π ds B`

For a `(𝔤, K)`-module `(ρ, π)` on `V` and a complex-linear map
`B : V →ₗ[ℂ] kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`, the predicate
says:

* for every `k ∈ unitaryCompact ℂ n` and `v ∈ V`, the function `B (ρ(k) v)` equals the right
  translate `R(k) (B v)` (here `k` is read as an element of `Matrix.unitaryGroup` to apply `ρ`);
* for every matrix `X` and `v ∈ V`, the function `B (π(1 ⊗ X) v)` equals
  `rightDerivative (matrixModel ℂ n) X (B v)`.

So `B` is a `(𝔤, K)`-intertwining map *into* the `U(n)`-finite functions. This is the mirror image
of the Library's `IsComplexStandardIntertwining`, which is for maps *out of* them. In the
present direction, the image membership is automatic, so no existence clause is needed. As in
the Library, only the real directions `1 ⊗ X` are imposed; `π` is complex linear on
`ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)`, so they determine all of `π`.

## Statement S1: `ComplexLanglandsSubrepresentationStatement`

For every `n`, every `V : Type uV` with `ρ` and `π`: if `IsComplexGKModule n ρ π`,
`IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, then there are a list `ds` with
`ds.length = n` whose exponents have non-decreasing real parts,
`ds.Pairwise (fun d e => d.exponent.re ≤ e.exponent.re)`, and a nonzero `B` with
`IsComplexStandardEmbedding n ρ π ds B`.

This is the subrepresentation form of the Langlands classification for `GL_n(ℂ)`. Sources:
Wallach 1979 (`wallach-1979-representations-reductive-lie-groups`), the route
Theorem 4.18 (Casselman's subrepresentation theorem), Lemmas 5.13 and 5.15, Theorem 6.7
(Langlands) and 6.9 (classification), pp. 77–80 (PDF 80–83); Knapp 1994
(`knapp-1994-archimedean-llc`), Theorem 4 (a)–(b), p. 405 (PDF 415), the quotient form.

For `GL_n(ℂ)` the minimal parabolic subgroup `P₀` is the upper triangular Borel subgroup `B`.
Wallach's minimal Levi `M₀` (4.2, 4.4, 4.7; p. 76), the centralizer of `A₀`, is the full
diagonal subgroup `(ℂ^×)ⁿ`. Its compact part is `°M₀ = M₀ ∩ U(n) = U(1)ⁿ` (4.4, 4.15), and its
split component is `A₀ = (ℝ_{>0})ⁿ`, the positive real diagonal matrices. An irreducible
representation `σ` of the abelian group `M₀ = °M₀ A₀` is a character. Its restriction to the
compact factor `°M₀` gives the integral angular weights `lᵢ`, and its restriction to `A₀`, the
`A₀`-exponent of 4.16, gives the complex radial exponents `tᵢ`. So `σ` is a list of `n`
characters `z ↦ (z/|z|)^{lᵢ} |z|^{2tᵢ}` of `ℂ^×`, which is exactly what `ComplexCharacterData`
records. Wallach's `V(P₀, σ)` is then a principal series of `n` characters.

Wallach's model (4.7)–(4.8) is
right-equivariant, `f(kp) = δ^{-1/2}(p) σ(p)^{-1} f(k)`, with `G` acting by left translation;
`f ↦ (g ↦ f(g⁻¹))` carries it to the Library's left-equivariant normalized model with the same
`σ`. Wallach's 6.7 gives the classification as the unique irreducible submodule of
`V(P_F, σ)` for exponents in the negative chamber piece `D₀*(F)` of 5.7; for `GL_n(ℂ)` (tempered
representations of the Levi blocks being unitary principal series) this gives an embedding in a
principal series whose exponents satisfy `Re t₁ ≤ ⋯ ≤ Re t_n`. The specialization to `GL_n(ℂ)`
and the change of model are standard derivations, not quotations. S1 is also equivalent to the
target given S2 and S3: the proof below, run in the other direction, turns Knapp's quotient form
into S1.

## Statement S2: `ComplexContragredientStatement`

For every `n`, `V : Type uV`, `ρ` and `π` with `IsComplexGKModule n ρ π`,
`IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`, there are a type `W : Type uV`
(with its additive group and complex module structures), a `(𝔤, K)`-module `(ρ', π')` on `W`
with `IsComplexGKModule n ρ' π'`, `IsIrreducibleGKModule ρ' π'` and `IsAdmissibleGKModule ρ'`,
and a bilinear form `P : W →ₗ[ℂ] V →ₗ[ℂ] ℂ` such that:

1. `P (ρ'(k) w) (ρ(k) v) = P w v` for all `k ∈ U(n)`, `w`, `v`;
2. `P (π'(Y) w) v + P w (π(Y) v) = 0` for all `Y ∈ ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)`, `w`, `v`;
3. `P` separates the points of `V`: if `P w v = 0` for all `w`, then `v = 0`;
4. every linear functional `ℓ` on `W` that is a finite vector
   (`FiniteVectors.IsFiniteVector`, finite-dimensional orbit span) for the dual representation
   `Representation.dual ρ'`, `k ↦ (ℓ ↦ ℓ ∘ ρ'(k⁻¹))`, is `P(·, v)` for some `v ∈ V`.

The intended witness is the `K`-finite contragredient `W = Hom_ℂ(V, ℂ)_K` with
`ρ'(k) w = w ∘ ρ(k⁻¹)`, `π'(Y) w = -w ∘ π(Y)` and `P(w, v) = w(v)`. Knapp–Vogan 1995
(`knapp-vogan-1995-cohomological-induction`), Chapter II, remark after (2.42), p. 118
(PDF 140), defines it and shows it is a `(𝔤, K)`-module. For admissible `V` each `K`-isotypic
component of `W` is the dual of the corresponding finite-dimensional component of `V`. This
gives admissibility, clause 3, clause 4 (`V` is the `K`-finite dual of `W`) and irreducibility
of `W`. These consequences are standard and are not quoted from the source. Proving S2 also
means checking the four clauses of `IsComplexGKModule` for `W`.

## Statement S3: `ComplexStandardDualityStatement`

For every `n` and lists `ds`, `ds'` whose position characters are pointwise inverse,
`complexPositionCharacter ds i z * complexPositionCharacter ds' i z = 1` for all `i : ℕ` and
`z : ℂˣ`, there is a bilinear form
`Q : kFiniteFunctions (complexStandardModule n ds) K →ₗ[ℂ] kFiniteFunctions (complexStandardModule n ds') K →ₗ[ℂ] ℂ`
such that:

1. `Q (R(k) f) (R(k) h) = Q f h` for `k ∈ unitaryCompact ℂ n` (the translates are given with
   their proofs of membership, which the module `PrincipalSeriesStability` supplies);
2. `Q (R(X) f) h + Q f (R(X) h) = 0` for every matrix `X` (again with membership proofs);
3. `Q` is nondegenerate in its second argument: for every `h ≠ 0` some `f` has `Q f h ≠ 0`.

The intended witness is `Q(f, h) = ∫_{U(n)} f(k) h(k) dk`. Since the characters are inverse, the
product `f h` satisfies `(f h)(b g) = δ_B(b) (f h)(g)`, and integration over `K` of such
functions is right `GL_n(ℂ)`-invariant (Iwasawa decomposition `GL_n(ℂ) = B U(n)`); clause 2 is
the derivative of the invariance. For clause 3 take `f(b k) = δ_B^{1/2}(b) χ(b) conj(h(k))`; it
is well defined because the characters are unitary on `B ∩ U(n)`, and `Q(f, h) = ∫ |h|² > 0`.
This is the standard duality of principal series; it is not quoted from a registered source.

The hypothesis is about position characters, so `ds` and `ds'` need not have length `n`.
Positions beyond a list's length carry the character `1` in `complexPositionCharacter`.

## Statement of the reduction

`ComplexLanglandsQuotientReductionStatement` (universe `uV`) is the proposition

  `ComplexLanglandsSubrepresentationStatement → ComplexContragredientStatement →
    ComplexStandardDualityStatement → ComplexLanglandsQuotientStatement`.

## Auxiliary declarations

* `complexCharacterDataInv d` is the inverse character `z ↦ (z/|z|)^{-l} |z|^{-2t}`: character
  `d.character⁻¹`, weight `-d.weight`, exponent `-d.exponent`. The field `character_eq` follows
  from `d.character_eq` by inverting both sides.
* `complexPositionCharacter_map_inv_mul ds i z`: the position characters of
  `ds.map complexCharacterDataInv` and `ds` multiply to `1` at every position, by induction on
  the list (both are `1` beyond the end).

## Proof of the reduction: `complexLanglandsQuotientReduction`

Take an irreducible admissible `(𝔤, K)`-module `(ρ, π)` on `V`.

1. S2 gives `(ρ', π')` on `W` and the pairing `P`.
2. S1 applied to `W` gives `ds'` of length `n` with non-decreasing real parts and a nonzero
   embedding `B` of `W`.
3. Put `ds = ds'.map complexCharacterDataInv`. S3, applied to `ds` and `ds'` with
   `complexPositionCharacter_map_inv_mul ds'`, gives `Q`.
4. Let `Λ = Q.compl₂ B`, so `Λ f w = Q f (B w)`. From the `K`-clause of `B` and clause 1 of
   `Q`: `Λ (R(k) f) (ρ'(k) w) = Λ f w`.
5. Each `Λ f` is a finite vector for `Representation.dual ρ'`. The span `S` of the right
   translates of `f` by `K` is finite-dimensional because `f` is `K`-finite. Its preimage `S'`
   in `kFiniteFunctions` injects into `S`, so it is finite-dimensional, and so is its image
   `Λ(S')`. Each orbit element `Λ f ∘ ρ'(u⁻¹)` (for `u ∈ U(n)`) equals `Λ(R(u) f)` by step 4,
   applied to `k = u⁻¹` and `g = R(u) f`, whose translate `R(u⁻¹) g` is `f`. And
   `R(u) f ∈ S'`. So the orbit span of `Λ f` lies in `Λ(S')`.
6. By clause 3 of S2, `P.flip : V → Dual W` is injective. By clause 4 and step 5, every `Λ f`
   lies in its range. So `A = (P.flip)⁻¹ ∘ Λ` (through `LinearEquiv.ofInjective` and
   `LinearMap.codRestrict`) is a linear map with `P w (A f) = Q f (B w)` for all `f`, `w`.
7. The conclusion: `ds.length = n` by `List.length_map`. `IsComplexLanglandsOrdered ds` holds
   because negating the exponents reverses the order (`List.pairwise_map`). `A ≠ 0`: pick `w`
   with `B w ≠ 0` and, by clause 3 of S3, `f` with `Q f (B w) ≠ 0`; then `P w (A f) ≠ 0`.
8. Both clauses of `IsComplexStandardIntertwining` are proved by separating points with `P`.
   The membership proofs come from `rightTranslation_mem_kFiniteFunctions_complexStandardModule`
   and `rightDerivative_mem_kFiniteFunctions_complexStandardModule` (module
   `PrincipalSeriesStability`). For `k ∈ K`: write `w' = ρ'(k)(ρ'(k⁻¹) w')`; by clause 1 of S2,
   `P w' (ρ(k) (A f)) = P (ρ'(k⁻¹) w') (A f) = Λ f (ρ'(k⁻¹) w')`, which equals
   `Λ (R(k) f) w' = P w' (A (R(k) f))` by step 4. For `X`: by clause 2 of S2,
   `P w (π(1⊗X) (A f)) = -P (π'(1⊗X) w) (A f) = -Q f (B (π'(1⊗X) w)) = -Q f (R(X) (B w))`,
   which equals `Q (R(X) f) (B w) = P w (A (R(X) f))` by clause 2 of S3. The last step is
   `linear_combination`.

## Dependencies and scope

The module imports `Langlands.Representation.Archimedean.ComplexGenericParameterReduction`
(the target and `IsComplexStandardIntertwining`) and
`Langlands.Representation.Archimedean.PrincipalSeriesStability`. The latter is the separate
candidate `0715f927-9d27-4968-bfac-83b2ed2650ca` of the same task; it must be integrated
first. The statements S1–S3 themselves use only Library definitions; the stability module is
used only in the proof of the reduction.

None of S1, S2 or S3 is proved here; each needs its own proof task. Like the target, they are
stated for the Library's algebraic `(𝔤, K)`-modules and its `complexStandardModule`. Their truth
relies on identifying `kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` with
the Harish-Chandra module of the classical principal series. The candidate
`6142a512-db78-4194-aca3-39b471d4e7e6` (module `PrincipalSeriesGKModule`) proves that these
functions form a `(𝔤, K)`-module in the Library's sense.
