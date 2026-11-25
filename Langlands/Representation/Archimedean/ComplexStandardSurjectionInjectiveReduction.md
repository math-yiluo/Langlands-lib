# Reduction of `ComplexStandardSurjectionInjectiveStatement` (V2)

This module was written for the proof of the Library's
`Langlands.Archimedean.ComplexStandardSurjectionInjectiveStatement`
(V2, module `Langlands.Representation.Archimedean.ComplexGenericStandardInjectiveReduction`).
V2 says: let `V` be an irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module that has the
standard-module parameter of some list `ds'` of complex characters, that is, an *injective*
intertwining map `B` from the `U(n)`-finite functions of the standard module of `ds'` into `V`.
Then every *surjective* intertwining map `A` onto `V` from the `U(n)`-finite functions of the
standard module of a list `ds` of `n` characters in the Langlands order is injective.

This module states three results and proves that together they imply V2. Each result needs a
separate proof. All declarations are in the namespace `Langlands.Archimedean`. The Lean names
`IsComplexGKModule`, `IsIrreducibleGKModule`, `IsAdmissibleGKModule`,
`HasComplexStandardParameter`, `kFiniteFunctions`, `complexStandardModule`, `unitaryCompact`,
`complexStandardRep` and `complexStandardLie` are the Library's; see `GKModule.md`,
`StandardModule.md` and `PrincipalSeriesGKModule.md`. `IsComplexLanglandsOrdered` and
`IsComplexStandardIntertwining` are defined, and their conventions explained, in
`ComplexGenericParameterReduction.md`.

Notation. For a list `ds` of `n` complex characters, `X(ds)` is the space
`kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` of `U(n)`-finite functions
of the standard module. `complexStandardRep n ds` is the action of `U(n)` on `X(ds)` by right
translation. `complexStandardLie n ds` is the action of `𝔤 = ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)` on `X(ds)`: it
sends `z ⊗ X` to `z` times the right derivative along `X`. `ComplexGenericParameterReduction.md`
explains why `X(ds)` is the Harish-Chandra module of the principal series `I(σ₁, …, σ_n)` of
Knapp 1994, (4.2). A *`(𝔤, K)`-isomorphism* is a bijective linear map that intertwines both
actions.

A `ComplexCharacterData` value has the fields `character`, `weight`, `exponent` and the
proof `character_eq` that `character z = (z/|z|)^weight |z|^(2·exponent)`. The character
determines the weight and the exponent. So "the list `es` is a permutation of the list `ds`"
(`List.Perm`) means the same as "the characters of `es` are a permutation of those of `ds`".

## Statement LU: `ComplexLanglandsQuotientUniqueStatement` (universe `uV`)

For every `n`, every complex vector space `V : Type uV`, every `ρ`, `π`, every two lists `ds`,
`es` and every two linear maps `A : X(ds) →ₗ[ℂ] V`, `B : X(es) →ₗ[ℂ] V`: if
`IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π`, `IsAdmissibleGKModule ρ`,
`ds.length = n`, `es.length = n`, `IsComplexLanglandsOrdered ds`, `IsComplexLanglandsOrdered es`,
`A ≠ 0`, `IsComplexStandardIntertwining n ρ π ds A`, `B ≠ 0` and
`IsComplexStandardIntertwining n ρ π es B`, then `ds.Perm es`.

Source: Knapp 1994 (`knapp-1994-archimedean-llc`), Theorem 4 (a) and (c), p. 405 (PDF page
415), due to Želobenko and Naimark. With `σⱼ = [·]^{lⱼ} |·|_ℂ^{tⱼ}`: (a) if
`Re t₁ ≥ ⋯ ≥ Re t_n` (4.3), then `I(σ₁, …, σ_n)` has a unique irreducible quotient
`J(σ₁, …, σ_n)`; (c) `J(σ₁, …, σ_n)` and `J(σ'₁, …, σ'_n)` are infinitesimally equivalent if
and only if there is a permutation `j` of `{1, …, n}` with `σ'ᵢ = σ_{j(i)}` for all `i`.
`IsComplexLanglandsOrdered ds` is the condition (4.3) for the exponents of `ds`.

How LU follows from the source. `A` intertwines the `U(n)`-actions and the actions of all
`Y ∈ 𝔤` (`IsComplexStandardIntertwining.map_rep`, `.map_lie` below), so its image is an
invariant subspace of `V`. It is nonzero because `A ≠ 0`, so it is `V` because `V` is
irreducible. Thus `V` is an irreducible quotient of the Harish-Chandra module of `I(ds)`. By (a),
read for Harish-Chandra modules (closed invariant subspaces of an admissible representation
correspond to `(𝔤, K)`-submodules of its `K`-finite vectors), `V` is the Harish-Chandra module
of `J(ds)`. In the same way `V` is that of `J(es)`. By (c), `es` is a permutation of `ds`. The
order hypotheses cannot be dropped: an unordered principal series can have several irreducible
quotients (see the `GL_2(ℂ)` example in `ComplexGenericParameterReduction.md`).

## Statement PI: `ComplexStandardPermutationStatement`

For every `n` and every two lists `ds`, `es`: if `ds.length = n`, `es.Perm ds`, and
`IsIrreducibleGKModule (complexStandardRep n ds) (complexStandardLie n ds)`, then there is a
linear map `T : X(es) →ₗ[ℂ] X(ds)` that is bijective and satisfies
`IsComplexStandardIntertwining n (complexStandardRep n ds) (complexStandardLie n ds) es T`.
In words: if the principal series of `ds` is irreducible, the principal series of every
rearrangement of `ds` is isomorphic to it as a `(𝔤, K)`-module.

Sources: Knapp 1986 (`provided-40cace9c…`, Representation Theory of Semisimple Groups; the PDF
page is the printed page + 14), and Knapp 1994 (`knapp-1994-archimedean-llc`) for the notion of
infinitesimal equivalence.

Scope of the sources. Global characters are defined on p. 333 for admissible representations
of a linear connected *reductive* group. The results used below, however, are stated under
narrower hypotheses: Section X.3 (p. 347), which contains Proposition 10.18, assumes that `G` is
linear connected *semisimple* and that `G ⊆ G^ℂ` with `G^ℂ` simply connected. `GL_n(ℂ)` is not
semisimple, so the sources are **not** applied to `GL_n(ℂ)` directly. They are applied to
`G' = SL_n(ℂ)` with `K' = SU(n)`, and the conclusion is carried back to `GL_n(ℂ)` by the
elementary steps 1–3 below. `SL_n(ℂ)` (`n ≥ 2`) satisfies every hypothesis of Chapter X: it is a
closed connected subgroup of `GL_n(ℂ)` stable under conjugate transpose, its Lie algebra
`𝔰𝔩_n(ℂ)` is semisimple, and `g ↦ (g, ḡ)` embeds it in `SL_n(ℂ) × SL_n(ℂ)`, a simply connected
complex group whose Lie algebra `𝔰𝔩_n(ℂ) ⊕ 𝔰𝔩_n(ℂ)` is the complexification of `𝔰𝔩_n(ℂ)`
regarded as a real Lie algebra.

* Proposition 10.18 (p. 352, Section X.3): for a minimal parabolic subgroup `S = MAN` and a
  Cartan subgroup `B` of `M`, the global character of the nonunitary principal series
  `U(S, σ, ν)` is `Θ_{σ,ν}(h) = Σ_{w ∈ W(A:G)} (e^{wν} ⊗ χ_{wσ})(h) / (ε_R D)^{G/MA}(h)` on
  `BA`, and `0` off the conjugates of `BA`.
* Proposition 10.5 (p. 336): infinitesimally equivalent admissible representations with global
  characters have equal characters.
* Theorem 10.6 (p. 336): the global characters of infinitesimally inequivalent irreducible
  admissible representations are linearly independent.
* Corollary 10.42 (p. 376): every Harish-Chandra module has a finite composition series; its
  global character is the sum of the global characters of its irreducible subquotients; the
  multiplicities of the subquotients do not depend on the composition series.
* Knapp 1994, p. 399 (PDF page 409): two admissible representations are infinitesimally
  equivalent when their Harish-Chandra modules (`K`-finite vectors with the actions of `𝔤` and
  `K`) are isomorphic; closed invariant subspaces correspond to `(𝔤, K)`-submodules.

How PI follows from the sources. If `es = ds` (in particular if `n ≤ 1`, since a permutation of a
list of length at most one is the list itself), `T` is the identity. Let `n ≥ 2`. Write
`χ = (χ₁, …, χ_n)` for the characters of `ds`, so that the functions `f` in the standard module
satisfy `f(b g) = χ(b) δ^{1/2}(b) f(g)` for upper triangular `b` with diagonal `(a₁, …, a_n)`, where
`χ(b) = ∏ χᵢ(aᵢ)` and `δ^{1/2}(b) = ∏ |aᵢ|^{2((n-1)/2 - i)}` (indices from `0`).

1. *The centre acts by scalars that do not change under permutation.* For `z ∈ ℂ^×`, the scalar
   matrix `z·1` is upper triangular with `δ^{1/2}(z·1) = |z|^{2 Σᵢ ((n-1)/2 - i)} = 1`, and it is
   central, so right translation by `z·1` is left translation: `f(g · z1) = f(z1 · g) =
   ω(z) f(g)` with `ω(z) = ∏ᵢ χᵢ(z)`. Hence `z·1 ∈ U(n)` (for `|z| = 1`) acts on `X(ds)` by the
   scalar `ω(z)`, and the right derivative along `λ·1` (`λ ∈ ℂ`) acts by the scalar
   `d/dt|_{t=0} ω(exp(tλ))`. Both scalars depend only on the product of the characters, so they
   are the same for `ds` and for its rearrangement `es`.
2. *From `(𝔤𝔩_n(ℂ), U(n))` to `(𝔰𝔩_n(ℂ), SU(n))`.* Every `X ∈ 𝔤𝔩_n(ℂ)` is
   `(X - (tr X / n)·1) + (tr X / n)·1` with the first summand in `𝔰𝔩_n(ℂ)`, and every `k ∈ U(n)` is
   `(z·1)(z⁻¹k)` with `zⁿ = det k`, `|z| = 1` and `z⁻¹k ∈ SU(n)`. By step 1 the actions of
   `U(n)` and of `𝔤𝔩_n(ℂ)` on `X(ds)` are those of `SU(n)` and of `𝔰𝔩_n(ℂ)` up to scalars. So a
   subspace of `X(ds)` is `(𝔤𝔩_n(ℂ), U(n))`-invariant if and only if it is
   `(𝔰𝔩_n(ℂ), SU(n))`-invariant; and, the scalars being equal for `es` and `ds`, a linear map
   `X(es) → X(ds)` that intertwines `SU(n)` and `𝔰𝔩_n(ℂ)` also intertwines `U(n)` and
   `𝔤𝔩_n(ℂ)`.
3. *Restriction to `SL_n(ℂ)`.* Every `g ∈ GL_n(ℂ)` is `d · (d⁻¹ g)` with
   `d = diag(det g, 1, …, 1)` upper triangular and `d⁻¹ g ∈ SL_n(ℂ)`. Hence restriction
   `f ↦ f|_{SL_n(ℂ)}` is injective on the standard module of `ds`, and it is onto the smooth
   functions on `SL_n(ℂ)` with the same transformation law under `B' = B ∩ SL_n(ℂ) = M'A'N`
   (extend `f'` by `f(b g') = χ(b) δ^{1/2}(b) f'(g')`; this is well defined because
   `B ∩ SL_n(ℂ) = B'`, and smooth by the formula through `d`). The modular factor of `B'` is the
   restriction of that of `B` (same `N`), so the target is the principal series of `SL_n(ℂ)`
   with parameters `σ' = χ|_{M'}` on `M' = {diagonal unitary matrices of determinant 1}` and `ν'`
   given by `χ|_{A'}` on `A' = {positive diagonal matrices of determinant 1}`. Restriction commutes
   with right translation by `SL_n(ℂ)` and with right derivatives along `𝔰𝔩_n(ℂ)`. By step 1 a
   function is `U(n)`-finite if and only if it is `SU(n)`-finite, and, restriction being
   injective and `SU(n)`-equivariant, if and only if its restriction is `SU(n)`-finite. So
   restriction is a linear bijection from `X(ds)` onto the Harish-Chandra module `X'(ds)` of
   this principal series of `SL_n(ℂ)` that intertwines `(𝔰𝔩_n(ℂ), SU(n))`. (As explained in
   `ComplexGenericParameterReduction.md` for `GL_n(ℂ)`, the Library's left-equivariant functions
   with right translation become Knapp's induced picture under `f ↦ (g ↦ f(g⁻¹))`.) The same
   holds for `es`. The parameter `(σ', ν')` is formed coordinatewise (the `j`-th diagonal entry
   carries the `j`-th character), so if `es` is a rearrangement of `ds`, the parameter of `es` is
   `(w σ', w ν')` for the permutation `w ∈ W(A' : G') ≅ S_n` that permutes the diagonal entries.
4. *The character argument for `SL_n(ℂ)`.* Here `S' = M'A'N` is a minimal parabolic subgroup
   and `M'` is abelian, so `B = M'` in Proposition 10.18. The sum there runs over all of
   `W(A' : G')` and the denominator does not depend on the parameter, so
   `Θ_{wσ', wν'} = Θ_{σ', ν'}`. By steps 2 and 3 and the hypothesis of PI, `X'(ds)` is an
   irreducible `(𝔰𝔩_n(ℂ), SU(n))`-module, so (closed invariant subspaces corresponding to
   submodules) `Θ_{σ', ν'}` is the global character of an irreducible admissible
   representation, and by Proposition 10.5 the character of a principal series depends only on
   its Harish-Chandra module. By Corollary 10.42, `Θ_{wσ', wν'}` is the sum, with
   multiplicities, of the characters of the irreducible subquotients of `X'(es)`. Theorem 10.6
   then forces a single composition factor, infinitesimally equivalent to the principal series
   of `ds`. So `X'(es)` is irreducible and there is a bijective linear map `X'(es) → X'(ds)`
   intertwining `SU(n)` and `𝔰𝔩_n(ℂ)`.
5. *Back to `GL_n(ℂ)`.* Composing with the restriction bijections of step 3 gives a bijective
   linear map `T : X(es) → X(ds)` that intertwines `SU(n)` and `𝔰𝔩_n(ℂ)`; by step 2 it
   intertwines `U(n)` and `𝔤𝔩_n(ℂ)`, that is, it carries right translation by `k ∈ U(n)` and the
   right derivative along `X ∈ 𝔤𝔩_n(ℂ)` on `X(es)` to the same operations on `X(ds)`. This is
   the conclusion of PI.

## Statement NZ: `ComplexStandardNontrivialStatement`

For every `n` and every list `ds` with `ds.length = n`, `X(ds)` is a nontrivial space
(`Nontrivial`, i.e. it has a nonzero element).

Provenance: internal. The principal series has nonzero `K`-finite vectors: restriction to `K`
identifies it with the functions on `U(n)` that transform on the left under the diagonal
unitary group by a character, and such `K`-finite functions exist. This elementary fact is
needed because irreducibility in the Library (`IsIrreducibleGKModule`) includes nontriviality.
It is proved as `complexStandardNontrivial` (module `ComplexStandardNontrivialProof`).

## Statement R: `ComplexStandardSurjectionInjectiveReductionStatement` (universe `uV`)

  `ComplexLanglandsQuotientUniqueStatement.{uV} → ComplexStandardPermutationStatement →
    ComplexStandardNontrivialStatement → ComplexStandardSurjectionInjectiveStatement.{uV}`.

## Helper results

* `IsComplexStandardIntertwining.map_rep`: an intertwining map `A` satisfies
  `A (complexStandardRep n ds k f) = ρ k (A f)` for every `k ∈ U(n)`. The proof uses the first
  clause of `IsComplexStandardIntertwining` at the element of `unitaryCompact ℂ n` corresponding
  to `k`.
* `IsComplexStandardIntertwining.map_lie`: `A (complexStandardLie n ds Y f) = π Y (A f)` for every
  `Y ∈ ℂ ⊗[ℝ] 𝔤𝔩_n(ℂ)`. The definition gives this for `Y = 1 ⊗ X`; the proof extends it to
  `z ⊗ X = z • (1 ⊗ X)` by complex linearity of both sides, and to sums (induction on tensors).
* `IsComplexStandardIntertwining.comp`: if `A` is intertwining into `(ρ, π)` and
  `B : V →ₗ[ℂ] W` carries `ρ k` to `ρ' k` and `π (1 ⊗ X)` to `π' (1 ⊗ X)`, then `B ∘ A` is
  intertwining into `(ρ', π')`.
* `isIrreducibleGKModule_of_injective`: if `X(ds)` is nontrivial and has an injective
  intertwining map `A` into an irreducible `(ρ, π)`, then `X(ds)` is irreducible. The image
  under `A` of an invariant subspace `W` is invariant (by `map_rep` and `map_lie`), so it is `⊥`
  or `⊤`; injectivity of `A` transfers this to `W`.
* `injective_of_isIrreducibleGKModule`: a nonzero intertwining map out of an irreducible `X(ds)`
  is injective, because its kernel is an invariant subspace and is not everything.
* `complexLanglandsLE d e` is the boolean `decide (e.exponent.re ≤ d.exponent.re)`.
  `isComplexLanglandsOrdered_mergeSort`: sorting any list with `List.mergeSort` and this relation
  gives a list in the Langlands order. The relation is transitive and total, so Lean core's
  `List.pairwise_mergeSort` applies.

## Proof of the reduction: `complexStandardSurjectionInjectiveReduction`

Assume LU, PI and NZ, and take the hypotheses of V2 for `n`, `V`, `ρ`, `π`, `ds` and `A`. Let
`ds'` (of length `n`) and the injective intertwining map `B : X(ds') → V` come from
`HasComplexStandardParameter n ρ π ds'`.

1. `X(ds')` is nontrivial by NZ, so `isIrreducibleGKModule_of_injective` makes it irreducible.
2. Let `es = ds'.mergeSort complexLanglandsLE`. It is a permutation of `ds'`
   (`List.mergeSort_perm`), so it has length `n`, and it is in the Langlands order.
3. PI, applied to `ds'` and `es`, gives a bijective intertwining map `T : X(es) → X(ds')`. By
   `comp`, `B ∘ T : X(es) → V` is intertwining. It is nonzero: `X(es)` has a nonzero element by
   NZ, and `B ∘ T` is injective.
4. `A ≠ 0`: `V` is nontrivial (part of irreducibility) and `A` is surjective.
5. LU, applied to `A` and `B ∘ T`, gives `ds.Perm es`. Hence `ds.Perm ds'`.
6. PI, applied to `ds'` and `ds`, gives a bijective intertwining map `T₂ : X(ds) → X(ds')`.
   `X(ds)` is nontrivial by NZ, so `isIrreducibleGKModule_of_injective` (with the irreducible
   target `X(ds')`) makes `X(ds)` irreducible.
7. `injective_of_isIrreducibleGKModule` applied to the nonzero `A` shows that `A` is injective.

## Scope

This module is an intermediate reduction, not a proof of V2: none of LU, PI or NZ is proved
here, and the theorem keeps all three as premises. The Library proves LU as
`complexLanglandsQuotientUnique` (module `ComplexLanglandsQuotientUniqueProof`), PI as
`complexStandardPermutation` (module `ComplexStandardPermutationProof`) and NZ as
`complexStandardNontrivial` (module `ComplexStandardNontrivialProof`);
`complexStandardSurjectionInjective` (module `ComplexStandardSurjectionInjectiveProof`) combines
them into V2.

Like V2, LU and PI are stated for the Library's algebraic `(𝔤, K)`-modules and its
`complexStandardModule`, and their truth relies on identifying `X(ds)` with the Harish-Chandra
module of the classical principal series (see `ComplexGenericParameterReduction.md`). PI is
weaker than the general theory: it needs the isomorphism only when `X(ds)` is irreducible.
