# At large level, torsion configurations determine data over algebraically closed fields

`Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionConfigurationDeterminationStatement`
is a proposition definition. It is a statement only. The module proves nothing.

## The statement

The statement is universe polymorphic in `u`. It says: for every
`P : Prerequisites.{u}` and all natural numbers `g d` with `0 < g` and `0 < d`,
there is a natural number `N` such that the following holds for every level
`n ≥ N`. Let `K : Type u` be an algebraically closed field with `(n : K) ≠ 0`, and
let `a b : Datum P (Spec K) g d n` be two data over `Spec K`. If
`a.TorsionConfigurationEquivalent b` (module `TorsionConfiguration`), then
`Isomorphic a b`.

`Isomorphic a b` is the published relation of module `Data`. It asks for a
polarized isomorphism `PolarizedIso a b`, that is, an isomorphism of abelian
schemes that carries the polarization of `a` to that of `b` and carries every
ordered level section of `a` to the corresponding one of `b`.

The bound `N` may depend on `P`, `g` and `d`, but not on `n`, `K`, `a` or `b`.
The statement says nothing about levels `n < N`. It makes no claim over bases
other than algebraically closed fields.

## Provenance

This is a derived intermediate statement. GIT does not state it. GIT does
contain the last step of the intended proof below, in a version for linearly
rigidified data (Mumford–Fogarty–Kirwan, *Geometric Invariant Theory*, 3rd
edition, registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
content SHA-256
`3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`, Chapter 7,
§2, printed pp.130–131, PDF pp.143–144).

GIT Definition 7.6 (printed p.130) defines the functor ℋ_{g,d,n} of *linearly
rigidified* polarized abelian schemes with level-`n` structure. An element
`α ∈ ℋ_{g,d,n}(S)` consists of an abelian scheme `π : X → S`, the level sections
`σ_1, …, σ_{2g}`, a polarization `ω` of degree `d²`, and a linear
rigidification `φ`. This is more structure than an element of the ordinary
functor 𝒜_{g,d,n} of Definition 7.2 (printed p.129), which has no `φ`. Using `φ`,
GIT embeds `X` as `I : X ↪ P^m × S`. On printed p.131 it then writes:

> I claim that the whole structure defining α ∈ ℋ_{g,d,n}(S) is determined only
> by (a) the embedding I: X ↪ (P^m × S), (b) the 2g + 1-sections of X/S:
> e, σ_1, σ_2, …, σ_{2g}.

The argument that follows has three parts, paraphrased here.

1. The identity section `e` determines the group law (Corollary 6.6), and the
   `σ_i` determine the level structure.
2. GIT identifies the pullback of `𝒪(1)` along `I` followed by the projection
   to `P^m` with the cubic bundle `L_Δ(ω)³`, normalized along `e` (§6.2). So the
   homomorphism `Λ(L_Δ(ω)³) = 6ω` (Proposition 6.10) is determined. Since the
   group of `S`-homomorphisms from `X` to `X̂` has no torsion, `ω` itself is
   determined. Torsion-free cancellation is thus the step that recovers the
   polarization.
3. GIT then recovers the rigidification `φ` from the embedding.

The present statement concerns ordinary polarized data, which carry no linear
rigidification. Its intended proof uses only parts 1 and 2, which recover the
group law, the level structure and the polarization. Part 3 is not needed,
because the rigidification has been forgotten.

GIT obtains quasi-projectivity of the fine moduli scheme (Theorem 7.9, printed
p.139, PDF p.152) by a different route. It descends along a quotient of the
scheme `H_{g,d,n}` of linearly rigidified data. This statement is not part of that
route. It is used instead to show that a bracket map is quasi-finite.

## Intended proof (not established)

Nothing in this section is proved or claimed. It records the route a proof is
expected to take.

Write `a = (A, λ, α)` and `b = (B, μ, β)`. Let `φ` and `(ψ_r)_r` witness the
configuration equivalence. Let `L_a` and `L_b` be the canonical bundles, so the
cubic bundles are `L_a³` and `L_b³`. Put `V_a = H⁰(A, L_a³)`, a vector space of
dimension `6^g · d` by the published `CubicDirectImageStatement` (proved in the
Library).

1. **Embeddings.** The complete linear system of `L_a³` gives a closed immersion
   `ι_a : A → P(V_a^∨) ≅ P^M` with `M = 6^g · d − 1`, and `ι_a^* 𝒪(1) ≅ L_a³`. The
   published `CubicFieldEmbeddingStatement` is the Library form of this. The
   point `ι_a(P^a_r)` is the line of the evaluation `ev^a_r`. Identify `P(V_a^∨)`
   with `P(V_b^∨)` through `φ`. The equations `φ ≫ ev^b_r = ev^a_r ≫ ψ_r` then say
   `ι_a(P^a_r) = ι_b(P^b_r)` for every `r : Fin (2g) → ZMod n`.
2. **Forms of bounded degree.** Let `F` be a homogeneous form of degree `t ≥ 1`
   vanishing on `ι_b(B)`. Then `F` vanishes at every point `ι_a(P^a_r)`. Because
   the level is full, the `P^a_r` are the `n^{2g}` distinct points of `A[n]`.
   Suppose `F` does not vanish on `ι_a(A)`. Its restriction is then a nonzero
   section of `L_a^{3t}` that vanishes on all of `A[n]`. Now `L_a^t` is the
   canonical bundle of the datum `(A, tλ, α)`, whose degree index is `t^g · d`, so
   `L_a^{3t}` is that datum's cubic bundle. The section is a hyperplane section of
   the complete embedding by `L_a^{3t}`. The published
   `CubicTorsionHyperplaneBoundStatement` (GIT Proposition 7.7, proved in the
   Library) bounds the number of `n`-torsion points on such a hyperplane by
   `6^g · t^g · d · g! · n^{2g−2}`. This is less than `n^{2g}` once
   `n² > 6^g · t^g · d · g!`, a contradiction. So `F` vanishes on `ι_a(A)`. By
   symmetry, the degree-`t` parts of the homogeneous ideals of `ι_a(A)` and
   `ι_b(B)` agree for every `t ≤ t₀`, provided `n² > 6^g · t₀^g · d · g!`.
3. **Uniform regularity.** Both images have Hilbert polynomial
   `h(t) = 6^g · d · t^g`, by Riemann–Roch for `L^{3t}` (GIT Proposition 6.13).
   By the uniform bound for the Castelnuovo–Mumford regularity of ideal sheaves
   with a given Hilbert polynomial (Gotzmann's regularity theorem), there is
   `t₀`, depending only on `h` and `M`, such that every closed subscheme of `P^M`
   with Hilbert polynomial `h` is cut out by its forms of degree `t₀`. Choose `N`
   with `N² > 6^g · t₀^g · d · g!`. Then `ι_a(A) = ι_b(B)` as closed subschemes.
   The Library's port of the FLT development contains a related uniform
   statement,
   `AlgebraicGeometry.HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq`
   (module
   `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq`).
   It gives agreement of the Hilbert function with `h` from a uniform degree on.
   Whether it suffices for this step is open.
4. **Isomorphism.** The equality of images gives an isomorphism of `K`-schemes
   `f : A → B` with `ι_b ∘ f = ι_a`. Since `ι_b` is injective on points,
   `f(P^a_r) = P^b_r` for every `r`. For `r = 0` this is `f(0) = 0`, so `f` is an
   isomorphism of abelian varieties carrying the ordered level of `a` to that of
   `b`. Also `f^*(L_b³) ≅ L_a³`. The bundle `L` of a polarization `λ` satisfies
   `Λ(L) = 2λ` (GIT Proposition 6.10), so `Λ(L³) = 6λ`. Therefore
   `6 · (f^∨ ∘ μ ∘ f) = 6 · λ`. Since `Hom(A, Â)` is torsion free,
   `f^∨ ∘ μ ∘ f = λ`, which is the polarization equation of `PolarizedIso`. This
   step follows the parts of GIT's argument that recover the group law, the level
   structure and the polarization. The recovery of a linear rigidification is not
   used.

## Role

This statement is one of three inputs of the proved definition
`largeLevelQuasiFiniteProjective_of_torsionBrackets` (module
`LargeLevelQuasiFiniteProjectiveBracketReduction`), used at universe `0`. The other
two are the companion `TorsionBracketMapStatement` and the accepted
`LargeLevelFiniteTypeStatement`. The definition proves
`LargeLevelQuasiFiniteProjectiveStatement`. In it, this statement turns finitely
many configuration classes in a geometric fibre of the bracket map into finitely
many geometric points.
