# Normalized quasicuspidal embedding in a product Levi

Author: Worker 917.

This pair states one future proof target in `Langlands.CuspidalSupport`. It
is a proposition definition only. It does not prove the assertion, does not
assume it anywhere, and claims no Library result implies it. Worker 171
requested it as an input for admissibility of arbitrary irreducible
product-Levi representations.

## Exact declaration

`Langlands.CuspidalSupport.NormalizedRefinedQuasicuspidalEmbeddingTheorem.{uF,uV} F T`
has outer binders
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
Its body installs exactly `T.topology` on `F.Carrier` and then asserts:

> for every `n : ℕ`, every `B : GeneralLinear.BlockShape n` and every
> `ω : SmoothRep.{0,uF,uV} ℂ (B.Levi F.Carrier)`, if `ω.IsIrreducible`
> then there are `S : Geometric.BlockRefinement B` and
> `σ : SmoothRep.{0,uF,uV} ℂ ((B.flatten S).Levi F.Carrier)` such that
>
> 1. `σ.IsIrreducible`,
> 2. `CuspidalSupport.IsLeviQuasicuspidal (B.flatten S) σ.representation`,
>    and
> 3. with the instance `T.leviTopologicalGroup B` installed, there is
>    `j : ω.representation.IntertwiningMap (T.normalizedRefinedInduced B S
>    (σ.representation.comp e.symm.toMonoidHom))` with
>    `Function.Injective j`,
>
> where `e := Geometric.flattenedLeviEquiv F.Carrier B S`.

In Lean, `e` is written inline in clause 3. All of `n`, `B` and `ω` are
universally quantified inside the proposition; `F` and `T` are parameters.
`S`, `σ` and `j` are existential. The statement does not claim that `S` or
`σ` is unique, and it adds no minimality condition on `S`.

`T.leviTopologicalGroup B` is the Library theorem that `B.Levi F.Carrier`,
with the topology induced by `T.topology`, is a topological group. It is
installed with `letI` immediately before the existential over `j`, because
the type of `T.normalizedRefinedInduced` mentions it. It installs no new
topology.

## The objects involved

All names below are existing Library declarations, reused by name.

- `B.Levi F.Carrier` (`Langlands.Group.GL.Blocks`) is the actual product
  `∀ i : Fin B.length, GeneralLinear (B.size i) F.Carrier`, with the
  product of the matrix topologies induced by `T.topology`.
  `SmoothRep.{0,uF,uV} ℂ G` is the full subcategory of `Rep ℂ G` whose
  objects are smooth, so smoothness is part of the input and of `σ`.
  `SmoothRep.IsIrreducible` is `Representation.IsIrreducible` of the
  underlying action: the lattice of invariant subspaces is simple. It
  includes nonzeroness and requires no finite dimension.
- `BlockRefinement B` (`Geometric.WeylDefinitions`) is
  `∀ i : Fin B.length, BlockShape (B.size i)`, an ordered partition of every
  outer block into positive inner blocks. The subgroups `refinedParabolic`,
  `refinedLevi` and `refinedUnipotent` of `B.Levi R` are the products over
  `i` of the upper block parabolic, the block diagonal Levi and the upper
  block unipotent subgroup of `S i`. `refinedLeviProjection` is the
  projection of the refined parabolic onto the refined Levi.
- `B.flatten S` (`CuspidalSupport.MinimalJacquetProof`) is the block shape
  of rank `n` whose blocks are the inner blocks of `S 0`, then those of
  `S 1`, and so on.
- `IsLeviQuasicuspidal C ρ` (`CuspidalSupport.LeviDefinitions`) says that
  for every `S' : BlockRefinement C` with `refinedParabolic F C S' ≠ ⊤`, the
  coinvariants `Jacquet.Coinvariants ρ (refinedUnipotent F C S')` form a
  subsingleton. Clause 2 applies it with `C = B.flatten S` to the action of
  `σ` itself, so the refinements tested are refinements of the flattened
  shape.
- `Representation.IntertwiningMap` is Mathlib's structure of a linear map
  commuting with the two actions. `Function.Injective j` concerns its
  underlying function, which is the underlying linear map.

### The coordinate direction

`flattenedLeviEquiv F.Carrier B S` (`Geometric.FlattenedLevi`) is a
multiplicative equivalence

`e : (B.flatten S).Levi F.Carrier ≃* refinedLevi F.Carrier B S`

from the flattened product to the subgroup-valued refined Levi. By
`flattenedLeviEquiv_component`, the `j`-th inner diagonal block of outer
block `i` of `e m` is the flattened block number
`B.flattenBlockEquiv S ⟨i, j⟩` of `m`, with the matrix indices cast along
`B.flatten_size_flattenBlockEquiv S ⟨i, j⟩`.
`flattenedLeviEquiv_symm_component` gives the inverse formula.

`σ` is a representation of the flattened Levi. Induction needs a
representation of `refinedLevi F.Carrier B S`, so clause 3 pulls `σ` back
along the inverse:
`σ.representation.comp (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom`.
Its carrier is the carrier of `σ`, and `m` in the refined Levi acts by
`σ(e⁻¹ m)`. The same inverse pullback appears in
`Parabolic.isAdmissible_flattenedLeviTransport_iff` and
`Parabolic.refinedCuspidalInduction_isAdmissible`. The statement uses no
abstract isomorphism, tensor product presentation or other coordinate model.

### The induced representation

For `τ : Representation ℂ (refinedLevi F.Carrier B S) V`,
`T.normalizedRefinedInduced B S τ` (`Geometric.RefinementFunctors`) is
`normalizedRefinedInducedOf B S (T.refinedLeviHalfModulus B S) τ`, that is,
`Induction.smoothInduced` for the subgroup `refinedParabolic F.Carrier B S`
and the inducing action
`twist (T.refinedParabolicHalfModulus B S)
(τ.comp (refinedLeviProjection F.Carrier B S))`.

- **Carrier.** `Induction.SmoothFunctions`: functions `f` from
  `B.Levi F.Carrier` to `V` satisfying the covariance below, each fixed by
  right translation by some open subgroup. The carrier lives in
  `Type (max uF uV)`.
- **Positive half-modulus covariance.** By
  `normalizedRefinedInducedOf_covariant`,
  `f(q g) = χ(π q) • τ(π q)(f g)` for `q` in the refined parabolic and `g`
  in `B.Levi F.Carrier`. Here `π` is `refinedLeviProjection` and
  `χ = T.refinedLeviHalfModulus B S`. By `refinedLeviHalfModulus_apply`,
  `χ m` is the nonnegative real square root of `T.refinedLeviModulus B S m`.
  That modulus is the product over the outer blocks `i` of
  `T.leviModulus (S i)` on the inner coordinates of `m`. Each
  `T.leviModulus` is `∏_{k<l} |det m_k|^{n_l} / |det m_l|^{n_k}` on the
  blocks of `S i`.
- **Action.** Right translation: by `normalizedRefinedInducedOf_apply`,
  `(g • f)(x) = f(x g)`.

## Universes

`uF` is the universe of the field carrier, so `B.Levi F.Carrier`,
`(B.flatten S).Levi F.Carrier` and `refinedLevi F.Carrier B S` lie in
`Type uF`. The coefficient field `ℂ` is in `Type 0`, the first universe
argument of `SmoothRep`. `uV` is the carrier universe of both `ω` and `σ`.
It is an independent universe parameter, with no relation imposed to `uF`.
The induced carrier, a type of functions on `B.Levi F.Carrier`, lies in
`Type (max uF uV)`. The intertwining map goes from a `uV` carrier into this
`max uF uV` carrier.

Consumers whose input carriers live in the saturated universe use the
specialization
`NormalizedRefinedQuasicuspidalEmbeddingTheorem.{uF, max uF uV} F T`. A
private check elaborated this specialization together with `{uF, uF}` and
`{uF, 0}`. It also checked that the displayed induced carrier has type
`Type (max uF uV)`.

## Included boundary cases

There is no hypothesis on `n`, `B`, `ω` or `T` besides the ones displayed.
In particular there is no assumption of admissibility, finite length,
finite generation, finite dimension, a central character, positive rank, a
tensor factorization along the blocks, a preselected refinement, an existing
embedding, or quasicuspidality of `ω`. There are no theorem-valued
parameters. The conclusion asserts neither admissibility nor finite length,
of `ω`, of `σ` or of the induced representation.

- **Whole-product refinement.** `S` may be the refinement in which every
  `S i` has a single block. Then the refined parabolic is all of
  `B.Levi F.Carrier`, the half modulus is one, and the induced
  representation is isomorphic to the pulled-back action. This is the expected
  witness when `ω` is already quasicuspidal.
- **Rank zero and the empty shape.** For `n = 0`, positivity of the block
  sizes and `∑ i, B.size i = 0` force `B.length = 0`. Then
  `B.Levi F.Carrier` is the one-element group, the only refinement is the
  empty family, and `B.flatten S` is again empty. An irreducible `ω` has a
  one-dimensional carrier. Every refinement of the empty flattened shape has
  the whole group as refined parabolic, so `IsLeviQuasicuspidal` holds
  vacuously. One may take for `σ` the trivial action on the carrier of `ω`.
  The covariance condition is then vacuous, the induced functions are
  determined by their value at the identity, and `v ↦ (g ↦ v)` is an
  injective intertwining map. So the statement needs no positivity
  hypothesis. This elementary argument is internal derived content. It is
  not quoted from the source, which does not discuss `GL_0`, and this pair
  does not formalize it.

## Original source

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group
GL(n,F) where F is a non-Archimedean local field*, Russian Math. Surveys
31:3 (1976), 1–68, English translation (cited as BZ76). Literature ID:
`bernstein-zelevinsky-1976-representations-gln`. PDF SHA-256:
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Readable original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.
Printed page numbers equal the PDF page numbers.

I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups. I*, Annales scientifiques de l'Ecole Normale Superieure (4)
10 (1977), 441–472 (cited as BZ77). Literature ID:
`bernstein-zelevinsky-1977-induced-i`.
PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Readable original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

The passages below were read directly on 2026-10-28.

BZ76:

- **2.21–2.22**, pp.21–22. For a closed subgroup `H` of an l-group `G`
  and `(ρ, H, E)`, `L(G, ρ)` consists of the functions `f : G → E` with
  `f(hg) = ρ(h) f(g)` and invariance on the right by an open compact
  subgroup. `G` acts by `(π(g₀)f)(g) = f(g g₀)`; this is `Ind(G, H, ρ)`.
  `ind(G, H, ρ)` is the subrepresentation of functions finite modulo `H`.
  The remark in 2.22 mentions a modulus-normalized variant of condition 1).
- **3.3–3.5**, pp.29–30. Partitions `α = (n₁, …, n_r)` of `n` into
  consecutive segments; `β ≤ α` when each segment of `α` is a union of
  segments of `β`. `G_α = ∏ G_{n_i}`, and for `β ≤ α` the group `G_β` is
  embedded in `G_α` in the natural way. `U_β` consists of the upper
  unitriangular matrices whose off-diagonal entries vanish inside each
  segment of `β`, and `P_β = G_β · U_β`. For `β ≤ α`,
  `U_β(α) = U_β ∩ G_α` and `P_β(α) = P_β ∩ G_α = G_β · U_β(α)`.
- **3.6**, p.30. `G_α` is compact modulo every parabolic subgroup.
- **3.12–3.13**, pp.32–33. `i_{α,β}(ρ) = ind(G_α, P, ρ)` for
  `P = P_β(α)`, with `ρ` extended trivially on `U = U_β(α)`; this is
  unnormalized induction. `r_{β,α}(π)` is the natural action of `G_β` on
  the coinvariants `E_U`. 3.13(b): first adjointness
  `Hom_{G_β}(r_{β,α}(π), ρ) ≅ Hom_{G_α}(π, i_{α,β}(ρ))`, proved using
  `i_{α,β}(ρ) = Ind(G_α, P, ρ)` by 3.6. 3.13(c): transitivity. 3.13(e):
  `r_{β,α}` preserves finite generation.
- **3.18**, p.34. `π ∈ Alg G_α` is quasi-cuspidal if `r_{β,α}(π) = 0` for
  all `β ≠ α`, `β ≤ α`.
- **3.19**, p.34. "Let `π ∈ Alg G_α` be irreducible. Then there exist a
  partition `β ≤ α` and an irreducible quasi-cuspidal representation
  `ρ ∈ Alg G_β` such that `π` is embedded in `i_{α,β}(ρ)`." The proof takes
  `β ≤ α` with `r_{β,α}(π) ≠ 0` and `r_{γ,α}(π) = 0` for all `γ < β`, uses
  3.13(c) for quasi-cuspidality and 3.13(e) for finite generation, takes an
  irreducible quotient `ρ` by 2.6, and applies 3.13(b); a nonzero map from
  an irreducible `π` is an embedding.

BZ77:

- **1.7–1.8**, printed p.444 / PDF p.5. `mod_U(g)` is the module of the
  automorphism `u ↦ g u g⁻¹`. Normalized induction 1.8(a)(1) uses
  `f(umg) = θ(u) mod_U^{1/2}(m) ρ(m)(f(g))` with right translation
  `(δ(g)f)(g') = f(g' g)`. Localisation 1.8(b) acts by
  `mod_U^{-1/2}(m)·(π(m)ξ + E(U, θ))`. The exponent signs were read from
  the rendered page, since the PDF text layer drops the minus sign.
- **2.1–2.4**, printed p.446 / PDF p.7. Standard subgroups of
  `GL(n, F)` are the `G_α`; `G_β < G_α` iff `β` is a subpartition of `α`;
  standard subgroups of a standard subgroup are its standard subgroups in
  `G`; quasicuspidality is vanishing of all proper `r_{M,G}`.

No erratum or correction for either source was found. The search covered
the project literature folder, its central-library pointer file and the
Library notes on 2026-10-28.

### Correspondence

- **The groups.** The source's `G_α` is `B.Levi F.Carrier`, for the
  partition `α` given by the block sizes of `B`. A partition `β ≤ α` is an
  ordered partition of every segment of `α`, which is a
  `BlockRefinement B`; the partition `β` itself is `B.flatten S`, and the
  abstract product `G_β` is `(B.flatten S).Levi F.Carrier`. The natural
  embedding of 3.4 of `G_β` into `G_α` is `e` followed by the inclusion of
  `refinedLevi F.Carrier B S`. Because the flattened order is outer block
  first, then inner block, `e` matches the source ordering of the segments
  of `β`. `P_β(α)` and `U_β(α)` are `refinedParabolic` and
  `refinedUnipotent`. This identification is derived from 3.3–3.5 and is
  not quoted. The field is a finite extension of `ℚ_p` with arbitrary
  supplied topological data, a special case of the source's
  non-Archimedean local field.
- **Quasicuspidality of `σ`.** By 3.18 and BZ77 2.1–2.4, quasicuspidality
  of a representation of `G_β` is vanishing of its coinvariants for every
  proper standard parabolic of `G_β`, that is, for every refinement of the
  partition `β` with proper refined parabolic. Clause 2 states exactly
  this for the flattened shape, via `IsLeviQuasicuspidal (B.flatten S)`.
- **The category.** The source's `Alg G` consists of complex
  representations with open vector stabilizers. This is `SmoothRep ℂ G`.
  The carrier universe `uV` is unrestricted, as the source places no
  cardinality condition on the representation space.
- **The induction.** By 3.6, `i_{α,β}(ρ) = Ind(G_α, P_β(α), ρ)`. Its
  functions satisfy `f(pg) = ρ(π p) f(g)` with right translation, and they
  are invariant on the right under an open compact subgroup. The Lean
  carrier uses an open subgroup instead; in `B.Levi F.Carrier` every open
  subgroup contains an open compact one, so the conditions agree.

### From the unnormalized source to the normalized statement

BZ76 3.19 is stated for unnormalized induction. The Lean statement uses the
normalized induction of BZ77 1.8. The conversion below is derived content,
not quoted from either source, and it is not formalized in this pair.

Let `ρ` be the source representation of `G_β`, viewed on the refined Levi,
and let `χ = T.refinedLeviHalfModulus B S`, a positive smooth character of
`refinedLevi F.Carrier B S`. Put `τ := χ⁻¹ ⊗ ρ`, that is, `τ(m) = χ(m)⁻¹ ρ(m)`.
The normalized covariance of `T.normalizedRefinedInduced B S τ` reads
`f(q g) = χ(π q) χ(π q)⁻¹ ρ(π q)(f g) = ρ(π q)(f g)`. This is the
unnormalized covariance of 2.21, with the same right translation. So the
normalized induction of `τ` and the unnormalized induction of `ρ` have the
same functions and the same action, and an embedding of `π` into one is an
embedding into the other. Finally `σ := τ ∘ e`, a representation of the
flattened Levi, satisfies `σ.comp e.symm = τ`.

The twist and the transport preserve the clauses:

- a twist by a character has the same invariant subspaces, and `e` is a
  group isomorphism, so `σ` is irreducible when `ρ` is;
- `χ` is locally constant, since the kernel of `T.refinedLeviModulus B S`
  is open (`isOpen_ker_refinedLeviModulus`), and `e` is a homeomorphism
  (`flattenedLeviEquivContinuous`), so `σ` is smooth when `ρ` is;
- every element of a refined unipotent subgroup of the refined Levi has
  determinant one in every diagonal block, so `χ` is one there and `τ` has
  the same coinvariants as `ρ`; `e` carries the standard refined subgroups
  of the flattened Levi to those of `G_β`, so `σ` is quasicuspidal when
  `ρ` is.

The identification of `χ²` with BZ77's `mod_U` for `U = U_β(α)` uses the
conjugation module of the upper block radical,
`∏_{k<l} |det m_k|^{n_l} / |det m_l|^{n_k}` inside each outer block. This
is the form of `T.leviModulus`. The conversion itself only needs `χ` to be a
smooth character trivial on unipotent elements, so it does not depend on
this identification.

## Relation to existing declarations

- `NormalizedQuasicuspidalEmbeddingTheorem` in
  `CuspidalSupport.QuasicuspidalPrerequisitesStatement`, proved in
  `CuspidalSupport.QuasicuspidalEmbeddingProof`, concerns inputs that are
  smooth representations of `GeneralLinear n F.Carrier` with `0 < n`. A
  representation of `B.Levi F.Carrier` is not such an input, not even for a
  one-block shape, whose Levi is a different Lean type. That theorem
  therefore does not supply this statement.
- `MinimalNonzeroRefinedJacquetTheorem` in
  `CuspidalSupport.MinimalRefinedJacquetStatement` is the published
  descent statement for product-Levi inputs. It pulls back along
  `GeneralLinear.BlockShape.leviRefinementEquiv`, while this statement uses
  `Geometric.flattenedLeviEquiv`. Their agreement is a proof obligation,
  not an assumption of this pair.
- `IrreducibleLeviAdmissibilityTheorem` in
  `CuspidalSupport.IrreducibleLeviAdmissibilityStatement` is the intended
  consumer. This pair does not use it.

## Proof outline (unproved)

The following is an intended route for a separate proof task, following the
source proof of 3.19. It is an outline only; nothing in it is proved here.

1. Apply `MinimalNonzeroRefinedJacquetTheorem` to `ω` to obtain `S` with a
   nonzero refined Jacquet quotient whose normalized action, pulled back to
   the flattened Levi, is quasicuspidal.
2. Show that this quotient is finitely generated, from irreducibility of
   `ω` and the analogue of 3.13(e), and extract an irreducible quotient
   `σ`; quotients of quasicuspidal representations stay quasicuspidal.
3. Transport between the coordinates of `leviRefinementEquiv` and of
   `flattenedLeviEquiv`.
4. Use the refined Frobenius map `Parabolic.FirstAdjointness.refinedFrobenius`
   to turn the nonzero quotient map into a nonzero intertwining map into
   `T.normalizedRefinedInduced B S (σ.comp e.symm)`, matching the normalized
   Jacquet and induction conventions.
5. Conclude injectivity from irreducibility of `ω`.

This pair proves no descent, finite generation, adjointness, embedding or
admissibility.
