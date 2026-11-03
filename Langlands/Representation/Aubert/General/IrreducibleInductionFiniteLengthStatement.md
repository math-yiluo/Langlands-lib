# Finite length of the actual dynamic normalized induction of irreducibles

Author: Worker 757, for task `1d3f1a06-ca7b-4438-ba38-885d5f70eda9`.
This module declares one proposition definition and no theorem, and it does
not prove the proposition. The parent Renard program
(`f5d1f399-a1f8-4ab5-a981-90b92abd4857`) plans a separate exact proof task for
this declaration.

## Source

D. Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`),
§VI.6.2 "Induction et longueur finie", Lemme and its proof, printed p. 178 /
PDF p. 184. In this file, PDF page = printed page + 6. The Lemme reads:

> Soit `P = MN` un sous-groupe parabolique de `G` et soit `(τ, E)` une
> représentation irréductible de `M`. Alors la représentation `i^G_P(τ, E)`
> de `G` est de longueur finie.

In English: for a parabolic subgroup `P = MN` of `G` and an irreducible
representation `(τ, E)` of `M`, the normalized induced representation
`i^G_P(τ, E)` of `G` has finite length. In Renard, `G` is the group of
`F`-points of a connected reductive group over an arbitrary nonarchimedean
local field `F` (V.1, printed p. 103; V.2.1, printed p. 104). Representations
are smooth complex representations.

## The declaration

`Langlands.Aubert.General.DynamicInductionIrreducibleFiniteLengthStatement.{u, uV} : Prop`
is a closed `def`. Its binders are exactly those of the published
`Langlands.Aubert.General.DynamicInductionFiniteLengthStatement.{u, uV}`
(module `Langlands.Representation.Aubert.General.PrerequisiteStatements`), in
the same order:

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]` and
  Mathlib's `[IsNonarchimedeanLocalField F]`. This covers every
  nonarchimedean local field, in every characteristic;
- a group scheme `G : GroupScheme (Spec (CommRingCat.of F))` with
  `hG : IsConnectedReductive G`, so every connected reductive group over `F`;
- every cocharacter `χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G`, including
  those with `P(χ) = G`;
- after `haveI := hG.isAffineHom` and
  `haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom`, the pinned
  topology `letI := rationalPointTopology F G.X` on
  `G(F) = RationalPoint F G.X`;
- `[LocallyCompactSpace (RationalPoint F G.X)]`,
  `[NonarchimedeanGroup (RationalPoint F G.X)]` and
  `hU : IsClosed U(χ)(F)`, where
  `U(χ)(F) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of F))))`.

These last three are exactly the hypotheses needed to form the functor. All
three are propositions, so they add no data. They hold for the pinned topology
(Renard V.2.1; Conrad, Proposition 2.1), and nothing here proves them.

Only the conclusion differs from the whole target. Here it is

```lean
∀ A : SmoothRep.{0, u, uV} ℂ
    ((Dynamic.centralizer χ).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of F)))) :
        Subgroup (RationalPoint F G.X)),
  A.IsIrreducible →
    ((normalizedInductionFunctor.{u, uV}
      (dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 (Spec (CommRingCat.of F))))) hU).obj A).HasFiniteLength
```

In words: every irreducible smooth complex representation `A` of the actual
Levi subgroup `Z(χ)(F) ≤ G(F)`, with the subspace topology, induces to a
smooth representation of `G(F)` of finite length. There is no other
representation-theoretic premise: no admissibility, finite dimension,
cuspidality, chosen cuspidal embedding, transitivity or geometric-lemma input.
The statement does not assume `CharZero F`, a splitness condition or a matrix
model. It also adds no structural hypothesis beyond the functor's typing
hypotheses: no closedness of `P(χ)(F)`, continuity of the projection,
Hausdorffness of `G(F)`, or unimodularity of `U(χ)(F)`.

### Universes

- `u` is the universe of `F`. The points `RationalPoint F G.X` and the
  subgroup `Z(χ)(F)` live in `Type u`.
- `uV` is the carrier universe of the inducing representation `A`. It is
  independent of `u`.
- The coefficient ring `ℂ` is in universe `0`.
- The functor's codomain is `SmoothRep.{0, u, max u uV} ℂ G(F)`. The induced
  space consists of functions `G(F) → A`, so its carrier is saturated to
  `Type (max u uV)`. This is the existing universe behavior of
  `normalizedInductionFunctor`, and it is unchanged here.

## The functor

`normalizedInductionFunctor h hU` (`Aubert/General/Parabolic`, Worker 23) is
applied to the published decomposition
`dynamic_isSemidirectDecomposition χ (Over.mk (𝟙 _))`, which is
`P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)` (`Aubert/General/DynamicParabolic`). The functor
is

`inflationFunctor h ⋙ Induction.normalizedSmoothInductionFunctor P (inductionCharacter U P hU h.le_normalizer)`.

- It inflates `A` along the projection `P(χ)(F) →* Z(χ)(F)`. That projection
  is the published `Dynamic.limitHom` (`dynamic_projection_eq_limitHom`).
- It twists by `inductionCharacter U P hU _`, whose underlying character is
  `HaarModulus.closedHalfCharacter U hU P _`. This is the positive square root
  `δ(p)^{1/2}` of the Haar modulus of conjugation by `p ∈ P(χ)(F)` on the closed
  subgroup `U(χ)(F)`. It is defined on all of `P(χ)(F)`.
- It takes smooth induction (`Induction.smoothInduced`). The induced space is
  the space of functions `f : G(F) → A` with
  `f(p g) = δ(p)^{1/2} A(proj p) f(g)` (Mathlib's `Representation.coindV`)
  that have an open stabilizer under right translation. `G(F)` acts by right
  translation.

## The predicates

- `SmoothRep.IsIrreducible A` (`Representation/Category/Basic`) is Mathlib's
  `Representation.IsIrreducible`, i.e. `IsSimpleOrder` on the lattice of
  invariant subspaces. It includes nonzeroness and does not require finite
  dimension.
- `SmoothRep.HasFiniteLength B` is
  `IsFiniteLength ℂ[G(F)] B.representation.asModule`. This is finite
  composition length over the group algebra, not finite dimension. By
  Mathlib's `isFiniteLength_iff_exists_compositionSeries`, it holds exactly
  when the lattice of `ℂ[G(F)]`-submodules has a composition series from `⊥`
  to `⊤`.

Renard's finite length is that of A.VI.3 (printed p. 263): an object of an
abelian category has finite length if it has a Jordan–Hölder series, and it is
simple if it is nonzero and has no subobjects other than `0` and itself.
III.1.4 (printed p. 60) carries this terminology over to smooth
representations through the equivalence `M(G) ≃ M(H(G))`. A subobject of a
smooth representation in `M(G)` is a `G`-stable subspace, which is
automatically smooth. The `ℂ[G]`-submodules of the underlying module are the
same subspaces. So Renard's "irréductible" and "de longueur finie" are the
Library's `IsIrreducible` and `HasFiniteLength`. This is a comparison of
definitions. It is not a Lean theorem in this module.

## Comparison of normalizations

Renard (VI.1.2, formula (VI.1.2.1), printed p. 135) defines
`i^G_P(τ, E) = Ind^G_P(τ ⊗ δ_P^{-1/2}, E)`, where `δ_P` is inflated from `M` to
`P`. Formula (VI.1.2.3), printed p. 136, reads
`f(m n g) = δ_P^{-1/2}(m) τ(m) f(g)`.

**Reciprocal modular character.** Renard's modular function is defined in
II.3.7 (printed p. 47) by `r(g) · μ_G = δ_G(g) μ_G`. The Remarque on printed
p. 136 says that, because of this choice, his `δ_P` is the inverse of the one
usually used in these formulas. The Lemme of V.5.4 (printed pp. 126–127) makes
this explicit. It gives `μ_P(a⁻¹ K_M K_N a) = δ_P(a) μ_P(K_M K_N)` and
`δ_P(a) = [a⁻¹ K_N a : K_{1,N}] / [K_N : K_{1,N}]`, and it extends
`δ_P = δ_N` to all `m ∈ M`. So Renard's `δ_P(m)` is the factor by which
`x ↦ m⁻¹ x m` scales Haar measure on `N`. The Library's
`HaarModulus.normalizerCharacter U m` is the factor by which `x ↦ m x m⁻¹`
scales Haar measure on `U`. That is the Bernstein–Zelevinsky 1977 §1.7
convention, with `δ(diag(a, b)) = |a/b|` for `B ⊂ GL_2`; see
`normalizerCharacter_smul_map` and [`Parabolic.md`](Parabolic.md). Hence, on
the Levi subgroup, Renard's `δ_P(m)` is the Library's `δ(m)⁻¹`, and Renard's
twist `δ_P^{-1/2}(m)` is the Library's `δ(m)^{1/2}`. On `M` the two inducing
twists therefore agree. This is a reading of the source conventions, not a
Lean theorem.

**Full-parabolic versus Levi-inflated twist.** The two twists are defined
differently on the unipotent radical.

- Renard's twist is the Levi character inflated to `P`. It is trivial on `N`
  by the Remarques on printed p. 136: `δ_P` is trivial on compact subgroups,
  and `N` is a union of compact open subgroups (V.5.2(iii), printed p. 123).
- The Library's `closedHalfCharacter U hU P` is defined on all of `P(χ)(F)`.
  At `u ∈ U(χ)(F)` its value is `δ(u)^{1/2}`, the half modulus of the inner
  automorphism by `u` of `U(χ)(F)`. On the Levi it agrees with the Levi half
  modulus by definition (`closedHalfCharacter_levi`).

The two characters on `P` agree exactly when `U` is unimodular: under the
named hypothesis `IsUnimodularModulus U hU`, `closedHalfCharacter_eq_comp_projection`
shows that the Library twist is the Levi half modulus composed with the
projection. Unimodularity follows from
`Jacquet.Localization.IsLimitOfCompactSubgroups U` by
`isUnimodularModulus_of_isLimitOfCompactSubgroups`. For `U(χ)(F)` this is
Renard V.5.2(iii), but at this module's Library base neither
`IsLimitOfCompactSubgroups` nor `IsUnimodularModulus` is proved for
`U(χ)(F)`. So the identification of the actual functor with Renard's
`i^G_P` remains an unproved comparison. This statement neither assumes nor
discharges it. The statement is about the actual Library functor, and a proof
must prove it for that functor. Proving unimodularity of `U(χ)(F)` is one
possible step, but it is not a premise.

**Parabolic subgroups.** The source quantifies over all parabolic subgroups
`P = MN` of `G`, with a Levi factor `M` and unipotent radical `N`. The
statement quantifies over all cocharacters `χ` and uses the dynamic subgroups
`P(χ)(F)`, `Z(χ)(F)` and `U(χ)(F)`, with the published decomposition
`P(χ)(F) = Z(χ)(F) ⋉ U(χ)(F)` (Conrad–Gabber–Prasad, Proposition 2.1.8(2)).
For connected reductive `G`, the parabolic `F`-subgroups are exactly the
`P_G(χ)` (Conrad–Gabber–Prasad, Proposition 2.2.9). Renard V.3.1 (printed
p. 110) obtains the Levi factors of `P` as the centralizers `M = Z(G, A)` of
the split components `A` of `P`. Matching every source pair `(P, M)` with some
`(P(χ), Z(χ))`, and `N` with `U(χ)`, is a structural comparison. The Library
does not yet prove it. Nor does it prove that the subspace topology on
`Z(χ)(F)` is the point topology of the Levi as a reductive group. Both belong to
the algebraic-groups programs, and this statement claims neither. The Markdown
of [`PrerequisiteStatements`](PrerequisiteStatements.md) describes the same
scope for the whole finite-length target.

## Provenance

The statement is the source Lemme, expressed through the dynamic parabolic
presentation and the actual Library functor and predicates described above. No
hypothesis is added and no case is dropped. Cocharacters with `P(χ) = G`
correspond to the parabolic subgroup `P = G` of the source.

Renard's proof, not formalized here, takes two steps. For a supercuspidal
`τ`, finite length is Théorème VI.5.4 (printed p. 173). In general, `τ` embeds
into some `i^M_{P'}(ρ)` with `ρ` irreducible supercuspidal on a Levi factor
`M'` of `M` (corollary of VI.2.1, from printed p. 137). Exactness of `i^G_P`
(VI.1.2 Proposition, printed p. 136) and transitivity
`i^G_P i^M_{P'} = i^G_{P'}` (VI.1.4, printed p. 136) then make `i^G_P(τ)` a
subrepresentation of a finite-length representation. These are
representation-theoretic proof obligations, not premises of this statement. A
proof by another route must still prove exactly this statement.

## Relation to other targets

- The whole target `DynamicInductionFiniteLengthStatement`
  (`PreservesFiniteLength` of the same functor, same binders) is not revised
  or duplicated here. Its exact proof task `174d2de0-fa21-41b4-b091-f1b86481790b`
  (Worker 717) keeps its ownership.
- The conclusion here has exactly the shape of the hypothesis `hirr` of
  `Langlands.SmoothRep.preservesFiniteLength_of_irreducibles`
  (`Smooth/FiniteLengthInduction`) for this functor. Together with
  `DynamicInductionExactnessStatement`
  (`Aubert/General/DynamicInductionExactnessStatement`), it gives the whole
  target by
  `SmoothRep.preservesFiniteLength_of_irreducibles _ (hx F G hG χ hU) (hirr F G hG χ hU)`
  after the same instance prelude. The author checked this composition
  privately; it is not part of this module.
- The opening paragraph of Renard VI.6.2 states the extension from
  irreducibles to all finite-length representations. That extension is the
  whole target's concern, not this module's.

## Sources

- D. Renard, *Représentations des groupes réductifs p-adiques* (French
  version dated 9 July 2026),
  `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c` (PDF page
  = printed page + 6): VI.6.2 Lemme and proof, p. 178; VI.1.2 (VI.1.2.1),
  p. 135; VI.1.2 Remarque, Proposition, Remarques and (VI.1.2.3), p. 136;
  VI.1.4, p. 136; VI.2.1, from p. 137; VI.5.4, p. 173; II.3.7, p. 47; V.5.4
  Lemme, pp. 126–127; V.5.2(iii), p. 123; V.3.1, p. 110; V.1, p. 103; V.2.1,
  p. 104; III.1.4, p. 60; A.VI.3, p. 263.
- B. Conrad, *Weil and Grothendieck approaches to adelic points* (2011),
  `conrad-2011-weil-grothendieck-adelic-points`: Proposition 2.1, printed
  pp. 2–3.
- B. Conrad, O. Gabber and G. Prasad, *Pseudo-reductive groups*, 2nd ed.
  (2015), `conrad-gabber-prasad-2015-pseudo-reductive`: Proposition 2.1.8(2),
  printed p. 53; Proposition 2.2.9, printed p. 67.
