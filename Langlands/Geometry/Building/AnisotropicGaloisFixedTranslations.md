# Galois-fixed translations of the apartment of an anisotropic group

Module `Langlands.Geometry.Building.AnisotropicGaloisFixedTranslations`.

## Contents

Throughout, `k` and `K` are fields with `[Algebra k K]`, `T` is a commutative group scheme over
`Spec k`, and `G` is a group scheme over `Spec k` with `[IsAffineHom G.X.hom]`. Also
`i : T.toGrp ⟶ G`, and `T_K`, `G_K`, `i_K` denote the published base changes along
`algebraBaseMap k K`. The published objects used are:

- `relativeRoots (T := T_K) i_K`: the relative roots of `i_K`, i.e. the nonzero characters of
  `T_K` with a nonzero weight space in the Lie algebra of `G_K`.
- `TranslationSpace (S := T_K) i_K` (module `Langlands.Geometry.Building.KPApartment`): the
  quotient of the real cocharacter space `V(T_K)` by the common kernel `rootAnnihilator i_K` of
  the relative roots. This is the translation space of a KP apartment of `i_K`.
- `galoisRootAction k K i` and `galoisTranslationAction k K i` (module
  `Langlands.Geometry.Building.GaloisTranslationAction`): the actions of `σ : K ≃ₐ[k] K` on the
  relative roots of `i_K` and on `TranslationSpace i_K`, induced by coefficient transport.
- For a KP apartment `D : KPApartmentData i_K ω` with `hD : GaloisStable k K i D` (module
  `Langlands.Geometry.Building.ApartmentGaloisAction`): the actions `galoisAction k K i D hD`
  on the points of `D.Apartment` and `galoisAffineAction k K i D hD` by affine automorphisms,
  whose linear parts are `galoisTranslationAction k K i σ`.

### Orbit sums of roots

- `eval_galoisRootAction_of_fixed w σ hv a`: if the class of `w : V(T_K)` in
  `TranslationSpace i_K` is fixed by `galoisTranslationAction k K i σ⁻¹`, then the root
  `galoisRootAction k K i σ a` takes the same value at `w` as the root `a`.
- `galoisRepresentation_sum_of_stable O hO τ`: if a finite set `O` of relative roots of `i_K` is
  stable under every `galoisRootAction k K i σ`, then the sum of the characters in `O` is fixed by
  `characterLattice.galoisRepresentation k K T τ`.
- `galoisRootOrbit k K i hT a` (a definition, with `[LocallyOfFiniteType G.X.hom]` and
  `hT : IsSplitTorus (T_K).toGrp`): the orbit of the relative root `a` under
  `galoisRootAction k K i`, as a `Finset`. It is finite because the relative roots of a split
  torus are finite (`IsSplitTorus.finite_relativeRoots`). Its API:
  - `mem_galoisRootOrbit`: `β` lies in the orbit iff `galoisRootAction k K i σ a = β` for some
    `σ`.
  - `self_mem_galoisRootOrbit`: `a` lies in its own orbit.
  - `galoisRootAction_mem_galoisRootOrbit`: the orbit is stable under every
    `galoisRootAction k K i σ`.

### Vanishing for anisotropic groups

In the following, `[IsGalois k K]`, `[LocallyOfFiniteType G.X.hom]`, `hG : IsAnisotropic G`,
`hi : IsClosedSubgroup i`, and `hT : IsSplitTorus (T_K).toGrp`. The Galois extension `K/k` may
be infinite.

- `sum_galoisRootOrbit_eq_zero hG hi hT a`: the sum of the characters in
  `galoisRootOrbit k K i hT a` is `0`.
- `eval_eq_zero_of_forall_fixed hG hi hT w hv a`: if the class of `w : V(T_K)` in
  `TranslationSpace i_K` is fixed by `galoisTranslationAction k K i σ` for every `σ`, then every
  relative root `a` of `i_K` vanishes at `w`.
- `eq_zero_of_forall_galoisTranslationAction_eq hG hi hT v hv`: a vector `v` of
  `TranslationSpace i_K` with `galoisTranslationAction k K i σ v = v` for every
  `σ : K ≃ₐ[k] K` is `0`.

### Chamber transitivity

In namespace `KPApartmentData`, with `[Mono i_K.hom.hom.left]`, any `ω : Kˣ → ℝ`,
`D : KPApartmentData (S := T_K) i_K ω` and `hD : GaloisStable k K i D`:

- `mem_rootStabilizer_galoisAffineAction σ`: `galoisAffineAction k K i D hD σ` lies in
  `rootStabilizer D.affineRoots`. The published `galoisAffineAction_mem_rootStabilizer` (module
  `Langlands.Geometry.Building.GaloisIncidentFacets`) states this only when `ω` is the order of
  an integer valuation. This version allows any `ω`.
- `chamberTransitivity_of_isAnisotropic hG hi hT hΨ hirr hc hne hC`: assume
  `hΨ : IsAffineRootSystemWithRankZero D.affineRoots`,
  `hirr : IsIrreducibleRoots D.affineRoots` (KP Definition 1.3.13), `hne : D.affineRoots.Nonempty`,
  and a regular point `c : D.Apartment` (`hc : IsRegular D.affineRoots c`). Assume also
  `[Fintype (simpleAffineRoots D.affineRoots (facet D.affineRoots c))]` and that every
  `galoisAffineAction k K i D hD σ` maps the chamber `facet D.affineRoots c` onto itself
  (`hC`). Then `HasTransitiveSimpleRoots D.affineRoots (facet D.affineRoots c)` and
  `AffineCartan.IsVertexTransitive (chamberCartanMatrix D.affineRoots (facet D.affineRoots c))`.
- `chamberTransitivity_of_isAnisotropic_of_fixed`: the same conclusion when `hC` is replaced by
  `hcfix : ∀ σ, galoisAction k K i D hD σ c = c`.

The module does not construct a Galois-stable KP apartment and does not prove that a
Galois-stable chamber exists. The irreducibility, nonemptiness and affine-root-system hypotheses
on `D.affineRoots` stay explicit.

## Provenance

The module is derived. It supplies the linear-algebra input for one step in the proof of
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Theorem 10.3.1 (printed p. 392,
PDF p. 423). There `G` is anisotropic, `C` is a `Γ`-stable chamber, and `C^Γ = {x}` because the
building of `G` has no facet of positive dimension. In the apartment, two `Γ`-fixed points
differ by a `Γ`-fixed translation vector. So `C^Γ` has at most one point as soon as the reduced
translation space has no nonzero `Γ`-fixed vector, and that is what
`eq_zero_of_forall_galoisTranslationAction_eq` proves. The anisotropy input is the vanishing of
Galois-fixed characters of tori in `G` (module
`Langlands.GroupScheme.Rational.AnisotropicGaloisFixedCharacters`; A. Borel, *Linear Algebraic
Groups*, 2nd ed., §8.14). The orbit-sum argument is internal: it is a standard way to turn a
fixed vector into a fixed character and is not quoted from KP. The chamber-transitivity
corollaries combine this with the module
`Langlands.Geometry.Building.AffineIrreducibleChamberTransitivity`, which is submitted together
with this one. For the vertex statement
behind them, see KP Proposition 1.3.22(6) (printed p. 23, PDF p. 54) and KP 9.2.4.

## Proof notes

- `eval_galoisRootAction_of_fixed`: `RealTorusSpace.eval_galoisCocharacterAction_right` moves
  the transport from the character to the vector, at the cost of inverting `σ`. Applying
  `rootForm a` to the fixed-point equation (`galoisTranslationAction_mk`, `rootForm_mk`) turns
  this into the claim. Here `galoisRootAction_val` identifies the value of the transported root
  as a character.
- `galoisRepresentation_sum_of_stable`: `map_sum`, then `Finset.sum_nbij'` with the bijection
  `galoisRootAction k K i τ` of `O` (inverse `galoisRootAction k K i τ⁻¹`). On each term this is
  `galoisRootAction_val`.
- `galoisRootOrbit` is `(Set.toFinite (Set.range fun σ => galoisRootAction k K i σ a)).toFinset`.
  The `Finite` instance on the relative roots comes from `IsSplitTorus.finite_relativeRoots`, and
  the instances `IsAffineHom` and `LocallyOfFiniteType` for `G_K` are passed explicitly. The
  module proves them for the pullback along `algebraBaseMap k K` (private instances
  `extendedAffineHom`, `extendedLocallyOfFiniteType`). Leaving them to instance search made
  elaboration time out.
- `sum_galoisRootOrbit_eq_zero`: by `galoisRepresentation_sum_of_stable`, the orbit sum is
  fixed by every `σ`. `T` is a torus by `isTorus_of_isSplitTorus_baseChange`, so
  `IsAnisotropic.galoisFixed_character_eq_zero` makes the sum zero.
- `eval_eq_zero_of_forall_fixed`: every root `β = galoisRootAction k K i σ a` of the orbit takes
  the value `a(w)` at `w`, by `eval_galoisRootAction_of_fixed` applied to `hv σ⁻¹`. Evaluation at
  `w` is additive in the character (private lemma `eval_finset_sum`), so the vanishing orbit sum
  gives `card (orbit) * a(w) = 0`. The orbit contains `a`, so its cardinality is positive and
  `a(w) = 0`.
- `eq_zero_of_forall_galoisTranslationAction_eq`: lift `v` to `w : V(T_K)`. By
  `Submodule.Quotient.mk_eq_zero` and `mem_rootAnnihilator`, it suffices that every relative
  root vanishes at `w`, which is `eval_eq_zero_of_forall_fixed`.
- `mem_rootStabilizer_galoisAffineAction`: the inverse of `galoisAffineAction k K i D hD σ` lies
  in `rootStabilizer D.affineRoots` by `galoisAffineFunctional_mem_affineRoots_iff` (module
  `Langlands.Geometry.Building.GaloisAffineRootAction`), and subgroups are closed under
  inverses. This is the same proof as the published integer-valuation version.
- `chamberTransitivity_of_isAnisotropic` is
  `IsAffineRootSystemWithRankZero.chamberTransitivity_of_hom_of_linear` (module
  `AffineIrreducibleChamberTransitivity`) applied to
  `ρ = galoisAffineAction k K i D hD`. Its linear-part hypothesis is
  `eq_zero_of_forall_galoisTranslationAction_eq`, since the linear part of
  `galoisAffineAction k K i D hD σ` is `galoisTranslationAction k K i σ` by definition.
- `chamberTransitivity_of_isAnisotropic_of_fixed`: by `image_facet_transportedRoots` (module
  `Langlands.Geometry.Building.AffineFacetTransport`), the affine map `galoisAffineAction σ`
  sends `facet D.affineRoots c` onto the facet of `galoisAction σ c = c` for the transported
  roots. `transportedRoots_galoisAffineAction` says the transported roots are `D.affineRoots`
  again, so `hC` holds.
