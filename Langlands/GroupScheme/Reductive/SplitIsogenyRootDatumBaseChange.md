# Root-datum isogenies on extended split-torus lattices

This is a derived transport construction for the split-isogeny realization
argument. It uses the published `SplitRootDatum.baseChange`, its pairing
identity, the actual character and cocharacter base-change equivalences, and
the record `Langlands.LinearAlgebra.RootDatumIsogeny`. It has no additional
literature claim.

Let `k` and `K` be integral domains in an arbitrary common universe, and let
`b : Spec K ⟶ Spec k`. For split tori `T` and `T'`, write `eX`, `eY`, `eX'`
and `eY'` for the integral linear equivalences on their actual character and
cocharacter lattices induced by pullback along `b`.

The helpers `SplitRootDatum.characterFiniteBaseChange` and
`SplitRootDatum.cocharacterFiniteBaseChange` transport finite generation
along these equivalences. The instance `SplitRootDatum.baseChange_isReduced`
transports reducedness: injectivity of character pullback preserves linear
independence of each pair of roots, so dependence after pullback implies
dependence before pullback; the original equality or opposite equality then
pulls back.

For finite reduced root data `P` and `P'` on the actual lattices, with the
finite-generation instances required by the isogeny record on both sides,
`RootDatumIsogenyRealization.rootDatumIsogenyBaseChange` sends an isogeny
`f : RootDatumIsogeny p P' P` to one between the actual base-changed root
data. Its weight map is `eX ∘ f.weightMap ∘ eX'⁻¹`; its coweight map is
`eY' ∘ f.coweightMap ∘ eY⁻¹`. The index equivalence, characteristic-exponent
proof, root factors and their power witnesses are retained unchanged.

The two conjugated maps are injective. Their transpose identity follows by
writing each lattice element as a pullback and applying the published pairing
identity twice together with `f.pairing_apply`. The root and coroot equations
follow from the original equations and integral linearity of the pullback
equivalences. The construction keeps the supplied natural number `p`; a
separate use over fields must identify it with the characteristic exponent of
the extended field where needed.

The theorems `rootDatumIsogenyBaseChange_weight` and
`rootDatumIsogenyBaseChange_coweight` identify the two maps on every pulled-back
lattice element. If an actual torus homomorphism `t : T ⟶ T'` induces the
original weight map, `rootDatumIsogenyBaseChange_torus` proves that its actual
base change induces the transported weight map. This uses surjectivity of
character pullback and its compatibility with precomposition.

This module constructs root-datum transport. It does not assert invertibility
of a graph projection or the split-isogeny realization theorem.
