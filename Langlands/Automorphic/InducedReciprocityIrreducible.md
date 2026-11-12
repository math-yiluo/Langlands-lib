# Irreducibility of induced reciprocity representations from relative regularity

Author: Worker 5134. Module `Langlands.Automorphic.InducedReciprocityIrreducible`.
Helper lemmas are in namespace
`Langlands.ClassField.Global.InducedReciprocityIrreducible`. The definitions and
main results are in `Langlands.ClassField.Global.RelativeWeilGroup`. The universe
of the number fields is `u`, and `uV` is the carrier universe of
`inducedReciprocityRepresentation`.

Setting: `c` is a fundamental class family, `h : FundamentalClass.Restriction c`,
and `E ⊆ E' ⊆ L` is a tower of number fields with `L / E` Galois. We write
`W_{L/E} = RelativeWeilGroup c E L` and `ξ : HeckeCharacter E'`. The
representation `inducedReciprocityRepresentation c E E' L h ξ` from
`Langlands.Automorphic.WeakInductionAssociationStatement` is
`Ind_{W_{L/E'}}^{W_{L/E}} (ξ ∘ τ_{E'})`. It is induced along the inclusion
`ι = restrictionInclusion c E L E' h : W_{L/E'} → W_{L/E}`.

Mathematical source: Henniart (2000), §3.4, uses the irreducibility of the
induced representation `S(X)`. That irreducibility rests on Harris's regularity
condition (Harris 1998, Definition 2.3; Library
`Langlands.Global.Harris.IsRelativelyRegular`). This module proves the
irreducibility in the Library's model of relative Weil groups.

## Definitions

- `rangeReciprocityCharacter c E E' L h ξ : ι.range →* ℂˣ` is the reciprocity
  character `reciprocityCharacter c E' L ξ` of `W_{L/E'}` (that is
  `w ↦ ξ(transfer w)⁻¹`), composed with the inverse of `ι` on its range
  (`InductionAlong.rangeInverse`). It is the same character, carried to the
  image of `W_{L/E'}` in `W_{L/E}`.
- `inducedReciprocityRepresentationEquiv c E E' L h ξ` is an equivalence of
  representations of `W_{L/E}`. It identifies
  `inducedReciprocityRepresentation.{u, uV} c E E' L h ξ` with
  `FiniteRepresentation.induce ι.range (characterLine.{u, 0} (rangeReciprocityCharacter c E E' L h ξ))`.
  It is induction (`FiniteRepresentation.induceEquivOfEquiv`) of the identity of
  `ℂ` between the two `ULift` carriers of the line.

## Results

The norm helpers below retain independent universes for the two number fields.
The related `Langlands.Global.AdelicFunctoriality` norm formulas in
`Global.Factors.RelativeWeilAssemblyCharacters` use a shared field universe.
The broader helper signatures are retained here.

Archimedean helper lemmas (namespace `InducedReciprocityIrreducible`):

- `completionMap_comp`: for places `τ` of `E`, `w` of `E'` and `p` of `L` with
  `p` over `w` over `τ`, the completion maps compose:
  `E_τ → E'_w → L_p` equals `E_τ → L_p`.
- `ideleNorm_ofCompletion` and `ideleClassNorm_ofCompletion`: the norm of an
  idele (class) concentrated at one archimedean place `q` of `L` is concentrated
  at the place `p` below `q`. Its component there is the local unit norm.
- `fixes_of_comap_eq`: let `E` be totally complex and `σ ∈ Aut(L/E)`. If the
  places `p ∘ σ` and `p` of `L` restrict to the same place of `E'`, then `σ`
  fixes `E'` pointwise.
- `ideleClassNorm_ofCompletion_completionMap`: let `E` be totally complex, let
  `r` be a place of `L` over the place `w` of `E'`, and let `y ∈ E_τˣ`. Map `y`
  to `L_r` and form the idele class concentrated at `r`. Its norm to `E'` is the
  class concentrated at `w` whose component is the image of `y` in `E'_w`.
- `fixes_of_ideleClassNorm_invariant`: let `E` be totally complex and `ξ`
  relatively regular over `E`. If `σ ∈ Aut(L/E)` satisfies
  `ξ(N_{L/E'}(σ a)) = ξ(N_{L/E'}(a))` for every idele class `a` of `L`, then
  `σ` fixes `E'` pointwise.

Main results (namespace `RelativeWeilGroup`):

- `rangeInverse_inclusion`: on `C_L`, the inverse of `ι` on its range sends
  `inclusion c E L b` to `inclusion c E' L b`.
- `rangeReciprocityCharacter_inclusion`: on `C_L` the transported character is
  `b ↦ ξ(N_{L/E'} b)⁻¹`.
- `rangeReciprocityCharacter_exactStabilizer`: let `E` be totally complex and
  `ξ` relatively regular over `E`. Then the image `N` of `C_L` is contained in
  `ι.range`. Moreover an element `a ∈ W_{L/E}` fixes the restriction of the
  transported character to `N` under conjugation by `a⁻¹` exactly when
  `a ∈ ι.range`.
- `inducedReciprocityRepresentation_isIrreducible`: let `E` be totally complex
  and `ξ` relatively regular over `E`. Then
  `(inducedReciprocityRepresentation.{u, uV} c E E' L h ξ).IsIrreducible`.

## Proofs

`completionMap_comp` holds because both sides are continuous ring maps that agree
on the dense image of `E` (`completionMap_algebraMap` and the scalar tower).

`ideleNorm_ofCompletion` compares the two components separately. At the
archimedean place `p'`, the norm is a product over the places of `L` above `p'`
of local norms of `Pi.mulSingle q y`. When `p' = p` only the factor at `q`
remains (`Finset.prod_eq_single`). Otherwise every factor is `1`, since no
place above `p'` equals `q`. The finite component of the norm is `1`.
`ideleClassNorm_ofCompletion` follows through `ideleClassNorm_mk`.

`fixes_of_comap_eq` writes both places with `InfinitePlace.mk_eq_iff`. Then the
two complex embeddings of `E'` are either equal or complex conjugate. In the
first case `σ` fixes `E'` by injectivity of `p.embedding`. In the second case
the restriction to `E` would equal its own conjugate, because `σ` fixes `E`.
So the place of `E` below `p` would be real, which contradicts `E` being
totally complex.

`ideleClassNorm_ofCompletion_completionMap` applies `ideleClassNorm_ofCompletion`.
The extension `L_r / E'_w` has degree one, since `w` is complex (`E'` is totally
complex over the totally complex `E`). So `InfiniteExtension.localNorm_algebraMap`
and `completionMap_comp` give the component.

`fixes_of_ideleClassNorm_invariant` argues by contradiction. Choose a place `p` of
`L` with restriction `τ` to `E`. Suppose `σ` moves an element of `E'`. Then by
`fixes_of_comap_eq` the places `p' = p ∘ σ` (`infinitePlaceEquiv σ p`) and `p`
of `L` restrict to distinct places of `E'` over `τ`. Relative regularity gives
`y ∈ E_τˣ` on which the archimedean components of `ξ` at these two places
differ. Consider the idele class concentrated at `p'` with component the image
of `y`. Galois transport
sends it to the class concentrated at `p` with component the image of `y`
(`ideleClassEquiv_ofCompletion` and
`IdeleGaloisDescentProof.infiniteTransport_completionMap`). Taking norms with
`ideleClassNorm_ofCompletion_completionMap`, the invariance hypothesis then says
that the two archimedean components agree on `y`. This is a contradiction.

`rangeInverse_inclusion` follows from injectivity of `ι` and
`restrictionInclusion_inclusion`. Then `rangeReciprocityCharacter_inclusion`
follows from `reciprocityCharacter_apply` and `transfer_inclusion` (the transfer
on `C_L` is the norm).

`rangeReciprocityCharacter_exactStabilizer`: `N ≤ ι.range` by
`restrictionInclusion_inclusion`, and `N` is normal (`ideleClassSubgroup_normal`).
Suppose `a` stabilizes the character, and put `σ = projection a⁻¹`. The relation
`a⁻¹ · inclusion b · a = inclusion (σ b)` (`RelativeWeilGroup.conjugation`) and
`rangeReciprocityCharacter_inclusion` show `ξ(N(σ b)) = ξ(N b)` for all `b`. So
`σ` fixes `E'` (`fixes_of_ideleClassNorm_invariant`). It therefore comes from
`Aut(L/E')` (`AlgEquiv.ofRingEquiv`). Hence `a⁻¹`, and so `a`, lies in
`ι.range` (`range_restrictionInclusion`). Conversely, for `a ∈ ι.range`,
conjugation by `a⁻¹` takes place inside `ι.range`. A character to the
commutative group `ℂˣ` is invariant under such conjugation.

`inducedReciprocityRepresentation_isIrreducible` applies Mackey's criterion
`GeneralPosition.induce_irreducible_of_exactStabilizer` with `N` and
`H = ι.range`. This gives irreducibility of the induced line in carrier
universe `0`. The equivalence `inducedReciprocityRepresentationEquiv` transfers
it (`CentralEigenspaceSplitting.isIrreducible_iff_of_equiv`).
