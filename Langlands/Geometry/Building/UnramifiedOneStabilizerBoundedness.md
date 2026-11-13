# Boundedness of one-stabilizers over the unramified field

This module states the boundedness half of Kaletha--Prasad, *Bruhat--Tits Theory: A New
Approach* (`kaletha-prasad-2023-bruhat-tits-new-approach`), Theorem 4.2.15(1), printed
p. 173 / PDF p. 204, for the actual maximal unramified field. It also states two
unproved input propositions and proves that they imply it. The setting is exactly that
of the published target `MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement`:

- `F` is a nonarchimedean local field;
- `inertiaFixedField F` is its maximal unramified extension `K`;
- `G` is a group scheme over `K` with affine structure morphism;
- `C : BuildingData F G` is supplied building data over `K`, that is,
  `IntegerValuationBuildingData (valuation F) G` for the constructed integer-valued
  valuation `valuation F` of `K`;
- algebraic boundedness (`IsAlgebraicallyBounded`, KP Definition 2.2.1) is taken for the
  valuative relation `ValuativeRel.ofValuation (fixedFieldValued F).v` on `K`, the
  relation the target prescribes.

All three propositions are universe-polymorphic in the universe `u` of `F`.

## Statements

- `OneStabilizerBoundedStatement`: for every such `F`, `G`, `C` and every point `y` of
  the reduced building `C.ReducedBuilding`, the one-stabilizer
  `C.oneStabilizer y = G(K)^1 ∩ G(K)_y` is an algebraically bounded subset of `G(K)`.
  KP uses this, for vertices, in the proof of Theorem 4.2.15(1): Axiom 4.1.2 says the
  group `G(k)^1_y` is bounded. Here it is stated for every point, not only vertices.
- `CentralizerNormOneBoundedStatement` (input): for every such `F`, `G`, `C`, the image
  `j(Z(K)^1)` in `G(K)` is algebraically bounded. Here `Z = C.centralizer.Z` is the
  centralizer of the maximal split torus `S`, `j = C.centralizer.j` is its inclusion in
  `G`, and `Z(K)^1 = characterValuationKernel (valuation F) Z` is its norm-one subgroup.
  This is the derived input replacing KP's use of the boundedness of `Z(k)^0` in
  Corollary 7.3.14. In KP it follows from Remark 2.6.18, printed p. 103 / PDF p. 134:
  `G(k)^1` is bounded when `G_der` is anisotropic, which holds for `Z = Z_G(S)`. For
  tori this is Proposition 2.5.8, printed p. 88 / PDF p. 119.
- `ZeroRootFiltrationBoundedStatement` (input): for every such `F`, `G`, `C`, every point
  `x` of the apartment `C.Apartment` and every relative root `a ∈ relativeRoots C.i`, the
  depth-zero filtration subgroup `U_{a,x,0} = C.filtration x a 0` of the root group is
  algebraically bounded. KP uses the boundedness of the groups `U_{a,x,f}` in the proof
  of Corollary 7.3.14, printed p. 251 / PDF p. 282. For supplied building data it is an
  obligation about the supplied apartment class, which this module does not discharge.

## Proof of the reduction

`oneStabilizerBounded_of_centralizer_of_zeroRootFiltration` proves
`OneStabilizerBoundedStatement` from the two inputs. After introducing `F`, `G`, `C`, `y`
and the prescribed valuative relation, it applies the generic theorem
`IntegerValuationBuildingData.isAlgebraicallyBounded_oneStabilizer` from
`Langlands.Geometry.Building.IntegerValuationOneStabilizerBounded`. That theorem holds over
any field with an integer-valued valuation and any valuative relation. Its two hypotheses
are the instances of the two input statements for this `F`, `G` and `C`.

The two input statements are not proved here. This module does not prove
`OneStabilizerBoundedStatement` outright, and it does not prove the maximality target.
