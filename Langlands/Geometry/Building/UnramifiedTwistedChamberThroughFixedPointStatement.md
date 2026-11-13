# Twisted-stable chambers through a twisted-fixed point over the maximal unramified extension

This module states `UnramifiedTwistedChamberThroughFixedPointStatement`. Take the building
over the maximal unramified extension and a Galois action twisted by a finite-level cocycle.
The statement says that every point fixed by this twisted action lies in the closure of a
chamber stable under it. Nothing in this module is proved.

It is the residual (special-fibre) step of the route to `UnramifiedTwistedChamberStatement`.
That route first obtains a point fixed by the twisted action, then a twisted-stable chamber
through it. The present statement is the second step. Together with a twisted-fixed point it
gives `UnramifiedTwistedChamberStatement` immediately, because its conclusion contains the
conclusion of that statement for the same data.

## Statement

The data are exactly those of `UnramifiedTwistedChamberStatement`. Let `F` be a
nonarchimedean local field (at universe `u`), `K = inertiaFixedField F` its maximal unramified
extension inside the separable closure, `Γ = Aut(K/F)` (`K ≃ₐ[F] K`) and
`G_K = baseChanged F K G`. The proposition quantifies over

- an `F`-group scheme `G` with `IsConnectedReductive G`;
- a commutative `F`-group scheme `T` with a homomorphism `iT : T → G` whose scalar extension
  `T_K → G_K` is a maximal `K`-split torus (`hiT`);
- an equipollence class `D` of valuations of the root datum of `(G_K, T_K)` for the order of
  the normalized valuation of `K`, a centralizer datum `C` of `T_K`, axiom V 6 for `D` and `C`
  (`h6`), and the stability of `D` under the coefficient action of `Γ` (`hD`);
- a map `c : Γ → G(K)` with `c (σ * τ) = c σ * σ(c τ)` for all `σ, τ`, where
  `σ(g) = rationalConjugate F K G σ g`, and a finite-dimensional intermediate field `E` of
  `K/F` with `c σ = 1` for every `σ` in the fixing subgroup of `E`.

Write `B = UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6`, with `hGK` the connected
reductivity of `G_K` from `connectedReductiveFieldExtensionStatement`. Write
`action σ = (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).action σ` for the
coefficient action of `σ` on the reduced building `B.ReducedBuilding`. The twisted action of
`σ` is `z ↦ c σ • action σ z`, as in `UnramifiedTwistedChamberStatement`. Let `Ψ` be
`B.affineRoots`, the affine roots on the apartment `B.Apartment`.

The proposition asserts the following. Let `y` be a point of `B.ReducedBuilding` with
`c σ • action σ y = y` for every `σ ∈ Γ`. Then there is a subset `Y` of `B.ReducedBuilding` such
that:

1. `Y` is a chamber of `B` (`B.IsChamber Y`);
2. `(fun z => c σ • action σ z) '' Y = Y` for every `σ ∈ Γ`;
3. there are `g ∈ G(K)` and apartment points `x₀`, `x` with
   - `ψ x₀ ≠ 0` for every `ψ ∈ Ψ`, so that `AffineRootSystem.facet Ψ x₀` is a chamber of the
     apartment;
   - `Y = (fun z => g • B.apartmentMap z) '' AffineRootSystem.facet Ψ x₀`;
   - `x ∈ AffineRootSystem.facetClosure Ψ x₀`;
   - `g • B.apartmentMap x = y`.

Clause 3 says that `y` lies in the closure of `Y`. The closure is taken in the translated
apartment `g · A` through one presentation of `Y` as a translate of an apartment chamber.
`facetClosure Ψ x₀` is the closure of the facet of `x₀`. It is given by the sign formula of
the corrections to KP Proposition 1.3.35: `x` lies on every root hyperplane through `x₀` and on
the closed side containing `x₀` of every other one. Since `x₀` lies on no root hyperplane, this
is the closed chamber. Clause 1 follows from clause 3 by the definition of
`IntegerValuationBuildingData.IsChamber`; it is stated separately so that clauses 1 and 2 are
literally the conclusion of `UnramifiedTwistedChamberStatement`.

For `c = 1` the statement says: every `Γ`-fixed point lies in the closure of a `Γ`-stable
chamber.

## Source

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), with `k = F`, `K` its maximal
unramified extension, `f` the residue field of `k` and `f̄` the algebraic closure of `f`, which
is the residue field of `K`:

- Proposition 9.10.1, proof of (4) ⇒ (1) (printed p. 381, PDF p. 412). Let `F` be a `k`-facet.
  By Axiom 4.1.22 (printed pp. 163–164, PDF pp. 194–195), the `f̄`-Borel subgroups of `G_F^0`
  are in bijection with all the `K`-chambers whose closure contains `F`. This bijection is
  `Γ`-equivariant. A Borel subgroup of `G_F^0` defined over `f` is fixed by `Γ`, so it
  corresponds to a `Γ`-invariant `K`-chamber whose closure contains `F`. Such a Borel subgroup
  exists when `G_F^0` is quasi-split over `f`.
- Proposition 9.10.4 (printed p. 382, PDF p. 413). If `dim(f) ≤ 1`, which holds for the finite
  residue field of `F`, then `G_F^0` is quasi-split for every facet `F` of `B(G)`. The proof
  applies Theorem 2.3.3(2) (printed p. 79, PDF p. 110), Steinberg's theorem that connected
  reductive groups over a field of dimension at most one are quasi-split.
- Proof of Theorem 10.6.1 (printed p. 397, PDF p. 428). For a cocycle `c` of `Γ` in `G(K)`, the
  twist `_cG` has the same building `B` over `K`, with the twisted action `x ↦ c(γ) γ(x)`. The
  proof applies Proposition 9.10.4 to `_cG`.

A point `y` fixed by the twisted action is a point of the building of `_cG` over `k`. It lies
in a `k`-facet `F` of that building. Propositions 9.10.1 and 9.10.4 applied to `_cG` and `F`
give a twisted-invariant `K`-chamber whose closure contains `F`, hence `y`. The finiteness
hypothesis on `c` says that `c` is constant on the cosets of an open subgroup of `Γ`. So `c` is
continuous and `_cG` is a `k`-form of `G`, to which the source applies.

## Provenance

This is a derived statement, not a numbered result of the source. It is the argument of
Proposition 9.10.1, (4) ⇒ (1), combined with Proposition 9.10.4. Both are applied, as in the
proof of Theorem 10.6.1, to the twist `_cG` and to the `k`-facet of a given twisted-fixed point.
It is formulated with the Library's supplied `Γ`-stable apartment class `D` and its coefficient
action, as in `UnramifiedTwistedChamberStatement`, not with the constructed building of `_cG`.
The supplied torus is only assumed to have a maximal `K`-split scalar extension `T_K`; it is not
assumed to contain a maximal `F`-split torus, so it need not be a special torus in the sense of
KP 9.2.2 (printed p. 326, PDF p. 357). Neither Borel subgroups nor the special fibre `G_F^0`
appear in the statement. The proposition only records the conclusion of the source argument. It
does not assert that the data `D`, `C` exist, nor that a twisted-fixed point exists.
