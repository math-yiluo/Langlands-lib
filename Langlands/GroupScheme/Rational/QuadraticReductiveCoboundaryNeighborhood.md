# Coboundaries near the identity of a connected reductive group over a complex quadratic extension

The module `Langlands.GroupScheme.Rational.QuadraticReductiveCoboundaryNeighborhood` proves
that, for a connected reductive group over a real field and its complex quadratic extension,
the Galois cocycles near the identity are coboundaries. This is the open neighbourhood used at
the real places in the proof of Platonov–Rapinchuk, Lemma 6.28 (printed p. 370), stated there
for a torus, here for a connected reductive group.

## Declarations

- `IsConnectedReductive.isQuasiSplit_of_isAlgClosed`: a connected reductive group over an
  algebraically closed field `M` is quasi-split. It has a Borel subgroup over `M`
  (`BorelExistence.exists_isBorelSubgroup`), which stays Borel over `AlgebraicClosure M`
  (`borelAlgClosedFieldExtensionStatement`).
- `affinePointsBaseChangeMulEquiv_baseChangeCoeffEquiv_eq_rationalPointEquiv`: for a group
  `G` over `K` and a field `M` over `K`, the two identifications of the rational points of
  `G_M` with the coefficient points `G(M)` agree, as ring points.
- `exists_torusCoefficientCoboundaryNeighborhood`: for a torus `T` over `K`, an algebraically
  closed topological field `M` over `K` with a ring isomorphism `M ≅ ℂ` continuous in both
  directions, and any continuous endomorphism `ψ` of `T(M)`, there is an
  open neighbourhood of `1` in `T(M)` whose points `x` with `x ψ(x) = 1` are of the form
  `a ψ(a)⁻¹`. The torus splits over `M`, and the statement is transported from
  `exists_torusPoint_coboundaryNeighborhood`.
- `exists_coboundaryNeighborhood_of_isConnectedReductive`: let `K` be an infinite field,
  `M/K` a quadratic Galois extension with `M` a nontrivially normed, algebraically closed
  field topologically isomorphic to `ℂ`, and `τ ≠ 1` a continuous element of `Gal(M/K)`.
  For a connected reductive group `H` over `K` there is an open neighbourhood `U` of `1` in
  `H(M)` (evaluation topology) such that every `x ∈ U` with `x · τ(x) = 1` is
  `a · τ(a)⁻¹` for some `a ∈ H(M)`.
- `affinePointsBaseChangeMulEquiv_relativeConjugate`: the base-change comparison
  `C(M) ≅ C_K(M)` for a group `C` over `F` and a tower `F ⊆ K ⊆ M` intertwines the relative
  Galois action of `τ ∈ Gal(M/K)` with its Galois action on `C_K(M)`.
- `exists_relativeCoboundaryNeighborhood_of_isConnectedReductive`: the same neighbourhood for
  a connected reductive group `C` over a field `F`, in its coefficient points `C(M)` with the
  relative Galois action `GaloisPoint.relativeConjugate F K M C τ`.

## Proof of the main theorem

Base change makes `H_M` connected reductive, hence quasi-split. Lemma 6.17 in the form of
`exists_quadraticOppositeBorelTorus` (over the infinite field `K`) gives a maximal torus
`t : T ⟶ H` over `K` with `T_M = B ∩ τ(B)` for a Borel subgroup `B` of `H_M`.
`IsQuadraticOppositeBorelTorus.exists_dynamicData` gives a cocharacter `χ` of `H_M` with
centralizer `T_M` such that `τ` carries `U(χ)` to `U(-χ)`; the cocharacter's automorphism is
`τ` because `Gal(M/K)` has two elements. The cell `U(χ) × T_M × U(-χ) → H_M` is an open
immersion (`Dynamic.isOpenImmersion_leviOppositeCell`), hence an open embedding on `M`-points,
and its middle coordinate is continuous.

Let `W` be the torus neighbourhood of `exists_torusCoefficientCoboundaryNeighborhood` for `T`
and `τ`. The set `U` is the image of the cell points whose middle coordinate lies in `W`,
transported to `H(M)`; it is open and contains `1`. If `x ∈ U` and `x τ(x) = 1`, write
`x = u · t(d) · τ(v)` with `u, v` in the positive unipotent coordinates and `d ∈ W`. Since
`τ(x) = x⁻¹` and the coordinates are unique (`exists_leviOppositeCell_coordinates`),
`v = u⁻¹` and `d τ(d) = 1`. Then `d = a τ(a)⁻¹`, and
`x = (u · t(a)) · τ(u · t(a))⁻¹`.

The relative version transports the neighbourhood along
`affinePointsBaseChangeContinuousMulEquiv F K M C`, using that `C_K` is connected reductive
(`connectedReductiveFieldExtensionStatement`) and
`affinePointsBaseChangeMulEquiv_relativeConjugate`.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press, 1994),
source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`. The proof of Lemma 6.28,
printed p. 370, uses an open subset `Δ_v ⊆ T_{L_w}` such that the cocycle given by any
`t ∈ Δ_v` with `t σ(t) = 1` is trivial, and attributes it to Proposition 3.3 (printed p. 113),
the openness of morphisms with surjective differential. Lemma 6.28' (printed p. 383) needs
the same neighbourhood for the reductive part `C` of a parabolic subgroup. The Lean proof does
not use an inverse function theorem: it reduces to the torus case through an opposite-Borel
torus of `H` over `K` (Lemma 6.17 over `K`) and the uniqueness of coordinates in its open
cell, as in the proof of Lemma 6.28 itself.
