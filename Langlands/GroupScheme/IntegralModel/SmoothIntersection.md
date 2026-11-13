# Products and smooth intersections of actual integral group models

This module develops the product and intersection step in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Corollary A.6.6, printed
p. 647 / PDF p. 678. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

`SmoothIntersectionStatement.{u}` is an unproved existence proposition.
Over a Henselian discrete valuation ring with algebraically closed residue
field, it starts from two actual affine flat finite-type models `M` and `N`
of the supplied smooth affine generic group `G`. It asks for an actual
smooth model `L`, compatible homomorphisms from `L` to both original
models extending the identity of `G`, and the literal subgroup equality
`L.integralPoints = M.integralPoints ⊓ N.integralPoints` inside the
original `rationalPoints G`.

The precise target quantifies over `R : Type u` with `[CommRing R]`,
`[IsDomain R]`, `[IsDiscreteValuationRing R]`, `[HenselianLocalRing R]`
and `[IsAlgClosed (IsLocalRing.ResidueField R)]`, a supplied `K : Type u`
with `[Field K]`, `[Algebra R K]` and `[IsFractionRing R K]`, and
`G : GroupScheme (Spec (CommRingCat.of K))` with
`[IsAffineHom G.X.hom]` and `Smooth G.X.hom`. For every
`M N : IntegralModel R K G`, it asks for `L : IntegralModel R K G` with
`L.IsSmooth`, `Nonempty (L.Hom M (𝟙 G))`,
`Nonempty (L.Hom N (𝟙 G))` and the subgroup equality above.
Here each `IntegralModel` includes an actual affine flat group scheme
locally of finite type (hence of finite type, since affine) over `R` and
its specified generic-fibre isomorphism with `G`. The `Hom` compatibility
square is an equality of generic group-scheme homomorphisms through these
specified isomorphisms. Thus the target retains the original models and
their generic identifications.

KP's Corollary A.6.6 says that the intersection of two schematic subgroups
of `X(K)` is schematic, for a smooth affine group `X` over the smaller
field `k`. In its proof, the two subgroups have smooth integral models
over the integer ring `O` of the maximal unramified field `K`. The proof
takes the schematic closure of the generic diagonal in their product,
checks the group structure by flatness on the generic fibre, and applies
Corollary A.6.5 to obtain a smooth model with the same points.

The Lean target is a derived model formulation of that argument. It
generalizes the maximal unramified setting to any Henselian DVR with
algebraically closed residue field, and takes the smooth affine generic
group directly over its supplied fraction field without descent data to
a smaller field. It also allows the two input models to be nonsmooth:
the same proposed route closes the generic diagonal in their product
and then smoothens that closure. The output maps would be composites
of the smoothening map, the closed inclusion and the two product
projections. This describes a proof route, not an implemented existence
proof. The proposition assumes no closure, smoothening, intersection
model, schematicity witness or model comparison; it asserts no universal
property of the resulting smooth model.

The base is strictly Henselian because its residue field is algebraically
closed, hence separably closed; that field is also perfect. In the
source's corrected Chapter 8 setting, the residue field of `k` is perfect
and that of `O` is its algebraic closure, so this covers the original
application. See the Appendix A convention, printed p.593 / PDF p.624;
the opening of §A.6, printed p.645 / PDF p.676; and the corrections,
PDF p.37.

`Hom.comp` implements composition of compatible model homomorphisms.
`product` uses the actual product group scheme over the integral base.
Its generic identification is the existing `baseChangeTensorIso` followed
by the tensor product of the two supplied generic identifications.
Affineness, flatness, local finite type and, when both factors are smooth,
smoothness follow from the corresponding product properties of scheme
morphisms. `productFst` and `productSnd` prove compatibility with the
original generic projections using the monoidal base-change comparison.
`product_integralPoints` proves the exact equality

```lean
(M.product N).integralPoints =
  M.integralPoints.comap (rationalPoints.map (fst G H)) ⊓
    N.integralPoints.comap (rationalPoints.map (snd G H))
```

The forward implication uses the compatible projections' naturality on
integral sections. For the reverse implication, `productPointsEquiv`
combines integral sections of the two factors into a section of the
product; the same equivalence on generic points proves that this section
maps to the originally supplied point. Pulling this formula back along
the original generic diagonal gives
`product_integralPoints_comap_diagonal`, using the two projection
identities. Both equalities concern literal subgroups of the specified
rational-point groups.
`Hom.integralPoints_le_inf` derives the necessary subgroup inclusion
from two supplied compatible generic-identity maps.

These elementary constructions and proofs require only a domain `R`
with specified fraction field `K`; they use no discrete valuation,
Henselianity or residue-field hypothesis. `product_isSmooth` additionally
assumes smoothness of both factors. The stronger base hypotheses occur
only in the unproved existence target.

The registered *Corrections and additions* (2024), source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.37 and 49–50, adds the Chapter 8 perfect-residue-field convention
and changes Appendix A.4, but leaves Corollary A.6.6 unchanged.

These elementary constructions are internal consequences of the
published `IntegralModel` and product APIs. They supply no schematic
closure or smoothening existence proof. In particular, the final
`IntegralModelAxiomsStatement` remains open.
