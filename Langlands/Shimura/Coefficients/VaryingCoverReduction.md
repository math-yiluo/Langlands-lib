# Power-reduction systems of varying-cover coefficient cospans

Author: Worker 13.

This is an internal construction from actual module quotients,
[functorial equivariant diagrams](../../CategoryTheory/EquivariantDiagramFunctor.md),
[associated cospans](VaryingCover.md), and the canonical comparison in
[CrossCoverReduction](CrossCoverReduction.md).

The inputs are a commutative ring `R`, an ideal `I`, a scheme `X`, a group
functor `D : J ⥤ GrpCat`, and a diagram
`Y : EquivariantDiagram D X.Etale` of actual small-etale objects and compatible
group actions. A coefficient input is
`M : EquivariantDiagram D (ModuleCat R)`. The scheme, ring, groups, and module
carriers share universe `u`; the index-object and index-morphism universes
are independent. No topologies on the groups or modules are required.

For a natural number `n`, write `P_n(M)` for the existing module quotient
`M / (I^n • ⊤)`, retaining its `R`-module structure. The power index includes
zero, and the inverse direction is from `n` to `m` whenever `m ≤ n`.
This power index is independent of the cover/group index `J`.

`coefficientDiagramPowers` postcomposes the existing inverse diagram of
module-quotient functors with `EquivariantDiagram.postcompose`. It is thus
an actual inverse diagram of endofunctors on varying-group coefficient
diagrams. At power `n` and group index `j`, its object is `P_n(M_j)`;
its action sends the class of `x` to the class of `ρ_j(g)x`, and its
coefficient transition sends the class of `x` to the class of the original
transition applied to `x`. The original equivariance equations are preserved
by the quotient functor.

`coefficientDiagramPowerUnit` is the genuine quotient transformation on
the entire diagram. Its compatibility with every power transition is proved
by evaluating the existing module quotient-unit equation at each group index.
`coefficientDiagramReductionFunctor` transposes the power and coefficient
diagram variables. `coefficientDiagramPowerTransition_surjective` proves
surjectivity on each module at each group index by the existing factor-map
surjectivity theorem. It makes no assertion of sectionwise surjectivity for
an associated sheaf.

Fix one arrow `f : i ⟶ j` of `J`, and put `φ = D.map f`. The original
associated cospan is

`A(Y_i,M_i) → A(Y_i,res(φ)M_j) ← A(Y_j,M_j)`.

`etaleAssociatedCoefficientPowerCospans` applies this actual associated-cospan
functor to the coefficient inverse diagram. It produces a functor from
coefficient diagrams to `ℕᵒᵖ`-diagrams of `WalkingCospan` diagrams of sheaves.
At power `n`, its cospan is

`A(Y_i,P_n M_i) → A(Y_i,res(φ)(P_n M_j)) ← A(Y_j,P_n M_j)`.

Every power transition and every map of coefficient diagrams is the image
under the existing cospan functor of its genuine coefficient map. Identity,
composition, and the two cospan-square obligations are inherited from the
composed functors.

Write `Q_n` for the existing sheaf power quotient, obtained by sectionwise
module reduction followed by sheafification.
`etaleAssociatedSheafPowerCospans` instead postcomposes the original cospan
with `Q_n` at every power. Its terms are

`Q_n A(Y_i,M_i) → Q_n A(Y_i,res(φ)M_j) ← Q_n A(Y_j,M_j)`.

Its power transitions come from `Langlands.Sheaf.AdicSystem.powers`.
No identification of these two cospan systems is assumed.

`etaleAssociatedPowerCospanComparison` constructs a morphism from the latter
cospan to the former. At each of its three vertices it is exactly the
canonical `constantAssociatedPowerReductionComparison`. The left-leg
square is its coefficient naturality at `M.transition f`. The right-leg
square is the proved cross-cover reduction square with the identity
restricted coefficient map. Preservation of identity by the module quotient
functor identifies the reduced coefficient map with the required identity.
Mathlib's `cospanHomMk` then bundles the three maps and the two proved squares.

`etaleAssociatedCospanReductionSystemsComparison` assembles these maps into
a natural transformation between the two functors to inverse diagrams of
cospans. Naturality in the power index follows at each vertex from the
proved transition compatibility of the canonical reduction comparison.
Naturality in coefficient diagrams follows from its coefficient naturality,
with group restriction at the common target. The three final formulas
identify its vertex components definitionally.

The provenance is this categorical assembly of the published constructions,
with all intrinsic equations proved from their functor laws and comparison
identities. No new result is attributed to external literature. There is
no finiteness, flatness, completeness, covering, or torsor assumption.
The construction concerns ordinary sheaves and their inverse diagrams.
It neither inverts the right cospan leg nor proves coherence giving inverse
transitions across arrows of `J`. The finite-torsor comparison, actual Harris
cover specialization, smoothness, derived limits, and cohomology remain
separate obligations.
