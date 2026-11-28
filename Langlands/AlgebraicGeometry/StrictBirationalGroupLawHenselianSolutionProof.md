# Solutions of strict birational group laws over strictly henselian discrete valuation rings

`Langlands.AlgebraicGeometry.strictBirationalGroupLawHenselianSolution` proves
`Langlands.AlgebraicGeometry.StrictBirationalGroupLawHenselianSolutionStatement`.
For a strictly henselian discrete valuation ring `R`, a morphism `X ⟶ Spec R`
as in the statement, and an open `Y` of `X` satisfying the density and
strictness hypotheses for `m`, it constructs a solution of `m` whose domain is
exactly `Y`.

## Restriction and section choices

The morphism `Y ⟶ Spec R` is smooth and separated by restriction. It is
quasi-compact because `X` is Noetherian and surjective by fibrewise density.
The scheme `Y` is reduced and has integrally closed domain stalks by smoothness
over the DVR. The restricted law `n` uses every pair in the original domain
whose inputs and product lie in `Y`. Its domain and both translation images are
fibrewise dense over both projections, by inclusion of the strictness witness.
The restriction lemma also factors every scheme-valued product of `m` with
inputs and output in `Y` through this domain. [Restriction](HenselianBirationalSolution/Restriction.md)

A section can be chosen to hit any prescribed fibrewise dense open of `Y ×_R P`
at a given point of a test scheme `P`. Over the closed point this follows from
rational-point density and smooth Hensel lifting. Over the generic point the
proof finds a generic point of `Y` in the closure of the generic points of
sections, using the DVR stalk at a generic point of the special fibre.
[Section density](HenselianBirationalSolution/SectionDensity.md)

## Gluing and multiplication

The charts consist of the original `Y` and a copy of `Y` for each section.
For two charts with partial translations `τ` and `σ`, form the schematic
closure of the graph of `σ⁻¹ ∘ τ` in `Y ×_R Y`. Associativity extends the
identity `τ(xw) = σ(yw)` to the open of this closure with a right factor `w`
where both expressions are defined. Fibrewise density permits a common `w`
for two lifts with the same coordinate. The identity and cancellation imply
injectivity of each projection. The projections are open immersions by
Zariski's Main Theorem, since they are quasi-finite, separated and of finite
type, and are open immersions on the original dense graph. Closedness of the
graphs extends the transition cocycle and gives separatedness of the result
by the valuative criterion. Smoothness is checked on the chart cover.
[Graph projections](HenselianBirationalSolution/GraphInjective.md),
[gluing](HenselianBirationalSolution/Glue.md),
[separatedness](HenselianBirationalSolution/GlueSeparated.md)

On the original square, choose a section `c` locally so that `w = c⁻¹x`
and `wy` are defined. Send `(x,y)` to the chart of `c` at `wy`. This gives
`μ : Y ×_R Y ⟶ Gl` by dense agreement on the original domain. For the total
square, choose a section chart `d` for the second coordinate and impose the
open condition that `xd` is defined and lies in the domain of the first chart
translation `τ`. The product there is `μ(τ(xd),y)`. Strictness and section
lifting give a cover by these pieces. Dense agreement extends multiplication,
and the identity for triples on a dense open of the cube gives associativity.
[Original square](HenselianBirationalSolution/Mul.md),
[total square](HenselianBirationalSolution/MulBar.md),
[associativity](HenselianBirationalSolution/MulBarAssoc.md)

## Group and solution

To solve `xz = y` locally, put the two points in one section chart and use an
auxiliary section `c` so that the partial-law equations `xr = c` and `cs = y`
are defined. The product of `r` and `s` is the desired solution. Applying this
construction to `ce = c` at the closed point of the base yields a section
`e` over the whole base. By associativity `e` is a right identity on the dense
image of the original right translation by `c`, hence on all of `Gl`. Local
right inverses and associativity give the left identity and two-sided inverse
identities. Uniqueness glues the inverses, and the resulting relative group law
gives a group object in schemes over `Spec R`.
[Local division](HenselianBirationalSolution/Division.md),
[group law](HenselianBirationalSolution/Group.md)

The image of the original chart is fibrewise dense because it meets each chart
along the domain of its partial translation. The charts of sections cover `Gl`
and each factors through `μ`, so the latter is surjective and `Gl` is
quasi-compact. The theorem fills `mul_eq` by factoring any admissible original
product through the restricted domain and applying the original chart product
formula. This verifies the solution on points valued in an arbitrary scheme.
[Assembly](HenselianBirationalSolution/Assembly.md)

## Provenance

Bosch, Lütkebohmert and Raynaud, *Néron Models* (Springer, 1990), §5.2 Theorem 3,
printed p. 117, gives the existence result specialized here to a strictly
henselian DVR. The restriction uses the setting of §5.2 Definition 1 and
Proposition 2, pp. 115–117. The graph and gluing arguments follow the constructions
in §5.3 Lemmas 1–3 and the adjoining translation construction, pp. 120–123,
with §2.3 Theorem 2′, p. 46. The proof glues the section translates simultaneously
and uses section choices from §2.3 Proposition 5, p. 47, and the DVR generic-point
argument above. The two multiplication extensions and local division correspond
to the steps of §5.3 Lemmas 6 and 8, pp. 125–126 and 127–128.

The literature ID is `bosch-lutkebohmert-raynaud-1990-neron-models`, with file
SHA-256 `16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
Printed page `p` is PDF page `p + 7`.
