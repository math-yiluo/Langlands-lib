# Topology of the actual standard-Levi chamber

The theorem
`Langlands.BruhatTits.Cartan.RenardLeviCones.leviChamberTopology.{u}` proves the
published proposition
`Langlands.BruhatTits.Cartan.RenardLeviCones.LeviChamberTopologyStatement.{u}`
without changing its hypotheses or conclusions. See
[the statement](RenardLeviChamberTopologyStatement.md) for the exact geometric
data and the derived arbitrary-field scope.

The proof chooses a standard cocharacter for `J` by the published
`standardCocharacter` theorem. Its real image vanishes on `J` and is strictly
positive on the remaining simple roots. The published
`standardLeviCentralDirections` theorem identifies the range of the actual
split-component cocharacter map with this root annihilator. Uniqueness of the
compatible factor through the maximal split torus identifies the supplied map
with that range realization, so the standard cocharacter lifts to `V A` and
lies in the chamber. This includes the empty-root case without a separate
nonemptiness premise.

The finite set of restricted simple roots gives finitely many continuous real
linear functionals in `moduleTopology ℝ (V A)`. Their strict positive halfspaces
have open intersection; their nonnegative halfspaces have closed intersection.
For a point `x` in the latter set and a chamber point `y`, the points `x + t • y`
lie in the chamber for every positive real `t` and tend to `x` as `t` tends to
zero from above. This proves the reverse closure inclusion; closedness gives
the forward inclusion. No Hausdorff or finite-dimension premise is used by this
elementary halfspace argument.

The source and exact scope are those of the paired statement: David Renard,
*Représentations des groupes réductifs p-adiques*, French edition of 9 July 2026,
source id `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
V.3.14–V.3.16, printed pp.113–114/PDF pp.119–120, and V.3.21, printed p.116/PDF
p.122. These original pages were reread on 16 November 2026. This proof uses
an alternate implemented route through published standard cocharacters rather
than choosing a fundamental-coweight basis. It proves no lattice partition,
valuation identity or additional existence of a Levi representative.
