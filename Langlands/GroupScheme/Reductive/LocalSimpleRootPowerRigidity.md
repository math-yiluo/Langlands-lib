# Homomorphism rigidity from simple-root power formulas

This internally derived module combines the actual opposite-root comparison
in `LocalOppositeRootRigidity` with the Weyl-generator homomorphism
extensionality theorem in `SplitHomomorphismRigidity`. It proves a conditional
local comparison for actual group morphisms. Construction of its power
formulas and their positive unit coefficients remains an explicit obligation;
the full isogeny torus-conjugacy theorem is not asserted here.

`OppositePower.HasPowerFormula.maps_eq` states that two homomorphisms with the
same formula on the same actual root map agree after composition with that
map. It requires neither an invertible coefficient nor a positive degree.
The proof compares their root points on every scheme test and uses actual
root-point extensionality.

`LocalSplitCell.HasSimpleRootPowerFormulas P Q b u v e f c d q` is a proposition
over a commutative ring `R`. The root data `P,Q` have index types `J,J'`, `b` is a
base for `P`, `u,v` are supplied families of actual additive-group maps, and
`e : J → J'` chooses the target root index. For every simple root `a` of `b`,
it requires the all-test formula for `f` from `u a` to `v (e a)` with coefficient
`c a : Rˣ` and degree `q a`, and the formula from the corresponding negative
map to the target negative map with arbitrary coefficient `d a` and the same
degree. The negative index is the root's self-reflection. This predicate
does not itself assert that the maps are root parametrizations, that `e`
comes from a root-datum isogeny, or that the degrees are positive.

`hom_ext_of_simpleRootPowerFormulas` assumes a commutative local ring, affine
reductive source and target groups, closed fibrewise maximal coordinate split
tori, supplied fibrewise root data, and actual simple and negative-simple root
parametrizations in both supplied families. The source family's Weyl points
realize the simple reflections. The two homomorphisms have the same torus
map and satisfy `HasSimpleRootPowerFormulas` with common `c,q`, possibly
different negative coefficient families `d,d'`, and positive `q` on all simple
roots. It concludes equality of the actual homomorphisms.

For each simple root, the proof uses
`opposite_maps_eq_of_powerFormulas` to obtain equality on its negative map.
The positive restrictions agree directly by their shared formulas. Evaluating
the negative equality at minus one gives equality on the negative Weyl
generators. The source root datum is finite and reduced by its fibrewise
specification, so each root has a simple-reflection word. The existing
`hom_ext_of_weylGenerators` propagates equality through these words and uses
the actual full-root open cell in the reductive source to conclude equality.

`hom_ext_of_chosenSimpleRootPowerFormulas` specializes this result to the
Library's `simpleRootFamilyLocal` in both groups. A target base and the
assumption that `e` sends source simple roots into its simple roots allow the
two specifications of those chosen families to supply all parametrization and
source Weyl hypotheses. No reducedness assumption on `R` is used.
