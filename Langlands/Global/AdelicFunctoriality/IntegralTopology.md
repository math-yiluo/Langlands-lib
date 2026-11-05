# Original module topology of number-field completed integers

This derived helper for Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), Example 4.2, printed p.10, supplies the original integral-ring topology inputs for the local Weil comparison. It concerns number fields in independent universes and every original finite prime above the chosen lower prime.

The completed integer rings are their original valuation subrings, with the inherited topological ring structures. Their open-unit property follows from the open valuation subring in a topological field. The restriction of the canonical completion embedding is continuous by the subtype topology, so its scalar action is continuous.

`integersProjective` derives projectivity of the original upper ring of integers over the lower ring from flatness and finite presentation: the lower ring is Dedekind and Noetherian, and the upper ring is finite and torsion free. `localFinite` uses the canonical integral tensor algebra equivalence and the surjective coordinate projection to derive finiteness of every original upper completed integer ring over the lower one. Compactness of the lower completed integer ring and the generic theorem `compactFiniteModuleIsModuleTopology` identify the original topology of the Hausdorff upper ring with its finite-module topology. Finiteness and torsion freeness over the lower discrete valuation ring then give projectivity.

No tensor equivalence, module finiteness, topology comparison or selected upper-place family is assumed. This helper does not construct a global integral model or prove compatibility with its generic fiber or the global adelic comparison.
