# Compact-open sheaf characterization

This module proves `CompactOpenSheafCharacterizationStatement`, Renard
(9 July 2026), II.2.4, Proposition, printed page 38 / PDF page 44, source
`renard-2026-representations-groupes-reductifs-padiques`.

The common group is constructed inside the published group of global locally
represented families of original stalk germs. Its elements vanish outside some
compact open. This condition is closed under addition by taking the union of
two compact opens, and under negation using the same open. In particular the
carrier lies in `Type (max u v)`, without identifying or restricting the original
space and value universes.

For a compact open `U`, the subgroup `supported U` consists of those elements
vanishing outside `U`. An original section over `U` defines a global germ
family: take its germ at each point of `U` and zero elsewhere. Inside `U` the
section itself is a local representative. Outside `U`, choose a basis open
contained in the open complement and use its zero section. This proves local
representability and gives `extendHom`.

The published `sheafSectionGermsBijective` supplies the essential descent step.
It gives injectivity because equality of extensions implies equality of the
original germs on `U`. For surjectivity, restrict a supported global germ
section to `U`, descend to an original section, and compare its extension
pointwise. `equiv` is the resulting additive equivalence with the specified
extension map.

Monotonicity follows because vanishing outside `U` implies vanishing outside
every larger open. Exhaustion is exactly the defining existence of a compact
open bound. For an element supported in `U ⊆ V`, naturality of original germs
under restriction shows that restricting its section over `V` and extending
from `U` fixes the element. On `V ∖ U` all germs vanish; injectivity of the
original section-to-germs map then gives the zero section.

These helper constructions are internal derivations of the Proposition. The
formal target asks for a common group with the four specified properties, and
does not require identifying it with a preselected compact-section carrier.
The implemented proof uses only this bounded-support description and proves
all the exact clauses of the published statement.
