# Localization of the block-reversal stabilizer

Author: Worker 330.

This internal algebraic construction composes published equivalences from
`Whittaker.OpenStabilizer`, `Jacquet.LocalizationTransport` and
`Tensor.CharacterLocalization`. It applies over every field `K : Type uK`,
every natural rank `n`, every ordered positive `BlockShape n`, every family
of complex block representations with carriers in an independent universe
`uV`, and every raw additive character `ψ : AddChar K ℂ`.

Put `P = B.parabolic K`, `U = upperUnipotent n K` and
`w = (B.reverseMatrix K)⁻¹`. The acting group is the actual
`openStabilizer B K = orbitStabilizer P U w`. Its coefficient representation
is the external tensor of the original block representations, pulled back
first through `B.leviProjection K` and then through
`stabilizerToInducing P U w`. Its character is the restriction of
`entrywiseCharacter ψ n`. Localization at the top subgroup therefore uses
every element of this actual stabilizer.

`openStabilizerLocalizationEquiv` identifies that quotient with the
`PiTensorProduct ℂ` of the original block quotients, localized at
`upperUnipotent (B.size i) K` with `entrywiseCharacter ψ (B.size i)`.
All quotients are the published relation-span construction with relation
`ρ(u)v - θ(u) • v`. The conclusion is an actual complex linear equivalence.
No smoothness, topology, admissibility, finite generation, character
nontriviality or unitarity is required.

The implementation first converts a family of subgroup elements into the
actual subgroup `Subgroup.pi Set.univ`. Composing this with the published
`openStabilizerEquiv` and the top-subgroup equivalence gives the group
equivalence used by `transportEquiv`. The coefficient equivalence is the
identity. Compatibility of actions follows from
`openStabilizerEquiv_leviProjection`; compatibility of characters follows
from `openStabilizerEquiv_character`. In particular, the original order
and internal coordinates of the blocks are retained, with no character
inversion. The final map is the published
`FiniteTensor.characterLocalizationEquiv`.

`openStabilizerLocalizationEquiv_mk_tprod` states that the class of a pure
tensor maps to the pure tensor of the individual quotient classes. It
follows from the identity coefficient map in transport and the published
pure-tensor evaluation law.

The provenance is internal composition of the three cited Library APIs.
This pair introduces no new literature assertion. It establishes neither
orbit openness nor compact-induction localization, filtration collapse,
or the full induced-localization theorem. Those remain separate inputs
to the parent heredity proof.
