# Formal etaleness descended from a localized base change

`EtaleLocalizedBaseChangeDescentStatement` is an internal local algebra
interface for the etale slicing proof. Let `D` be a pushout of commutative
algebras `T` and `B` over `A`, and let `C` be a localization of `D` at an
arbitrary submonoid. All displayed algebra structures are compatible with
the indicated scalar towers. The rings may live in five independent universes.

Assume that `A` and `B` are local rings, that `A → B` is local and essentially
of finite presentation in the published Library sense, that `C` is flat
over `A` and faithfully flat over `B`, and that `T → C` is formally
unramified. Then `A → B` is formally etale. The statement does not require
that `C`, `D`, or `T` be local.

This is a derived internal assertion. Faithful flatness reflects the
injectivity tests for flatness and therefore gives flatness of `B` over
`A`. The pushout comparison for Kaehler differentials, its localization
comparison, and faithful flatness give vanishing of the differentials
of `B` over `A`. For a local algebra essentially of finite presentation,
flatness and formal unramifiedness imply formal etaleness: its
residue-field fibre is formally etale by the field criterion, and the
local smoothness criterion gives formal smoothness before combining it
with formal unramifiedness.

These are consequences of Mathlib's tensor, differential, faithful
flatness and local smoothness results, rather than assumptions about a
scheme quotient or source descent theorem. Passing from scheme
pullbacks and stalk maps to these algebra hypotheses is a separate step.
