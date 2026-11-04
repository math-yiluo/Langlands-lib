# Products on actual adelic points from independent arithmetic spreads

`Langlands.Global.AdelicSpreadProductStatement` asserts preservation of
binary products for the actual full-adele point spaces in both arithmetic
cases, at arbitrary common universe `u`. The factors and product have
independently specified finite-type arithmetic models `MX`, `MY`, `MP`,
over three arbitrary finite sets `S`, `T`, `U`, and arbitrary specified
isomorphisms from their actual generic fibers. Finite type means locally
finite type and quasi-compact. Each finite set may be empty.

The field product is any binary fan `c` with its categorical limit proof.
The comparison sends an actual point of `c.pt` to its composites with
`c.fst` and `c.snd`. The source has exactly the existing topology from `MP`
and `eP`; the target has the product of the existing topologies from `MX`,
`eX` and `MY`, `eY`. The comparison defines neither topology. No
compatibility between the three spreads or their isomorphisms is assumed.
No scheme is required to be affine or separated.

For function fields the arbitrary constant field `k` is perfect, as
required by the existing generic-fiber point construction. `F` retains
its specified compatible `k` and `RatFunc k` actions and finite extension
condition `FunctionField k F`; no separability assumption or finiteness of
`k` occurs. The number-field clause uses actual full `Adeles K`, including
every infinite factor. Neither clause assumes local compactness or finite
residue fields.

This is a derived extension of the product compatibility in Brian Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp.8–9, especially the product construction before Corollary 3.7
and Section 4's final-topology discussion. Registered source:
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The unrestricted perfect constants and nonseparated factors are derived
scope, rather than assertions quoted verbatim from Conrad.

The proof route is to enlarge the two factor models to a common finite
place set, take their actual relative product there, and apply the
fixed-model pullback comparison with the terminal model as separated
base. The generic-fiber functor preserves products; its universal property
identifies that model's generic fiber with `c.pt`. Naturality of actual
point homeomorphisms identifies the cone-leg maps. Topology independence
compares this product model with the independently specified model `MP`
and compares the enlarged factor spreads with the original ones.

This file states propositions only. Pullbacks over a nonterminal field
scheme and whole-paper completion are separate obligations.
