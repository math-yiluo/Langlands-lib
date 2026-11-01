# Checks for actual additive corner induction

These are internal elaboration checks of the accompanying construction, not
additional assertions attributed to Renard. Their governing source and scope
are Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, Chapter I conventions (printed pp.5–7/PDF11–13),
I.2.1–I.2.2 (printed pp.14–16/PDF20–22), and I.3.1–I.3.2
(printed pp.19–20/PDF25–26). The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF1–2, explains the nonunital right-corner issue; the 2026 version governs.

Complete unapplied declaration assignments check the original right action,
its commutation with regular left multiplication, the explicit ordinary-module
adapter, the actual quotient carrier and inherited group, its residual action,
pure tensors and balancing, whole maps and their identity, composition, zero
and addition laws, their additive Hom-group map, and intrinsic nondegeneracy.
They also check the ambient and nondegenerate objects and functors, complete
underlying maps, additive instances and Hom laws, and equality of the whole
composite with inclusion and its original actions and maps.
`ambientFunctorInterface` is a named assignment of the complete, unapplied
`ambientFunctor` declaration to its independently specified functor type;
it is an alias used as the companion entry declaration. Ring and carrier
universes are independent; composition uses three independent carrier
universes. Explicit unequal assignments test the ring both above and below
carrier universes for tensors, maps, both functors and the inclusion equality.

The competing-action section supplies unrelated original left and right
actions on the ambient ring, corner actions on both input groups and ambient
actions on both tensor carriers. The checks pin the selected regular, right
corner, `ofModule`, quotient group and residual structures. Complete underlying
maps remain the published tensor maps with the identity on the ambient ring.

The competing-ring and competing-group section goes further: a second
nonunital ring on the ambient carrier, a second ring on the original corner
carrier, new additive groups and ordinary corner actions on both input
carriers, and new additive groups and residual actions on both tensor carriers
are all locally available. Preliminary assignments verify that typeclass
inference selects those competitors. Fully explicit applications then retain
the original ring, corner ring, input groups, ordinary actions, balancing
actions, tensor groups and residual actions. They check the entire actual
quotient and its residual structure, complete induced maps, intrinsic
nondegeneracy, and the bundled ambient object's original group and action.

The boundary checks show the actual tensor carrier is subsingleton if either
factor is subsingleton, or if the chosen idempotent is zero. In the last case
balancing by the corner unit relates each pure tensor to a tensor with zero
first factor. The same intrinsic nondegeneracy theorem accepts a zero carrier
and a zero ring at independent universes. The explicit example with ambient
ring `ℤ` and zero idempotent shows right multiplication by the corner unit
does not fix `1`; the construction has imposed no false right unit law.

This is an arbitrary-ring additive generalization of the source construction.
Complex scalar comparison, the fixed-part isomorphism and its naturality,
generatedness, quotient comparison, simple-class correspondence and equivalence
remain separate successors. Worker 1187 authored these checks and the intrinsic
local-unit proof used in the core; Worker 633 authored the core construction,
maps and functors.
