# Constructed equivariant sheaves of module-valued functions

Author: Worker 13.

Let a group `G` act on a topological space `X`, let `R` be a commutative ring,
and let `ρ` be an actual `R`-linear representation of `G` on a module `M`.
For each open `U`, `FunctionSheaf.presheaf` assigns the module of all functions
from `U` to `M`. No continuity is imposed on those functions.

For a transport arrow from `U` to `V` labelled `g`, its restriction map sends
`s` to the function `x ↦ ρ(g⁻¹)(s(g • x))`. The image of `x` belongs to `V`
by the arrow's containment proof. The map is linear because `ρ(g⁻¹)` is
linear. Identity and composition follow from the group action and
representation laws. In particular, a label-one open inclusion gives
ordinary restriction.

`underlyingIso` identifies the ordinary underlying presheaf of sets with
Mathlib's presheaf of arbitrary functions. `isSheaf` transfers Mathlib's
proved gluing theorem along this isomorphism and the limit-preserving,
isomorphism-reflecting forgetful functor on modules. `sheaf` is consequently
a constructed object of `TopologicalSheaf`, rather than a record postulating
an output sheaf or cohomology group.

`sectionRepresentation` converts the general global-section action to
Mathlib's category `Rep` using its existing equivalence with module-valued
actions. In the function example, `sectionAction_apply` computes the actual
left operator as `s ↦ (x ↦ ρ(g)(s(g⁻¹ • x)))`. This also checks the
inverse-label convention in the transport category.

`FunctionSheaf.map` applies a coefficient intertwiner pointwise. Its
naturality on every transport arrow is precisely the intertwining equation.
`FunctionSheaf.functor` constructs the resulting functor from Mathlib's
category of representations to equivariant sheaves, with identity and
composition proved pointwise. `constantSections` constructs the natural
equivariant map from the coefficient representation to global functions.

This is a derived example for the topological transport-of-sections framework
in the companion files. Its provenance is the compatible section transport
described in Berkovich's unfinished *Etale equivariant sheaves on p-adic
analytic spaces*, section 1.4, printed p.7, before Definition 1.4.1.
Worker 13 read the original passage. The construction here uses ordinary
open subsets and arbitrary functions. It does not assert that this sheaf
is locally constant, smooth, an analytic étale sheaf, or Harris's algebraic
coefficient local system.

Source registration:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

`X` and `M` occupy universe `u`; the group and coefficient ring have independent
universes. There is no topology on `R` or `M` and no continuity or smoothness
assumption on the group action. Formal dependencies are the companion
transport/sheaf modules and Mathlib's function sheaves, module categories and
representations at commit `5ed2965256430c3649e86755f9576b54eca72435`,
Lean 4.34.0.
