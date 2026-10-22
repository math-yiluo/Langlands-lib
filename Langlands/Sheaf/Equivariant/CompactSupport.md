# Compact support under a moving-space action

Author: Worker 13.

This development connects the actual transport presheaf of the companion
modules to the stalk support in `Langlands.Sheaf.CompactSupport`.
For a group acting on a topological space, with every individual group
operator continuous, restriction of a transported section to a translated
open equals transport of its restriction to the original open.

The proof first characterizes zero germs by actual vanishing on an open
neighborhood. It transports that neighborhood and its zero section by the
inverse-labelled arrow. Consequently the support of `g • s` lies in the
image under `g` of the support of `s`. A continuous image of a compact set
is compact, and the support is closed by the previously constructed stalk
argument. Thus every group operator preserves the compact-support submodule.
Applying the same argument to the inverse operator proves the exact support
identity `support(g • s) = g • support(s)`.

`representation` restricts the actual global representation to that submodule.
The identity and multiplication laws are proved by the underlying action laws
and subtype extensionality. Equivariant sheaf morphisms induce intertwiners on
compact sections by their naturality for the inverse-labelled global arrows.
`functor` constructs compact sections with their representation, and `inclusion`
is the natural equivariant subtype map into all global sections.

These are ordinary-topological constructions motivated by Berkovich,
*Etale equivariant sheaves on p-adic analytic spaces*, unfinished 1995–1996
manuscript, section 1.4 p.7 (section transport) and section 1.5 p.11
(support by nonzero germs and compact sections). Worker 13 read those
original passages. The analytic site and smoothness of the resulting
section representation remain distinct obligations.

The space, ring and module carriers have universe `u`, and the group has
independent universe `uG`. The group needs no topology; continuity of each
individual point operator is supplied by `ContinuousConstSMul G X`.
No sheaf property is needed for the support-transport argument, which uses
actual colimit stalks of module presheaves.

Source registration:
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

The imported topological equivariance and ordinary compact-support constructions
are present in Library commit `30ceb5a0d89d8094c1663fc19f35416519b9a125`.
Their implementation is reused unchanged. The present module supplies the
support-transport argument and its equivariant compact-section functor.
