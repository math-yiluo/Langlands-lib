# Flat finitely presented families and their relative groupoids

This module implements the objects and arrows of the scheme, proper ambient
specialization of Stacks Project Situation 99.5.1 (Tag 08KA). Fix actual schemes
`X S : Scheme.{u}`, a morphism `f : X ⟶ S`, and any test scheme `T : Over S`.
The underlying space is the published `Picard.relativeSpace f`, namely the
actual fibre product `T.left ×_S X`. Its structure map to the test scheme is
`(Picard.relativeProjection f).app T`.

For any scheme morphism `p : Y ⟶ B`, `IsFamily p M` is the conjunction of
`M.IsFinitePresentation` and `Modules.IsFlatOver p M`. The first is Mathlib's
local finite free presentation condition: on a covering family of opens the
module is a cokernel of a map between finite free module sheaves. It implies
quasi-coherence and finite type. It is not merely a condition on stalks. The
second condition asserts flatness of the actual module stalk at every point
of `Y` over the corresponding local ring of `B`, with scalar action through
`p.stalkMap`. Both predicates are published interfaces. The module proves that
their conjunction is invariant under actual module isomorphisms, using their
published isomorphism transport results.

`Family p` is the full subcategory of `Y.Modules` on this predicate. Its
`forget` functor is fully faithful and retains every module morphism between
families. `ofModule` includes any locally finitely presented module with a
proof of the relative flatness condition. `ofIso` and `ofIsoIso` transport this
structure across actual module isomorphisms. Finite affine sections follow
from the published `Modules.hasFiniteAffineSections_of_isFinitePresentation`,
without assumptions on the scheme's noetherianity or quasi-compactness.

`FamilyGroupoid f T` is the core of the family category for the relative
projection. Its objects retain their actual module sheaves as `M.of.obj`, and
its arrows retain actual isomorphisms, without passing to isomorphism classes.
`FamilyGroupoid.forget f T` is faithful. `FamilyGroupoid.homEquiv` identifies
each arrow type with the type of all isomorphisms of the underlying module
sheaves. Its inverse lifts any such isomorphism to the full subcategory and
then its core. The accompanying equalities identify the forward map with the
forgetful functor on homs and preserve identities and composition.

Proper support need not be an additional object field when `f` is proper.
`FamilyGroupoid.hasProperSupport` proves it for every object of the full slice
`Over S`. The proof supplies the derived finite affine sections to the
published `Modules.hasProperSupport_relativeSpace`. That result constructs
the closed subscheme defined by affine annihilator ideals and proves that its
map to `T.left` is proper: the relative projection is a base change of the
proper map `f`, and the support immersion is a closed immersion. In particular,
this is properness of the scheme-theoretic support, not just a claim about a
closed topological set. `properSupportExists` also exhibits a closed immersion
satisfying the published `IsSchemeTheoreticSupport` condition (the exact
annihilator kernel on every affine open) and having proper composite to the
test base. It uses the published equivalence with this source characterization.
`Family.hasProperSupport` gives the same implication for any proper `p`.

The construction is defined for arbitrary ambient morphisms, and its proper
support conclusions assume only properness of the ambient morphism. It
therefore includes the task's proper, flat, locally finitely presented
specialization and all test schemes, including empty, nonreduced,
nonnoetherian and non-quasi-compact schemes. Ordinary pullback functors,
preservation of relative flatness, and pseudofunctor coherence are separate
units; this module supplies their object and arrow categories.

The original source is the retained and registered Stacks Project Section
99.5, source `stacks-coherent-sheaf-stack-08ka-2026-11-01`, folder SHA-256
`4ac7cc2a6a797cd51c3a793bbf7684229a8f43b69031e852a0681c219ab99078`.
Situation 99.5.1 specifies the object conditions and actual module
isomorphisms; its fixed-test fibres give the groupoids implemented here.
Lemma 99.5.2 motivates the later ordinary-pullback construction. The support
interpretation is explicit in the proof of Lemma 99.5.4. The published
`Modules.SchemeTheoreticSupport` pair records the separate annihilator-support
source correspondence with Stacks Lemma 29.5.4 (05JU) and Definition 29.5.5
(05JV). The full-subcategory and core packaging and the concrete arrow
bijection are internal categorical realizations of these source fibres.
