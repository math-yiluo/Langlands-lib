# Functorial cokernel complexes

Author: Worker 13.

This module constructs the iterative cokernel complex of a coaugmentation
`η : 𝟭 A ⟶ T` on a universe-polymorphic abelian category `A`. It uses Mathlib
cokernels in the functor category, so the successive objects, maps and their
functoriality are actual categorical constructions.

Set `Q₀ = Id`, `Cⁿ = Qₙ ⋙ T`, and let `Qₙ₊₁` be the cokernel of the natural
map `Qₙ → Cⁿ`. The differential `Cⁿ → Cⁿ⁺¹` is the cokernel projection followed
by the next coaugmentation. The cokernel equation proves that consecutive
differentials compose to zero. Evaluation gives a functor from `A` to
nonnegative cochain complexes and a map from each original object to degree
zero, whose composite with the first differential is zero.

The recurrence takes the cokernel of the coaugmentation of each residual
object. Berkovich instead describes the next term using the cokernel of the
preceding differential. These give canonically isomorphic residual objects:
the preceding differential factors as an epimorphic cokernel projection
followed by the current coaugmentation, so a map annihilates the differential
exactly when it annihilates that coaugmentation. The code uses the former
recurrence directly; it does not introduce a second complex or claim a
formalized comparison theorem between two implementations.

This is the formal categorical construction underlying Berkovich's Godement
iteration in section 1.5, printed/PDF page 10 of *Etale equivariant sheaves on
p-adic analytic spaces*, the supplied unfinished 1995–1996 manuscript. It is a
derived generalization to an arbitrary coaugmented endofunctor. No assertion
that an arbitrary coaugmentation is injective, or that the constructed complex
is exact or acyclic, is part of this definition. The actual sheaf functor and
scheme specializations are constructed separately in this definition group.

The registered source is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder digest
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The cited member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Worker 13 read the construction in the original. The source's exactness,
softness and compact-support comparison results are separate theorem
obligations, not fields assumed by this construction.

The only external formal dependency is the project's pinned Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, Lean 4.34.0. There are no
project axioms or placeholders. The category's object and morphism universes
are explicit; no finite-dimensionality or coefficient characteristic
restriction is introduced here.
