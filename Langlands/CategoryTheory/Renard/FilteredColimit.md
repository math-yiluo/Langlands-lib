# Renard A.IV.2: the concrete directed quotient

This definition unit implements the final concrete abelian-group construction
in David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, Appendix A.IV.2, printed page 258 / PDF page 264.
The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original direct-system setup on printed page 257 / PDF page 263 and the
construction on PDF264 were read in full. The supplementary author errata
`renard-2010-corrections-complements`, PDF18–19, correct the old edition's
word “limit” to “colimit”; the governing 2026 text already incorporates it.
No project source-errata file was present at the inspected Library base.

The namespace is `Langlands.Renard.FilteredColimit`. The inputs are a partial
order `I : Type uI` with the source's pairwise-upper-bound condition
`IsDirectedOrder I`, abelian groups `G i : Type uG`, and additive transition
maps `f i j h`. The actual `DirectedSystem` laws state that self transitions
are identities and successive transitions compose. There is no injectivity,
finite-generation or finite-index premise. The universes `uI` and `uG` are
independent.

## Actual objects and intrinsic laws

`Carrier G f` is an abbreviation for Mathlib's `DirectLimit G f`, literally
`Quotient (DirectLimit.setoid f)` on `Σ i, G i`. Its relation says that two
representatives become equal at a common later stage. It is not a predicate
standing for an unknown colimit, nor a quotient of a direct sum.

`classOf` inserts a representative. `classOf_eq_iff` exposes the defining
eventual-equality relation, `classOf_transition` identifies a representative
with each of its forward images, and `exists_classOf` gives a representative
of every quotient element. These are direct specializations of the native
quotient relation and representative API.

With `Nonempty I`, the native `AddCommGroup` instance equips `Carrier G f`
with its operations. `of G f i` is the canonical additive homomorphism;
`of_apply` identifies its value with `classOf`. `zero_eq_classOf`,
`classOf_add` and `neg_classOf` compute zero, addition at any supplied common
upper bound, and negation. Thus the operation formulas are independent of
the representatives and of the common upper bound, since they compute the
already well-defined native operations. `of_comp` gives equality of the
canonical homomorphisms after every transition.

`diagram G f` is the actual functor from the ordered category `I` to
`AddCommGrpCat.{max uI uG}`. Each component is
`ULift.{uI} (G i)`; the transition lowers its input, applies `f i j h`, and
raises its output. The lift reconciles the independent universes with the
quotient carrier in `Type (max uI uG)`. It changes no underlying group or
transition up to the explicit additive equivalence `AddEquiv.ulift`.
The functor laws follow from the two `DirectedSystem` laws.

For a nonempty index, `cocone G f` has vertex the actual quotient group.
Its legs lower the lifted factors and apply `of`. Naturality is precisely
`classOf_transition`. `lift G f g hg` is an actual additive homomorphism
to any abelian group `H : Type uH` from a compatible family `g` on the
original components. Its function is native quotient recursion, and
`lift_classOf` computes its value on a representative. The target universe
`uH` is independent of both input universes.

## Empty-index boundary

Renard displays only pairwise directedness. That condition permits an empty
ordered set, but its displayed disjoint union is then empty and cannot
carry a group identity. `carrier_isEmpty` proves this for the literal
quotient, without assuming `Nonempty I`. This is an internal diagnosis of
the construction's missing nonemptiness premise, not an author-issued erratum.

`emptyCocone G f`, under `IsEmpty I`, instead has the singleton abelian group
as its vertex and the vacuous family of legs. This is the correct candidate
for the empty categorical colimit. A later statement/proof unit must verify
both cocones' universal properties and the source's eventual-zero
consequence. This unit does not assert those theorems. The already published
arbitrary-category ordered-system statements retain their original
unrestricted index scope.

## Reuse and provenance

The implementation reuses Mathlib at commit
`5ed2965256430c3649e86755f9576b54eca72435`:
`Mathlib/Order/DirectedInverseSystem.lean` supplies the actual setoid,
quotient, transition, representation and recursion laws;
`Mathlib/Algebra/Colimit/DirectLimit.lean` supplies its algebraic instances
and operation/recursion formulas. `Mathlib/Algebra/Group/ULift.lean` supplies
the additive universe comparison. `Mathlib/Algebra/Category/Grp/Zero.lean`
supplies the ambient additive-group category and the singleton group.
The short Lean laws above expose these constructions directly; the remaining
universal-property and eventual-zero assertions are reserved for separate units.
The exact native source citations are:

- `mathlib-directed-inverse-system-5ed296525643`, SHA256 `dfa51418e1841cbd7e9bdf3db469f9f6c5a06c966b376c193f55f98b6c5340d9`; lines 67–279: DirectedSystem, DirectLimit.setoid, quotient, representatives, transition laws, and lift.
- `mathlib-algebra-colimit-direct-limit-5ed296525643`, SHA256 `58ce3acade8dc0f9fcba9e7b1084ac58549612289fe5a68eeabdcab23d4c6b8b`; lines 59–305: generated additive instances, zero_def, add_def, neg_def, lift_zero and lift_add.
- `mathlib-algebra-group-ulift-5ed296525643`, SHA256 `8896514ab2df99b9cd7d64495246397f55df9e8d639d2e712ae37cbedda5ff00`; lines 27–121: ULift group instances and the additive AddEquiv.ulift.
- `mathlib-algebra-category-grp-zero-5ed296525643`, SHA256 `cc36f4407477cfc0ca7a251a3bc9ed1d2f7197c82aee17c272953904c2d57bd3`; lines 60–91: additive commutative-group zero-object construction using PUnit.

Worker 709 implemented this adapter. Worker 6 contributed the prior
source-scope reconciliation and the requirement to retain the concrete
filtered-colimit and empty-index obligations after the general
ordered-system results. See the
[A.IV progress map](../../../../notes/renard/limits-colimits-progress.md)
for those complementary published results and their remaining boundaries.
