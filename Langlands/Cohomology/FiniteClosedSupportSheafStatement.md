# Abelian sheaves with finite closed support

`Langlands.Cohomology.FiniteClosedSupportSheafStatement.{u}` is a
Prop-valued definition of a derived proposition. It supplies a target for a
subsequent proof; this file contains no proof of the proposition.

For every `X : TopCat.{u}`, actual abelian sheaf
`F : TopCat.Sheaf AddCommGrpCat.{u} X`, and set `S : Set X`, the
proposition assumes precisely:

- `S.Finite`;
- `IsClosed ({x} : Set X)` for every `x ∈ S`;
- `IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj)`
  for every `x ∉ S`.

The third hypothesis says that the support, defined as the set of points
whose actual abelian stalk is not a zero object, is contained in `S`.
This is the support itself, without taking its closure. The container `S`
may also include points with zero stalk. No new support predicate is defined.

The conclusion is the conjunction of `TopCat.Presheaf.IsFlasque F.obj`
and

```lean
IsZero (F.obj.obj (Opposite.op (⊤ : TopologicalSpace.Opens X))) ↔ IsZero F
```

The first factor is Mathlib's existing flasque predicate: every restriction
morphism is an epimorphism, equivalently a surjective homomorphism for
abelian groups. The object
`F.obj.obj (Opposite.op (⊤ : TopologicalSpace.Opens X))` is the actual
abelian group of sections on all of `X`. The right side of the equivalence
says that `F` is a zero object in the category of abelian sheaves on `X`.
The statement uses Mathlib's existing stalk functor and section evaluation.

The finite and closed-point assumptions ensure that `S ∩ U` is closed in
`X` for every open `U`: it is a finite union of closed singletons. No
separation axiom on `X` is assumed. The quantifiers include `S = ∅` and
the empty space, and impose no nonemptiness, coherence, finite-generation,
module, scheme, or injectivity condition.

The provenance is derived. The support convention is the one in the
Stacks Project, `modules.tex`, Definition `definition-support`, source
lines 470–489, at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. The paragraph preceding
Lemma `lemma-i-star-exact` and that lemma, source lines 549–575, apply
this convention to abelian sheaves and describe abelian sheaves supported
in a closed subset. The retained source is registered as
`stacks-closed-immersion-exactness-a04446e5`, in
`literature/Stacks Project - Exactness of closed-immersion pushforward and vanishing of its higher direct images (source at a04446e5)/modules.tex`.
The finite-closed flasqueness and global-section detection implication is
derived here, rather than quoted as either of those source statements.

The derivation motivating the target is as follows. Given a section on an
open `U`, the opens `U` and `X \ (S ∩ U)` cover `X`. Their overlap has
zero stalks, so the section restricts to zero there. Gluing with zero on
the second open extends the section to `X`. Restricting such extensions
gives every restriction surjection. If the global-section group is zero,
these surjections make every section group zero, so the sheaf is a zero
object. Conversely a zero sheaf has a zero global-section group.
This is a mathematical rationale for the statement, not Lean proof evidence.

The scope is this elementary topological abelian-sheaf proposition.
Scheme cohomology, higher-direct-image support, proper base change, and
Leray assertions require separate statements and proofs.
