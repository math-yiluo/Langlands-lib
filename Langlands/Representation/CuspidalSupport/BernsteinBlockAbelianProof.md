# Abelian Bernstein blocks in every carrier universe

Author: Worker 167, Task 5313 (`03088b22-a403-46ae-a6ed-6dea22f5472a`).

`Langlands.CuspidalSupport.bernsteinBlockAbelian` proves the exact published
`BernsteinBlockAbelianStatement`. Every field, group, topology, standard-family
and inertial-class parameter is introduced unchanged. The field universe `uF`
and carrier universe `uV` remain independent.

The published block predicate requires every irreducible actual subquotient
`π` to satisfy `IsBernsteinInertialSupport` after the specified
`SmoothRep.universeLift.{uF}`. It is therefore definitionally
`SmoothRep.irreducibleSubquotientsProperty` for that lifted support predicate.
The published theorem
`SmoothRep.irreducibleSubquotientsSubcategory_abelian` gives the abelian
structure on exactly this full subcategory. Its equality with
`Preadditive.fullSubcategory` is definitionally the equality with the
inherited preadditive instance required by the target.

The generic theorem proves the constituent condition is a Serre class:
actual subquotient transitivity gives subobject and quotient closure, and
the actual irreducible-subquotient dichotomy gives extension closure.
Finite products stay in the class, so the inherited full-subcategory
construction supplies its abelian structure. This application uses no
Bernstein decomposition, support-uniqueness, finite-length or admissibility
premise.

Source: David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, VI.7.2, remark after the proof of the
decomposition theorem, printed p.184 / PDF p.190. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 167 read VI.7.2 at PDF pp.187–190. The source deduces abelianness
from closure under subquotients; Lean makes the required finite additive
and extension closure explicit through the published generic theorem.

This proves only the abelian-block conjunct of
`BernsteinDecompositionStatements`. The decomposition and split-subrepresentation
conjuncts remain separate obligations.
