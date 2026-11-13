# A nondegenerate module with a degenerate completion

Worker 258. This module proves the published
`Langlands.Algebra.LeftLimitNotNondegenerateStatement`.
The source assertion is Renard, *Représentations des groupes réductifs p-adiques*
(9 July 2026), I.1.4, printed page 10 / PDF page 16: the completion need not be
nondegenerate. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The following explicit example is derived internally; the cited passage does
not specify one.

Let `A` be the published algebra `CountableSupportAlgebra.Carrier ℂ ℂ` of
countably supported functions, with pointwise operations, and give `M = A`
its original left regular action. Local units prove that `A` is idempotented
and `M` is nondegenerate. In the actual completion, the family assigning to
every idempotent `e` its element `e` is compatible.

If the completion were nondegenerate, this family would be fixed by some
idempotent `f`. The published formula `idempotent_smul` then identifies it
with the canonical family of `f`. Evaluating at `e` gives `e*f=e` for every
idempotent. Every `a` has a right local unit `e`, so associativity gives
`a*f=(a*e)*f=a*(e*f)=a`. Commutativity makes `f` a left identity, contradicting
the published `CountableSupportAlgebra.no_left_identity` on the uncountable
base `ℂ`. All actions are the original regular and completion actions from
the published statement.
