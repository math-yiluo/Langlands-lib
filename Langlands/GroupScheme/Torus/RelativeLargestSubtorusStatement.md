# Statement: the largest relative subtorus

`Langlands.GroupScheme.RelativeMultiplicativeTypeLargestSubtorusStatement.{u}`
is a statement-only `Prop`-valued definition. This module proves nothing and
introduces no axioms.

Its local predicate `IsLargestSubtorus t`, for `t : T ⟶ H` over a scheme `S`,
asserts that `t` is a closed subgroup, `T` is a relative torus, and every closed
subtorus `t' : T' ⟶ H` factors through `t` by an actual group-scheme
homomorphism. This universal property contains every closed subtorus; it is
stronger than merely excluding larger subtori. The factorization is unique
because a closed immersion is a monomorphism.

For every group `H` of multiplicative type over every scheme `S`, the
statement asserts existence of such a largest subtorus and stability of
this property for every choice of largest subtorus under every base change
`S' ⟶ S`. The base and all objects range over universe `u`.

`RelativeMultiplicativeType.IsMultiplicativeType` means diagonalizable with
finitely generated abelian character groups on an fppf cover.
`RelativeTorus.IsTorus` means a finite split torus on an étale cover; the
rank may vary. `IsClosedSubgroup` means a closed immersion of the underlying
schemes. Thus `H` may have finite or nonreduced parts and need not be smooth.
There are no Noetherian, reducedness, connectedness or nonemptiness assumptions
on the base.

The source is Brian Conrad, *Reductive group schemes* (2014), source ID
`conrad-2014-reductive-group-schemes`, retained as
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
Printed and one-based PDF pages agree. Definition B.1.1, p.280, supplies the
multiplicative-type convention. Remark B.1.2, pp.280–281, explicitly asserts a
closed subtorus containing all closed subtori and retaining this property
under arbitrary base change. On p.281 the split construction is
`D_S(M/M_tor) ⊂ D_S(M)`, with the general case obtained by fppf descent.
Proposition B.3.4, pp.290–291, supplies the étale-local splitting convention for
groups of multiplicative type and hence for the tori in this assertion.

The Lean factorization property expresses the source's containment of closed
subgroups. Two representatives satisfying it factor through one another,
so the source's uniqueness of the subgroup also yields the assertion for
every largest representative. The statement omits the character-module
construction and any assertion about existence or finiteness of a quotient.
It extends the base scope of the existing field-level
`MultiplicativeTypeLargestSubtorusStatement`; it does not replace that
statement's additional quotient-recognition and ambient-normality clauses.
