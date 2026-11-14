# Closed immersions in diagrams of group extensions

`Langlands.GroupScheme.FppfExtensionClosedImmersionStatement.{u}` concerns
group schemes over an arbitrary scheme `S`. Let `q : G → Q`, `q' : G' → Q'`,
`f : G → G'`, and `c : Q → Q'` be homomorphisms such that
`f ≫ q' = q ≫ c`. Suppose that a homomorphism `a : ker(q) → ker(q')`
commutes with the actual kernel inclusions and `f`. If `q` is flat,
surjective, and locally of finite presentation, and `a` and `c` are closed
immersions on underlying schemes, the statement asserts that `f` is a
closed immersion on underlying schemes.

The kernels and their inclusions are the fibre products with the target
unit defined in `Langlands.AbelianScheme.Kernel`. Thus the assertion uses
actual scheme kernels, rather than an additional abstract exactness
predicate. It imposes no flatness, surjectivity, or finiteness condition
on `q'`, and no separatedness or finiteness condition on the four structure
morphisms.

This is a derived strengthening of Brian Conrad, *Reductive group schemes*
(2014), Lemma 5.3.8, p.169, registered as
`conrad-2014-reductive-group-schemes` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`).
Conrad assumes a diagram of fppf short exact sequences of flat, separated,
finitely presented group schemes. The internal formulation retains only
the source quotient cover needed for a descent proof. It is not presented
as a verbatim encoding of the source's hypotheses.

The intended proof factors `f` through `G' ×[Q'] Q`. Pulling this
factorization back along a cover obtained from `q` identifies it with
the product of the identity on `G` and the map `a`. Closed immersions
descend along fppf covers. Composing with the base change of `c` then
gives the assertion. This file specifies the proposition; it does not
provide its proof.
