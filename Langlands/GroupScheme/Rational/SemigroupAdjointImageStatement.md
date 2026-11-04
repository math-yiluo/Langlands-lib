# Semigroup images under adjoint quotients

`RelativeRoot.SemigroupAdjointImageStatement` isolates the geometric image
claim used in the reductive step of CGP Proposition 3.3.10(c). It is a
proposition target, not a proof of that claim.

The statement quantifies over an algebraically closed field `k : Type u`,
an actual adjoint quotient `q : G → Q`, a split acting torus `S`, actual
actions `b` and `c`, and equivariance on every test scheme. The existing
`IsAdjointQuotient q` supplies connected reductivity of `G`, adjointness of
`Q`, flatness, scheme-surjectivity and local finite presentation of `q`,
its full scheme-theoretic centre kernel, and its scheme and group quotient
universal properties. Affineness is also passed explicitly to construct the
two intrinsic semigroup functors; it is already implied by the geometric
quotient hypotheses.

For every additive semigroup `A` of actual characters with `0 ∈ A`, the
conclusion is `IsFppfImage (semigroupSubgroup b A) (semigroupSubgroup c A) q`.
This requires actual monic group-scheme representatives of the two functors
and a commuting restriction morphism which is flat, surjective and locally
of finite presentation. It asserts an fppf subgroup image, rather than
surjectivity on points over each original test scheme. Neither `q` nor its
full centre kernel nor the restriction is required to be smooth.

The target is derived from Conrad–Gabber–Prasad, *Pseudo-reductive Groups*,
second edition, proof of Proposition 3.3.10(c), printed p.113 / PDF p.139.
The source chooses a maximal torus fixed by the acting torus and compares
the root-subgroup descriptions of the semigroup groups in `G` and in its
full-centre quotient. It explicitly allows a nonsmooth quotient. The two
descriptions give the subgroup image equality. The fppf restriction in this
target also uses the source's full inverse-image equality: the full centre
lies in the chosen torus and then in the semigroup group because `0 ∈ A`.
An actual fppf map restricts to an fppf map on such a full inverse image by
base change. This is a derived formulation of those source claims, not a
verbatim assertion of smoothness in the source.

The action `c` and actual quotient `q` are supplied. Their existence, inner
factorization of torus actions, fixed maximal tori and root-subgroup
comparison are not proved here. The proposition does not extend this claim
to arbitrary fppf homomorphisms or remove the condition `0 ∈ A`.

`semigroupSubgroup_comap_eq_of_adjointImage` is a formal conditional consumer.
It assumes the new image proposition and separately assumes containment of
the entire centre in the source semigroup functor. It rewrites the actual
kernel range as the full centre using `IsAdjointQuotient`, then applies the
published `IsFppfImage.comap_eq_of_kernel_le` descent lemma. The resulting
equality holds on every test scheme, including nonreduced schemes. This
consumer proves neither the new proposition nor the centre-containment
hypothesis and does not finish the full semigroup comparison theorem.
