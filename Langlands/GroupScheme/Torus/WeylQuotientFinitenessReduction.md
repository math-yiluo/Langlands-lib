# Finiteness of a supplied Weyl quotient from a general local-base criterion

This is an internal derived reduction in an arbitrary universe. It combines the
actual splitting-cover counts in `WeylQuotientSplittingCoverOrder` with the
Library's fpqc descent of finiteness and its passage from single-morphism descent
to locality on the target for the fppf precoverage.

`WeylQuotientFinitenessReductionStatement` is an implication. Its first premise
is a general finiteness criterion for quasi-compact separated étale morphisms
of schemes. The criterion assumes that for every commutative local ring `R`
and morphism `Spec R ⟶ Y`, a single natural number counts all actual lifts into
`X` of every algebraically closed `R`-field with its given algebra structure.
The natural number is chosen before the field and algebra structure. This
general criterion is an explicit premise; the module does not prove it.

The conclusion of the implication concerns a reductive group scheme `G` over
an arbitrary scheme `S` and a closed maximal relative torus `t : T.toGrp ⟶ G`.
It takes a supplied closed representative `n : N ⟶ G` of the actual all-test
normalizer and a supplied group scheme `W` with a scheme-surjective homomorphism
`q : N ⟶ W`. On every test scheme, the kernel of `q` must be exactly the inverse
image under `n` of the actual centralizer functor. The structure morphism of
`W` must be quasi-compact, separated and étale. The conclusion is that this
structure morphism is finite. No separate local-finite-type assumptions on `N`
or `W` are needed: closedness of `n` and smoothness of `G` give the former, and
étaleness gives the latter.

`weylQuotientFinitenessReduction` proves this implication. The splitting-cover
count theorem supplies an étale cover of `S` such that each pulled-back quotient
has the universal local-base cardinality condition. The geometric assumptions
on `W` survive base change, so the explicit general criterion proves finiteness
over each member. Each étale member is flat and locally of finite presentation,
so the same family is an fppf cover.

The proof then uses `FppfLocal.isLocalAtTarget_fppfPrecoverage` for the property
`IsFinite`. Its hypotheses are Zariski target locality, stability under base
change, and descent along surjective flat locally finitely presented morphisms.
The first two are standard Mathlib instances. The third follows from the
Library's fpqc finiteness descent and Mathlib's fpqc-to-fppf descent instance.
Thus finiteness on all cover members implies finiteness of `W` over `S`.
No quasi-compactness of the individual étale cover morphisms is assumed.

This reduction constructs no quotient. It leaves the general smooth-affine
quotient theorem and the general local-base finiteness criterion as separate
mathematical obligations. It does not prove the unconditional
`WeylGroupSchemeFiniteEtaleStatement`.
