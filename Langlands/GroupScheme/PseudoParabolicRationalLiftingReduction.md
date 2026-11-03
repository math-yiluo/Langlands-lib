# Rational lifts through a supplied split-radical quotient

Author: Worker 1478.

This internal construction connects the published actual-map split-radical
reduction to rational lifting. It supplies a conditional reduction within
the main proof, rather than a proof of the unrestricted rational-lifting
statement.

`PseudoParabolicRationalLiftingProperty G` is the exact quotient-and-point
body of `PseudoParabolicQuotientRationalLiftingStatement`, for a fixed field
and a fixed ambient group. It quantifies over every actual pseudo-parabolic
inclusion, every supplied quotient model, the existing separatedness,
local finite type and quasi-compactness conditions on its structure map,
the smoothness, surjectivity and quasi-compactness of the supplied projection,
and its exact right-coset fiber equivalence on every relative scheme test.
Its conclusion lifts every rational point under that same projection.
The theorem `pseudoParabolicQuotientRationalLiftingStatement_iff` is a
definitional equivalence between the published target and the fixed-group
property universally quantified with precisely the target's smooth,
connected, affine ambient hypotheses.

Within `PseudoParabolicRationalLiftingReduction`, the data are an actual
split-radical inclusion `n : N → G`, any supplied fppf group quotient
`f : G → H` with the specified full scheme kernel, an actual
pseudo-parabolic inclusion `i : P → G`, and a supplied actual
pseudo-parabolic inclusion `j : K → H` with exact full preimage
`range i = (range j).comap f`. The construction additionally takes an
actual scheme section `s : H.X → G.X`, with `s ≫ f.hom.hom = 𝟙 H.X`,
and the fixed-group lifting property of `H`. The section is not required
to be a group homomorphism.

`exists_lift` retains the original quotient scheme `Q` and its original
projection `q : G.X → Q`. Affineness of `G` over the field and the
affineness of `H` supplied by `hj` give quasi-compactness of `f`. The published split-radical reduction constructs
the actual map `r : H.X → Q` with `f.hom.hom ≫ r = q`, proves that it
is smooth, surjective and quasi-compact, and proves its exact all-test
coset condition for the supplied `j`. Thus the fixed-group property of
`H` applies to this same `Q` and yields a rational point `a` with
`a ≫ r = x`. The section equation gives `s ≫ q = r`, so `a ≫ s`
lifts `x` under the original `q`.

The noncomputable definition `lift` packages the result as an actual
rational point of `G` together with its equation under `q`. Classical
choice supplies this data from `exists_lift`. No canonical choice is
claimed. `property_of_section` uses this construction to transfer the
entire fixed-group property from `H` to `G`, assuming the preceding
pseudo-parabolic descent data can be supplied for each `i`.

The provenance is internal, using the existing actual-map factorization
and its geometric and fiber-condition transport lemmas. All declarations
work in arbitrary universe `u`, over every field, including imperfect and
finite fields and all characteristics. The supplied section, the
pseudo-parabolic descent data, and the lifting property of `H` remain
inputs. This module does not prove their existence, establish a dimension
decrease, construct the affine group quotient, or prove the exact main
target. It provides the explicit rational-point step for a later dimension
induction once those prerequisites have been proved.
