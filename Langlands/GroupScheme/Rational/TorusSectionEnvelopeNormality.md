# Envelope normality from conjugates of a quotient section

This internal reduction uses the existing actual represented fppf quotient,
split unipotence, homomorphism conjugacy, fixed ground-field envelope, and
fpqc descent interfaces. It does not change the target envelope or normality
predicate and does not prove the finite-field solvable target by itself.

`torusSectionLift q s i` is the homomorphism `i ≫ q ≫ s`. When `s ≫ q` is the
identity, its composite with `q` is exactly `i ≫ q`. The target group of `q`
need not itself be a torus for the reduction below.

`conjugatesInto_baseChange` transports universal conjugate containment under
an arbitrary change of base. It uses the existing point equivalences, their
multiplicativity, and the equality between the base change of a subgroup
range and the range of the actual base-changed homomorphism.

Assume that `G` is smooth affine over a field, `n : N → G` is a smooth connected
closed split unipotent subgroup, and `q : G → Q` is the represented fppf
quotient by its full all-test range. Supply a group homomorphism section
`s : Q → G`. The additional containment hypothesis says that every ambient
conjugate of every section-image point is in the fixed ground-field torus
envelope, on every test scheme. The exact stable-vector subgroup proposition
remains an explicit structural input. Torus vector action linearization and
split unipotent affine torsor triviality are supplied by their published proofs.

After extension to the algebraic closure, take any closed torus map `i` into
`G`. Its section lift has the same quotient map. The published same-source
conjugacy theorem for torus maps through a split unipotent kernel supplies a
single rational ambient conjugator taking this lift to `i`. The section-conjugate
containment hypothesis, transported to the algebraic closure, therefore puts
the whole image of `i` in the base-changed envelope. The published envelope
base-change criterion proves equality with the geometric torus envelope.
Geometric envelope normality and its fpqc descent then give normality on every
original test scheme, including nonreduced tests.

No maximal-torus conjugacy or maximal-torus base-change theorem is required by
this implemented route. Existence of the split unipotent quotient and section,
the stable-vector proposition, and universal section-conjugate containment
remain genuine inputs to this reduction. They must be discharged before the
exact finite-field solvable proposition is proved.
