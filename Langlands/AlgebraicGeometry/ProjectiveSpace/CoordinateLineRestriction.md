# Restriction of projective coordinate lines

This is an internal adapter derived from the existing actual polynomial-Proj
model and its homogeneous-localization charts. All coefficient rings `K`, `R`
and `B` are arbitrary commutative rings in universe `u`; `n` is any natural
number. Write `A_R = R[X_0,…,X_n]` with its standard total-degree grading.
The scheme sources below also lie in universe `u` and need not be affine,
reduced or nonempty.

`unitChartRingMap_target_comp` takes a ring homomorphism `f : A_R → B`,
a ring homomorphism `φ : B → K`, an element `t : A_R`, and a witness that
`f(t)` is a unit. It identifies unit-chart evaluation for `φ ∘ f` with
`φ` composed with unit-chart evaluation for `f`. These algebraic maps
from the degree-zero localization exist without a homogeneity or
positive-degree premise on `t`. The proof uses uniqueness of ring maps
from the ordinary localization away from `t`.

`chartRingMap_comp_coefficients` takes any graded ring homomorphism
`g : A_K → A_R`, any `f : A_R → B`, and any `t : A_K`. Evaluation on the
chart away from `t` for `f ∘ g` equals the graded chart map induced by
`g`, followed by chart evaluation for `f` away from `g(t)`. Its codomain
is the ordinary localization of `B` away from `f(g(t))`. This is another
algebraic identity without geometric map-existence hypotheses. The proof
computes both maps on homogeneous fraction representatives.

`fromOfGlobalSections_comp_coefficients` is the corresponding identity of
actual scheme morphisms. It takes an arbitrary scheme `X`, a graded map
`g : A_K → A_R` satisfying
`I_R ≤ g(I_K)`, where `I` denotes the irrelevant homogeneous ideal, and a
ring homomorphism `f : A_R → Γ(X,⊤)`. It also explicitly assumes that the
ordinary ideals `f(I_R)` and `(f ∘ g)(I_K)` are both the unit ideal. These
three premises supply `Proj.map g` and the two global-coordinate maps.
The identity is
`from(f ∘ g) = from(f) ≫ Proj.map g`.
The proof compares restrictions on the defining cover, indexed by
positive-degree homogeneous elements, and uses the preceding chart identity
and the existing formula for `Proj.awayι ≫ Proj.map`. No invertibility or
linearity assumption is imposed on `g`.

For a scheme `X` with a specified algebra structure `R → Γ(X,⊤)` and
`j : Fin(n+1)`, `basisPoint_toSpec` identifies the structural composite
of the actual coordinate point `basisPoint_R(X,j)` with
`X.toSpecΓ ≫ Spec.map(R → Γ(X,⊤))`. It follows from the existing
`fromOfGlobalSections_toSpecZero` formula and evaluation on constant
polynomials.

`comp_basisPoint` takes schemes `X,Y` with specified `R`-algebra structures
on both global-section rings, a scheme morphism `a : Y → X`, and the
compatibility equation
`a.appTop ∘ algebraMap_R,X = algebraMap_R,Y`. It proves
`a ≫ basisPoint_R(X,j) = basisPoint_R(Y,j)`. The chosen coordinate evaluates
to `1`, so the previously proved unit-chart formula applies on the entire
source. Target-ring naturality and the naturality of `toSpecΓ` give the
identity.

`basisPoint_coefficientMap` takes both specified algebra structures
`R → Γ(X,⊤)` and `K → Γ(X,⊤)`, a ring homomorphism `φ : K → R`, and
the compatibility equation
`algebraMap_R,X ∘ φ = algebraMap_K,X`. It proves
`basisPoint_R(X,j) ≫ coefficientMap n φ = basisPoint_K(X,j)`.
The coefficient polynomial map fixes each variable and acts by `φ` on
constants. Thus the two evaluation homomorphisms agree; their primitivity
is the existing basis-evaluation theorem. Applying the graded composition
identity gives the result.

These are restriction identities for existing coordinate points, used to
construct natural relative basis sections. They do not assert existence of
a stabilizer representation or a homogeneous quotient.
