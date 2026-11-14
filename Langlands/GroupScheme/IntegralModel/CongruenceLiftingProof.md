# Henselian lifting at every positive congruence level

Author: Worker 503.

The theorem
`Langlands.GroupScheme.IntegralModel.henselianCongruenceLifting.{u}` proves
exactly
`Langlands.GroupScheme.IntegralModel.HenselianCongruenceLiftingStatement.{u}`.
For every commutative Henselian local ring `R : Type u`, every group scheme
`Y` over `Spec R` with smooth structure morphism, and every positive integer
`n`, the actual reduction homomorphism

`baseChangeSectionHom (congruenceBaseMap R n) Y`

is surjective. Its target consists of sections of the actual base change
of `Y` to `Spec (R / (maximalIdeal R)^n)`. The theorem makes no affineness,
separatedness, quasi-compactness, domain, noetherianity, discrete valuation,
or completeness assumption. Its only universe parameter is `u`.

## Implemented proof

The helper theorems lie in the namespace
`Langlands.GroupScheme.IntegralModel.CongruenceLifting`. The first three
work with commutative rings `R`, `A` and `S` in universe `u`, with `R`
Henselian local, `A` local, a surjective algebra map `R -> A`, and a
nilpotent maximal ideal of `A`.

`exists_lift_of_etale` lifts an `R`-algebra map `phi : S -> A` when `S` is
etale over `R`. Let `K` be the residue field of `A`. The composite
`R -> A -> K` is surjective. The published Library theorem
`Langlands.CommutativeAlgebra.HenselianSections.exists_lift_of_etale`
gives an `R`-algebra map `sigma : S -> R` inducing the composite of `phi`
with `A -> K`. The reduction of `sigma` to `A` and `phi` agree in `K`.
The kernel of `A -> K` is the nilpotent maximal ideal of `A`, so Mathlib's
`Algebra.FormallyUnramified.lift_unique'` shows that they agree in `A`.
This uses formal unramifiedness of the etale algebra `S`.

`exists_lift_of_polynomial` treats an algebra `S` etale over a polynomial
algebra `P = R[X_i]` with finitely many variables. Lift the values
`phi(X_i)` to elements of `R` using the surjectivity of `R -> A`. These
values define an evaluation `theta : P -> R`. Endow `A` with the
`P`-algebra structure induced through `S`; the coordinate equations show
that `R -> A` respects the `P`-algebra structures. The tensor product
`B = R tensor_P S`, taken using `theta`, is etale over `R` by base change.
The compatible maps `R -> A` and `S -> A` give a map `rho : B -> A`.
The preceding lemma lifts `rho` to `B -> R`. Precomposing with `S -> B`
lifts `phi`, as verified on the pure tensors `1 tensor x`.

`exists_lift_of_smooth` treats a smooth `R`-algebra `S`. The kernel of
`S -> A -> K` is a prime ideal `q`. Mathlib's
`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial` chooses `g` outside
`q` such that `S[1/g]` is standard etale over a polynomial algebra in
finitely many variables. Since the residue of `phi(g)` is nonzero,
`phi(g)` is a unit in the local ring `A`. Thus `phi` extends to
`S[1/g] -> A`. Apply `exists_lift_of_polynomial` and precompose with the
localization map to obtain the desired lift of `phi`.

`exists_section_of_smooth` is the scheme form. Let `p : U -> Spec R` be
smooth and `b : Spec A -> U` a point over `R`. Choose an affine open `V`
containing the image under `b` of the closed point of `Spec A`. Every point
of the spectrum of a local ring specializes to its closed point. Continuity
of `b` and openness of `V` therefore imply that the whole image of `b`
lies in `V`; no affineness of `U` is needed. Factor `b` through
`Spec Gamma(U,V)` by open-immersion lifting. Full faithfulness of `Spec`
turns this factored map and `p` into compatible ring maps
`R -> Gamma(U,V) -> A`. The first map is smooth, since the composite of
the open immersion with `p` is smooth. The preceding algebra lemma gives
`Gamma(U,V) -> R`. Applying `Spec` and composing with `V -> U` gives a
section `sigma` of `p` satisfying the exact equation
`Spec(R -> A) >> sigma = b`.

For the application, `congruenceRing_nontrivial` proves that
`A = R / m^n` is nonzero: `m^n <= m` for positive `n`, and `m` is proper.
The final theorem equips `A` with a local ring structure using the
surjection from `R`. The lemma
`congruenceRing_maximalIdeal_isNilpotent` identifies its maximal ideal
with the image of `m`; its `n`th power is zero because ideal maps preserve
powers and the quotient map kills `m^n`. No finiteness assumption on `m`
is used.

Given a section `y` of the base change of `Y` over `Spec A`, compose its
underlying morphism with the first pullback projection to get
`b : Spec A -> Y`. The section equation for `y` and the pullback equation
show that `b` is over `R`. The scheme lemma gives `sigma : Spec R -> Y`
whose reduction is exactly `b`. This is an integral section. Finally,
`baseChangeSectionHom_left` describes its actual reduced section as a
pullback lift. The equality with `y` follows by `pullback.hom_ext`, using
the exact equation for `b` on the first projection and the section
equation on the second.

## Provenance and scope

The mathematical source is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Lemma 8.1.3 and proof, printed pages 284–285, PDF pages
315–316, registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
Those pages were read from the registered original. The registered
November 2024 corrections contain no entry for this lemma or these pages.
The source proof chooses an affine etale chart over affine space, lifts
its coordinates, and solves the resulting etale lifting problem using
the Henselian property. The Lean proof implements the same route using
standard etale polynomial charts and tensor products. Its etale step
uses the published residue-field lifting theorem followed by uniqueness
across the nilpotent maximal ideal, rather than invoking EGA's
finite-test bijection directly.

The source states the result for smooth schemes over the Henselian
valuation ring of the book. The target already generalizes the base to
any Henselian local ring and specializes the conclusion to group
schemes. The helper scheme theorem explains why the implemented proof
requires only those hypotheses. The local-chart specialization is derived
infrastructure following the published Library's
`Langlands.CommutativeAlgebra.PointedEtaleLocalSections` proof with local
quotient points in place of residue-field points. No statement or any of
its imported Lean/Markdown pairs is changed.
