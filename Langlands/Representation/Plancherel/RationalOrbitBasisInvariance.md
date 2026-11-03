# Basis independence of scalar smooth orbit functions

Author: Worker 200.

This internal construction proves that the existing scalar smoothness
predicate on the actual discrete-series twist orbit is independent of the
finite integer basis chosen for the actual rational-character valuation
image. It supplies explicit character reconstruction in any such basis,
the resulting orbit parameter map, its open-quotient property, and the
equivalence of the smoothness tests.

The motivation is Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), VI.1, printed pp.295–296
(PDF pp.61–62). The source tests smoothness after pulling back to the
unitary character torus and uses its scalar smooth-function algebra in
the diagonal-invariant description of coefficient families. The basis
comparison proved here is an internal prerequisite for that construction;
the source does not state these integer-matrix lemmas separately.

## Integer monomials and their real lifts

For finite `K` and an integer matrix `a : J → K → ℤ`,
`finiteTorusMonomial a` and `finiteTorusMonomialLift a` are

\[
 m_a(z)_j=\prod_k z_k^{a_{jk}},\qquad
 A_a(x)_j=\sum_k a_{jk}x_k.
\]

`finiteTorusExp_monomialLift` proves
`finiteTorusExp ∘ A_a = m_a ∘ finiteTorusExp`. Its proof uses the
additive exponential homomorphism to turn the finite sum into a product,
then the integer-scaling law for `Circle.exp`.
`contDiff_finiteTorusMonomialLift` proves smoothness of `A_a` by finite
sums of constant multiples of coordinate projections.

Recall that `IsSmoothFiniteTorusFunction f` means
`ContDiff ℝ ∞ (f ∘ finiteTorusExp)`, with complex values regarded as
a real normed space. `IsSmoothFiniteTorusFunction.comp_monomial`
composes this smooth lift with `A_a` and uses the exponential identity
to prove smoothness of `f ∘ m_a`. Both index types are finite for this
smoothness result.

## Reconstructing the same lattice character

Let `L` be any additive commutative group with its displayed integer
module structure, and let `b : Basis J ℤ L` and `c : Basis K ℤ L`.
For finite `J`, `finiteTorusBasisChange b c` reconstructs the
circle-valued character from its values `z_j` on `b_j` and evaluates
that character on `c_k`:

\[
 T_{bc}(z)_k
   = \left(b.\operatorname{constr}_{\mathbb Z}
          (j\mapsto\operatorname{ofMul}(z_j))(c_k)\right).\operatorname{toMul}
   = \prod_j z_j^{\,b.\operatorname{repr}(c_k)_j}.
\]

The second equality is `finiteTorusBasisChange_eq_monomial`, proved
by the finite-basis reconstruction formula and the conversion of sums
and integer scalar multiplication to products and integer powers.

When both bases are finite, `finiteTorusBasisChange_constr` proves
that reconstructing in `c` after this evaluation gives exactly the
original linear map reconstructed in `b`. It checks equality on the
basis `c`. Evaluation on `b_j` then proves
`finiteTorusBasisChange_inverse`:
`T_cb (T_bc z) = z`.

`continuous_finiteTorusBasisChange` uses the Laurent formula,
continuity of each integer power, finite products, and the product
continuity criterion. `finiteTorusBasisChangeHomeomorph b c` has
underlying map `T_bc`, inverse `T_cb`, and these continuity proofs.

`isSmoothFiniteTorusFunction_basisChange_iff` proves

\[
 f\circ T_{bc}\text{ is smooth}\quad\Longleftrightarrow\quad
 f\text{ is smooth}.
\]

The reverse implication is smooth precomposition by an integer
monomial. The forward implication precomposes by the inverse
integer monomial and simplifies using `T_bc ∘ T_cb = id`.
Thus basis independence is proved by explicit inverse smooth lifts.

## Actual unramified characters

The field `F : Type u` is an arbitrary nonarchimedean local field.
For the actual constructions, `G` is an affine group scheme locally
of finite type over `F`, with
`hG : GroupScheme.IsConnectedReductive G`. Its rational points have
the canonical rational-point topology and the proved nonarchimedean
group structure. No splitness, quasisplitness or characteristic
restriction is imposed. The character evaluation identity itself
does not require the local-finite-type premise.

Put `L = Additive (rationalDiscreteValuationImage G)`. For any finite
integer basis `b` of `L`, let `b0` be the existing
`rationalReductiveValuationBasis G hG` and let `e0` be the existing
`rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG`.
`rationalUnitaryUnramifiedCharacterOfBasis hG b` is the actual map

\[
 \chi_b(z)=e_0^{-1}(T_{b b_0}(z)).
\]

It takes values in the existing continuous unitary unramified
character group of `G(F)`. For an actual rational point `g`,
`rationalUnitaryUnramifiedCharacterOfBasis_apply` proves

\[
 \chi_b(z)(g)=
 \prod_j z_j^{\,b.\operatorname{repr}(v(g))_j},
\]

where `v(g)` is the existing actual valuation-image projection,
regarded additively. In Lean the equality is in `ℂ`, after including
the left side from `ℂˣ` and the right side from `Circle`. The proof
unfolds the existing character reconstruction, applies
`finiteTorusBasisChange_constr`, and expands the reconstruction in
`b`. Thus the new parameters reconstruct the same actual lattice
characters and their actual pullbacks to rational points.

## Actual orbit parameters and smoothness

Let `T` be a commutative group scheme, `s : T.toGrp ⟶ G` a
central morphism with proof `hs`, and `A = s(T(F))`. The measurable
space on `G(F)/A` and its Haar measure `mu` remain displayed.
Normality of `A` is derived from centrality before each dependent
Haar and representation-class binder. The representation-carrier
universe `uV` is independent of the field universe `u`.

For an existing canonical discrete-series class `omega`, write
`O_omega` for its actual unitary-unramified twist orbit.
`rationalDiscreteSeriesOrbitCoordinateMapOfBasis s hs mu hG b omega`
is the existing default orbit coordinate map composed with
`T_(b b0)`. Its `val` theorem identifies its underlying class as
`chi_b(z) • omega`. Its open-quotient theorem composes the
existing open quotient with the basis-change homeomorphism, so its
codomain has the same actual orbit topology.

Finally, `isSmoothRationalOrbitFunction_basis_iff` says, for every
scalar function `f : O_omega → ℂ`,

\[
 \operatorname{IsSmoothFiniteTorusFunction}(f\circ p_{\omega,b})
 \quad\Longleftrightarrow\quad
 \operatorname{IsSmoothRationalOrbitFunction}(f).
\]

This is the generic basis-change equivalence applied to the default
orbit pullback. In particular any two finite image bases give the
same test and the same existing scalar function algebra. No
actual-image finite-index assumption or affineness of `T` is used.

This pair concerns scalar exponential-lift smoothness. Comparison
with a quotient manifold structure or Mathlib `ContMDiff` remains
open. Coefficient tensors, their nontrivial stabilizer action in
VI.1, representative comparisons for those tensors, normalized
intertwiners, wave packets, and the Plancherel assertions remain
separate obligations.
