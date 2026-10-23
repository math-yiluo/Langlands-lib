# Inverse transpose preserves Whittaker type

This derived construction completes the functional-space part of the existing
Weyl transform. It builds explicit complex-linear equivalences between standard
Whittaker functionals on a representation and inverse-character functionals on
its inverse-transpose pullback, and in the opposite character direction. It
then proves that the published `RankinSelberg.IsOfWhittakerType` condition is
preserved and reflected by this pullback with character reversal.

## Source and provenance

The normalization is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg
Convolutions* (1983), section 2.1, printed pages 385–386. Source ID
`jpss-1983-rankin-selberg`; central-library file
`Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both pages were read visually from the original scan. Page 385 defines
Whittaker type using admissibility, finite type and a one-dimensional functional
space, and explains the inverse-transpose and character-reversal argument.
Page 386, formula (4), gives the corresponding transform of coefficient
functions; its following paragraph separates the irreducible contragredient
identification.

The present implementation is derived from the published project definitions
and their proved algebraic identities. It reuses `Whittaker.DualTransform`,
`GeneralLinear.inverseTranspose`, `GeneralLinear.weylLong`,
`CuspidalSupport.GroupTransport` and `RankinSelberg.AnalyticStatement`.
The two-sided functional equivalences and the group-algebra finiteness helper
make the source's transport argument explicit. The algebraic equivalences are
valid in greater generality than the source's local-field setting; they are
not claimed as a separate statement in that source.

## Constructions and implemented arguments

Write `i(g) = (g⁻¹)ᵀ`, `w` for the all-ones long Weyl representative and
`r(u) = w i(u) w` for the reflected upper-unipotent element. The existing
matrix lemmas give `w² = 1`, `i(w) = w` and `i² = id`.

`Whittaker.reflectedFunctionalEquiv π θ θ' hθ hθ'` takes two characters
satisfying `θ(r(u)) = θ'(u)` and `θ'(r(u)) = θ(u)`. It constructs an actual
linear equivalence

```
functionals N θ π ≃ₗ[ℂ] functionals N θ' (inverseTransposePullback π).
```

Both its forward and inverse maps send a functional `ℓ` to
`v ↦ ℓ(π(w)v)`. For the forward covariance equation, the proof uses
`w i(u) = r(u) w`, then the source functional's covariance and `hθ`.
For the inverse equation, it uses `w u = i(r(u)) w`, covariance for the
pullback representation and `hθ'`. The two inverse laws follow by applying
`π(w)` twice and using `w² = 1`. Linearity is pointwise. Thus the construction
requires no choice of a nonzero functional or of a basis.

`Whittaker.dualFunctionalEquiv π ψ` specializes this equivalence to the
standard and inverse-standard characters. The theorem
`dualFunctionalEquiv_apply` identifies its forward map with the already
published `dualFunctional ψ π` exactly. The reverse-character specialization
is `dualInverseFunctionalEquiv π ψ`, with its explicit evaluation lemma.
Both specializations use the proved character-reflection identities.

`finite_asModule_comp_mulEquiv` is the general finite-type transport helper.
For a representation `ρ` of `G` and a group equivalence `e : H ≃* G`,
finite generation of `ρ.asModule` over `R[G]` implies finite generation of
the pullback module over `R[H]`. The proof uses Mathlib's
`MonoidAlgebra.domCongr R R e.symm`. The pullback algebra action composed with
this algebra equivalence equals the original action, as checked on the group
basis. The identity on the underlying carrier therefore gives a surjective
semilinear map from the original module to the pullback module.
`Module.Finite.of_surjective` transports finite generation along this map.
This does not impose finite dimension over `R`.

`RankinSelberg.isOfWhittakerType_inverseTransposePullback` transports the
three clauses of the existing Whittaker-type predicate separately:

1. Admissibility follows from the published
   `isAdmissible_comp_continuousMulEquiv`, using
   `GeneralLinear.inverseTransposeContinuous`.
2. Finite generation over the group algebra follows from
   `finite_asModule_comp_mulEquiv`.
3. Given the source functional-space equivalence with `ℂ`, compose it with
   the inverse of `dualFunctionalEquiv` to obtain the target equivalence.

`isOfWhittakerType_inverseTransposePullback_inverse` proves the same result
starting with the inverse character. The theorem
`Whittaker.inverseTransposePullback_involutive` follows from the actual
matrix involution. Combining it with the two transport theorems gives
`isOfWhittakerType_inverseTransposePullback_iff`:

```
IsOfWhittakerType n (inverseStandardCharacter ψ n) (inverseTransposePullback π)
  ↔ IsOfWhittakerType n (standardCharacter ψ n) π.
```

## Scope and remaining obligations

The finite-type helper uses a commutative coefficient ring and groups with
independent universes `uR`, `uG`, `uH`, and `uV`. The functional equivalences use
a commutative ring `F`, its declared topology, the shared complex-valued
`UnitaryAdditiveCharacter F`, and a complex module `V`. No topology is imposed
on `V`. Field and carrier universes `uF` and `uV` are independent. The final
Whittaker-type theorems use a field `F`, matching the existing predicate, and
its declared topology; no additional topological-ring assumption is needed.
All matrix ranks are `n + 1`, including rank one. Neither character
nontriviality nor irreducibility is required for these transport results.

These results transport a supplied Whittaker-type hypothesis. They do not
prove that an arbitrary representation has Whittaker type or that an
irreducible representation is generic. Identification of the inverse-transpose
pullback with the actual smooth contragredient, multiplicity one, and the
analytic existence and functional-equation theorems remain separate
obligations. No local-factor comparison or law is asserted here.
