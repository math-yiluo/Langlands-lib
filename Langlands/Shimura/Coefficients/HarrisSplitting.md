# Harris coefficient spaces and actual completed factors

Author: Worker 57.

## Purpose and provenance

Harris (1999), Section 3, printed page 306, takes an algebraic representation
over a number field `L` and uses the coefficient algebra `L_v = L ⊗_ℚ ℚ_v`.
Printed pages 307–308 then use stable lattices in `W(L_ℓ)`. This module
decomposes that actual algebra and coefficient module at a finite rational
place into the factors at all places of `L` above it. It proves that the
published Harris action becomes the product of the published completion
actions.

This decomposition and its action comparison are internal deductions, rather
than additional assertions quoted from Harris. The ring bijection is obtained
from the published `completedTensorComparison` by exchanging the tensor
factors. Tensoring this ring equivalence with `W` and distributing a tensor
product over a finite dependent product gives the module equivalence.
Algebraic naturality and the existing rational scalar comparison give the
equivariance identities. No decomposition or action comparison is supplied
as an assumption.

The original passage on printed pages 306–308 was read directly. Source:
Michael Harris, *Galois properties of cohomological automorphic forms on
GL(n)* (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
The published proof and arithmetic provenance of the completed-tensor
theorem are documented in
`Langlands/Global/AdelicFunctoriality/CompletedTensorComparisonProof.md`.

## Coefficient algebra

Let `L : Type u` be a number field and `p : FinitePlace ℚ` an actual finite
rational place. Write `Qp = FiniteCompletion ℚ p` and
`Ll = FiniteCompletion L l`. The index `FinitePlacesAbove L p` is the
published finite subtype of actual finite places of `L` whose prime ideals
lie over `p.asIdeal`; it carries the corresponding lies-over instance.

For any such place `l`, `harrisCoefficientProjection L p l` is an
`L`-algebra homomorphism

`L ⊗[ℚ] Qp →ₐ[L] Ll`.

It is the tensor-product lift of the embedding of `L` and the canonical
completed embedding `completionMap p l : Qp →+* Ll`. Its `_tmul` formula is

`a ⊗ b ↦ algebraMap L Ll a * completionMap p l b`.

The `_includeRight` theorem says that restricting this map to rational
scalars and composing with the tensor inclusion `Qp → L ⊗[ℚ] Qp`
recovers that completed embedding as a rational algebra map.

`harrisCoefficientRingMap` collects these maps into the dependent product.
Its bijectivity theorem identifies its underlying function with
`finiteTensorMap p` after `Algebra.TensorProduct.comm ℚ L Qp`.
The identification is proved by tensor induction, using the displayed
pure-tensor formula and commutativity in each completed field. The finite
conjunct of `completedTensorComparison ℚ L` proves bijectivity of the
first map; the factor exchange is an equivalence.

`harrisCoefficientRingEquiv` is therefore a constructed equivalence

`L ⊗[ℚ] Qp ≃ₐ[L] ((l : FinitePlacesAbove L p) → Ll)`.

Its application at `l` is exactly `harrisCoefficientProjection L p l.1`.
In particular the index consists of all the actual places above `p`, rather
than a chosen completion or an assumed decomposition.

## Coefficient module

Let `W : Type w` be an additive commutative group and an `L`-module.
There is no finite-dimensionality hypothesis on `W`. The definition
`harrisCoefficientEquiv L p W` has type

`((L ⊗[ℚ] Qp) ⊗[L] W) ≃ₗ[L]`
`  ((l : FinitePlacesAbove L p) → Ll ⊗[L] W)`.

The construction first applies the `L`-linear equivalence underlying
`harrisCoefficientRingEquiv`, tensored with `W`, and then Mathlib's
`TensorProduct.piLeft L W` for the finite dependent family of completions.
The resulting equivalence is asserted to be `L`-linear. This declaration
does not equip the target with a transported `L ⊗[ℚ] Qp`-module structure
or assert linearity over that larger algebra.

The `_tmul` theorem gives its component formula

`(s ⊗ x) ↦ (l ↦ harrisCoefficientProjection L p l.1 s ⊗ x)`.

The `_apply` theorem identifies each component on an arbitrary tensor with
the actual tensor projection
`(harrisCoefficientProjection L p l.1).toLinearMap.rTensor W`.
Its proof extends the pure-tensor formula by tensor induction.
The coefficient field and module may lie in independent universes.

## Local action and point compatibility

Let `A : Type v` be a possibly noncommutative rational algebra with
`σ : AlgebraInvolution ℚ A`, and let
`ρ : (σ.baseChange L).AlgebraicRepresentation W` be the published natural
algebraic representation. The universes of `A`, `L` and `W` are independent.
No finite-dimensionality or continuity assumption is needed for the local
constructions.

The general lemma `AlgebraInvolution.pointsMap_comp_apply` proves that
changing coefficients by a composite of rational algebra maps is the
composite of the named point maps. The proof compares the algebra-unit
coordinate using `changeCoefficients_comp` and the scalar-unit coordinate
by the definitions.

`ρ.harrisProductLocal p` is a group homomorphism from `σ.Points Qp` to
the `L`-linear automorphisms of the dependent coefficient product. Its
`l` component is the existing
`ρ.actVia (completionMap p l.1).toRatAlgHom`, restricted to `L`-scalars.
`LinearEquiv.piCongrRight` assembles the automorphisms; their identity and
multiplication laws prove the homomorphism laws. The application formula
retains these exact component actions.

`harrisCoefficientProjection_points` proves that applying the point map
of `harrisCoefficientProjection` after the rational tower map gives the
same point as first using `completionMap` and then the tower map into
the group over `L`. Its proof uses the published `towerPoints_naturality`,
the proved point-composition lemma, and the `_includeRight` identity.
This lemma depends on `σ` and `L`, but not on the representation `ρ`.

`ρ.harrisCoefficientEquiv_local p` says, for every `g : σ.Points Qp`
and coefficient tensor `x`,

`harrisCoefficientEquiv L p W (ρ.harrisLocal p g x) =`
`  ρ.harrisProductLocal p g (harrisCoefficientEquiv L p W x)`.

The proof compares the two sides at every actual place above `p`. It
rewrites the equivalence as its tensor projection, applies `ρ.naturality`
to the coefficient projection, and rewrites the resulting group point
with `harrisCoefficientProjection_points`. Thus equivariance concerns
the original evaluated actions on both sides.

## Finite-adelic and rational actions

For the remaining declarations assume `[Module.Finite ℚ A]`, as required
by the published finite-local map. `ρ.harrisAdelic p` composes
`ρ.harrisLocal p` with `σ.finiteLocalMap p`. It acts by automorphisms
linear over `L ⊗[ℚ] Qp`. `ρ.harrisProductAdelic p` composes the product
local action with that same map, and acts by `L`-linear automorphisms.
Its component formula is the published `ρ.placeAction p l.1`.

`ρ.harrisCoefficientEquiv_adelic p` specializes local equivariance to
`σ.finiteLocalMap p g`. Finally, `_diagonal` says that, at every `l`,
the action of `σ.finiteAdelicDiagonal g` on the decomposed coefficient
is the scalar extension to `Ll` of
`ρ.rationalAction (σ.diagonalPoints L g)`. The proof combines adelic
equivariance, the component formula, and the published
`placeAction_diagonal` identity.

This module supplies the algebraic comparison needed to assemble the
existing single-completion coefficient constructions. It does not yet
assemble their integral lattices, reduction rings, torsion actions,
congruence levels or descent. It proves no continuity of the new
equivalence, freeness of the level actions, covering or torsor property,
scheme realization, local-system construction or cohomological comparison.
