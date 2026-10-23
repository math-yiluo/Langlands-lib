# Tensor compatibility of refined normalized induction

Author: Worker 346.

`Langlands.Parabolic.RefinedInductionTensorTheorem.{uF,uV}` is a
proposition-valued statement, not a proof. It quantifies over every prime
`p`, actual `PadicField.{uF} p`, compatible `TopologicalData`, rank `n`,
outer block shape `B`, refinement `S`, and smooth complex representation
`A i` of the actual inner Levi `(S i).Levi F.Carrier`. No admissibility,
irreducibility, finite length, or finite-dimensionality is assumed.

The namespace `Langlands.Parabolic.RefinedInductionTensor` names the
intermediate objects: `Factors` is the family of smooth inner-Levi
representations; `inducingRepresentation` is its transported external
action; `BlockFunctions` and `blockRepresentations` are the individual
normalized induction carriers and actions; `externalRepresentation` is
their external tensor action; and `RefinedFunctions` and
`refinedRepresentation` are the refined induction carrier and action.
These definitions use the existing constructions directly.
`CanonicalInverse` is the displayed pointwise equation, and `Comparison`
asserts existence of an equivalence satisfying it. The theorem statement
universally quantifies `Comparison`. Naming these objects keeps the
elaborated proposition small without changing its mathematical content.

Let `M = B.Levi F.Carrier`, let `L` be the actual subgroup
`Geometric.refinedLevi F.Carrier B S` of `M`, and write `V_i` for the
carrier of `A i`. The inducing representation is the actual external tensor
of the representations of `A i` on `PiTensorProduct ℂ V`, pulled back from
the nested product of inner Levis to `L` by
`(Geometric.refinedLeviEquiv F.Carrier B S).symm.toMonoidHom`.
The statement asserts nonemptiness of the subtype of actual
`Representation.Equiv` objects from `T.normalizedRefinedInduced B S` of
this representation to
`FiniteTensor.external (fun i => T.normalizedParabolicInduced (S i)
(A i).representation)` that satisfy the formula below. Thus it asserts
existence of an actual equivariant complex linear equivalence, together
with its canonical inverse formula, rather than accepting an equivalence
as input.

For a family of actual smooth induced functions `f_i` and `g = (g_i)` in
`M`, the inverse `J = E.symm` is required to satisfy

```
J (⊗ᵢ f_i) (g) = ⊗ᵢ (f_i (g_i)).
```

The Lean equation uses `PiTensorProduct.tprod` and `Induction.eval` on
both sides. It fixes the direction from the tensor of function spaces to
the tensor-valued function space. Pure tensors span the indexed tensor
product, so this prescription determines that inverse linear map.
The actions on both induced function spaces are right translation. The
individual covariance factors are the positive half-moduli
`T.parabolicHalfModulus (S i)`; the refined factor is
`T.refinedParabolicHalfModulus B S`, whose full positive modulus is the
product of the inner moduli in the actual coordinates. The formula uses
these existing normalizations without an additional scalar or inversion.

The field universe `uF` and coefficient-carrier universe `uV` remain
independent. The original finite tensor carrier has universe `uV`; both
induced/tensored output carriers have their natural universe `max uF uV`.
No resizing is asserted. All block shapes are quantified, including the
empty family at rank zero. In that case the groups are trivial and the
indexed tensor is the empty tensor, with its unit pure tensor; the same
equation applies. No separate nonemptiness hypothesis is imposed.

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977),
441–472, Proposition 1.9(g) and (e), printed p.445, and §2.2–2.3,
printed p.446 (PDF pages 6–7). The registered source is
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original pages were read directly. Proposition 1.9(g) gives
commutation of compact induction with an external tensor factor.
Proposition 1.9(e) identifies compact and smooth induction when the
quotient is compact; §2.3 applies this to parabolic induction.
Iterating the external-factor compatibility in the product Levi gives
the finite-family formulation here. The use of the actual refined subgroup,
its coordinate equivalence, indexed tensor carriers, the empty family,
and the displayed formula is an internal specialization and explicit
formulation of that compatibility, not a quotation of a finite-index
formula from the source.

A future proof must construct the displayed map on the actual smooth
covariant functions and prove it bijective. In particular, surjectivity
requires the compactness of the parabolic quotients and the uniform open
right stabilizers of smooth induced functions; an unrestricted
function-space tensor identity does not supply it. This module proves no
tensor-induction comparison, naturality theorem, or adjacent-block
association theorem. It provides the focused comparison statement needed
before a separate proof task.

The module compiles in the pinned Lean environment, and inspection of
`RefinedInductionTensorTheorem` confirms that it returns `Prop` with
independent universe parameters `uF` and `uV`. This checks the formulation,
not the truth of the asserted comparison.
