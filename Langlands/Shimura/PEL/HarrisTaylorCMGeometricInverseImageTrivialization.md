# Exact-cover trivialization of inverse-image CM coefficient systems

Author: Worker 57.

This internal construction gives invariant evaluation and exact-cover
trivializations for the existing inverse-image CM coefficient system. A single
source cover trivializes the complete diagram of exponents reachable from its
index, with the original full-lattice coefficient reductions on every arrow.

## Inputs and objects

All arithmetic and geometric inputs are exactly those in
[HarrisTaylorCMGeometricInverseImageComparison](HarrisTaylorCMGeometricInverseImageComparison.md).
They include the universe-zero totally real and CM fields, the central simple
unitary datum D, signature charts C and the displayed algebra structures,
finite-dimensional coefficient representation ρ, small level U, rational finite
place p and nonzero m. The exact representability premise q and named tensor,
Picard, duality, polarization, Weil-transition, adelic, torsion, relative dual
existence and geometry, and geometric rigidity premises remain explicit.

Write Xbar for the actual geometric CM scheme at U, Jbar for its small-etale
topology, Ybar for the exact geometric coefficient-cover diagram, and
`R = HarrisCoefficientIntegers K p` for the full integral coefficient ring.
The original equivariant coefficient diagram M is
`cmHarrisCoefficientDiagram D ρ p U m hm`, with its full stable-lattice
reductions and original residual group actions.

Let F be `cmHarrisGeometricCoefficientSystem`, the existing inverse image of
the original coefficient system along the actual scheme fiber-product
projection. Let A be `cmHarrisGeometricAssociatedCoefficientSystem`, formed by
association on the exact geometric covers with the same coefficient diagram.
The imported whole-system comparison is
`e : F ≅ A = cmHarrisGeometricCoefficientSystemAssociatedIso ...`.
It is constructed from arbitrary scheme inverse image and the canonical
cartesian cover comparisons; it is not an input premise. For an etale object
Z over Xbar, put `L_Z = Jbar.overPullback (ModuleCat R) Z`.

## Evaluation and local trivialization

For any actual map `a : Z ⟶ Ybar_k`,
`cmHarrisGeometricCoefficientEvaluationAlong k a` is the morphism

```text
L_Z(F_k) → L_Z(constantSheaf_Jbar(M_k))
```

given by `L_Z.map(e.hom.app k)` followed by the published invariant evaluation
`etaleAssociatedEvaluationAlong Xbar Ybar M k a` on A. Thus evaluation uses the
same cover and coefficient action as the exact geometric associated system.

`cmHarrisGeometricCoefficientTrivializationAlong k a` is an isomorphism with
this forward map. It composes `L_Z.mapIso(e.app k)` with the existing exact
geometric associated-coefficient trivialization along a. The `_hom` formula
is reflexivity. Taking Z = Ybar_k and a its identity gives the trivialization
on the exact coefficient cover itself; its covering property is supplied by
the imported geometric coefficient diagram.

For a transition `f : i ⟶ j`, write `b_f = Ybar.obj.map f` and let c_f be the
constant-sheaf morphism induced by the original reduction `M.obj.map f`.
The theorem `cmHarrisGeometricCoefficientEvaluationAlong_transition` proves

```text
L_Z.map(F.map f) ≫ eval_j(a ≫ b_f)
  = eval_i(a) ≫ L_Z.map(c_f).
```

The proof combines functoriality of L_Z, naturality of e.hom at f, and the
published evaluation transition formula for the exact geometric associated
system. Thus the result retains the specified reductions rather than choosing
new transition maps after trivializing.

## Simultaneous source-cover trivialization

For `k : ℕᵒᵖ`, define

```text
cmHarrisGeometricCoefficientSourceSystem k
  = Under.forget k ⋙ F ⋙ L_Ybar_k.
```

Its objects are all arrows k → i and its morphisms are the original compatible
index arrows. In the opposite natural-number category these are precisely
the exponents at most k.unop. The source is a diagram of actual sheaves on
the over-site `Jbar.over Ybar_k`.

`cmHarrisGeometricCoefficientSourceAssociatedIso k` restricts and localizes e
to compare this source diagram with the existing associated source diagram.
The `_hom_app` lemma identifies each component with `L_Ybar_k.map(e.hom_i)`.

The entry definition `cmHarrisGeometricCoefficientSourceTrivialization k`
composes this isomorphism with the existing associated source trivialization.
Its target is the unchanged `cmHarrisGeometricConstantCoefficientSourceSystem`,
which restricts and localizes the constant sheaves of the original full
coefficient diagram. The `_hom_app` formula evaluates at i along the exact
forgetting map `Ybar.obj.map i.hom`. The `_inv_app` formula first reverses the
associated source evaluation and then applies the localized inverse of e.
Both formulas follow by reflexivity.

The `_transition` and `_inv_transition` theorems are naturality of this
single diagram isomorphism in both directions. They identify every localized
transition of F with the constant sheaf of the original lattice reduction.
No single finite cover is claimed to trivialize all larger exponents.

## Provenance and remaining scope

This is internal composition of the published arbitrary-morphism CM comparison
and the exact geometric associated-system evaluation and source trivialization
from [HarrisTaylorCMGeometricAssociatedSystem](HarrisTaylorCMGeometricAssociatedSystem.md).
It adds no external-literature assertion. The original-source provenance of
arithmetic, covers and moduli remains in the paired imported modules.

The exact representability theorem, rigidity, canonical-model geometry and
other named prerequisites remain obligations. No new derived-category,
cohomology, quotient-ring scalar, inverse-limit or lisse-adic theorem is
asserted, and the host task remains incomplete.
