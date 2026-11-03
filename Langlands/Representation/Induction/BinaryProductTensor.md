# Binary product induction and tensors

This module constructs the canonical equivalence

\[
 \operatorname{Ind}_{P}^{G}(\sigma)\otimes_k
 \operatorname{Ind}_{Q}^{H}(\tau)
 \;\simeq\;
 \operatorname{Ind}_{P\times Q}^{G\times H}(\sigma\boxtimes\tau)
\]

for smooth right-translation induction with compact left quotients. The
equivalence intertwines the actual \(G\times H\) actions and sends \(f\otimes h\)
to the function \((g,x)\mapsto f(g)\otimes h(x)\).

## Provenance and scope

This is a derived adapter for Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), V.1, printed p.288
(PDF p.54). That page defines
\(L(\omega,P)=I_{P\times P}^{G\times G}(E\otimes\check E)\) and uses its
natural identification with \(I_P^G E\otimes I_P^G\check E\).
The present module supplies the underlying binary product-induction
comparison. Its general subgroup formulation uses the already published
`Langlands.Induction.finiteProductTensorMap_bijective`; it does not repeat
the finite-product bijectivity proof.

The inducing actions here are arbitrary actions on vector spaces over a field.
No smoothness, admissibility, irreducibility or unitarity of those actions is a
premise. The induced carriers themselves are the existing `SmoothFunctions`:
left-covariant functions admitting a single open subgroup of right invariance.
The source and target carry the existing `smoothInduced` right-translation
actions.

The normalized parabolic specialization still needs the comparison of the
product half-modulus with the two factor half-moduli and the actual
Levi/unipotent product data. The module makes no claim about compact models,
smooth families on character orbits, quotient measures, or the analytic
Plancherel theorem.

## Hypotheses and universes

The main declaration `Langlands.Induction.BinaryTensor.equiv` takes:

- a field \(k\);
- topological groups \(G,H\) with `NonarchimedeanGroup` and
  `WeaklyLocallyCompactSpace` instances;
- actual subgroups \(P\leq G,Q\leq H\), with compact actual left quotients
  `LeftQuotient P` and `LeftQuotient Q`;
- \(k\)-vector spaces \(V,W\) and representations
  \(\sigma:P\to\operatorname{End}_k(V)\),
  \(\tau:Q\to\operatorname{End}_k(W)\).

The `NonarchimedeanGroup` instances include the topological-group laws.
There is no separate Hausdorff or closed-subgroup premise. These are exactly
the topological and compactness hypotheses of the imported finite-product
result. The field, two groups, and two inducing carriers have five independent
universe parameters. In particular, the binary specialization imposes no
equality between the universes of \(G,H\), or of \(V,W\).

The algebraic constructions `external`, `inducing`, and `pullEquiv` work over
an arbitrary commutative ring. `external σ τ` is the tensor action pulled
back along the two projections of \(G\times H\); `external_tmul` records its
pointwise formula. `inducing P Q σ τ` restricts the external action to the
actual subgroup `P.prod Q` through `P.prodEquiv Q`. `pullEquiv` pulls an
actual representation equivalence back along a group homomorphism.

## Construction in common universes

`Index` is `Unit ⊕ Unit`. `family` and `tuple` encode a pair as a dependent
two-coordinate family. Their group, module, topology, nonarchimedean,
weak local compactness, and compact quotient instances are obtained by
the two cases of this index.

`tensorEquiv` uses singleton indexed-tensor equivalences followed by
`PiTensorProduct.tmulEquivDep`. Its pure-tensor formula is
`tensorEquiv_tmul`. The variant `tensorEquivDep` permits an arbitrary
dependent family on this index; `tensorEquivDep_symm_tprod` and
`tensorEquivDep_tprod` give its two evaluation directions.

`groupEquiv` is the actual continuous multiplicative equivalence from
\(G\times H\) to the dependent tuple group, with inverse coordinate
evaluation. `subgroupEquiv` identifies `P.prod Q` with the actual
coordinatewise subgroup of that tuple group.

`representationFamily` places the two inducing actions at their two
coordinates. `inducingEquiv` intertwines the binary inducing action with
the indexed inducing action, using `tensorEquiv`. `inducedTensorEquiv`
does the same for the two induced carriers, using `tensorEquivDep`.
The proofs check the actions on pure tensors.

`finiteEquiv` promotes the published `finiteProductTensorMap` to a
representation equivalence by its proved bijectivity, then pulls the action
back along `groupEquiv`. `productInducedEquiv` returns from the tuple group
to the binary group by `precomposeSmoothInducedGroupEquiv`, and
postcomposes values by the inverse of `inducingEquiv` using
`smoothInducedEquiv`. Their composition with `inducedTensorEquiv` is
`commonEquiv`.

`commonEquiv_tmul_eval` unfolds this composition. The published
`finiteProductTensorMap_tprod_eval` gives the indexed pointwise formula,
and the binary tensor regrouping yields \(f(g)\otimes h(x)\).

## Transport between independent universes

The `ULift` helpers preserve actual mathematical objects:

- `liftGroupEquiv` is the continuous up/down group equivalence;
  `liftSubgroup` is the inverse-image subgroup under down, and
  `liftSubgroupEquiv` is the induced subgroup equivalence.
- `liftRepresentation` conjugates the subgroup action by the standard
  `ULift.moduleEquiv`, also pulling the action back along subgroup down.
- `liftQuotientEquiv` transports the actual right-coset relation defining
  the left quotient. It supplies `liftCompactQuotient`.
  The lift also preserves nonarchimedeanness through its open embedding
  and weak local compactness through its closed embedding.
- `liftInducedEquiv` precomposes the induced function with group up and
  postcomposes its values with module down. The forward and inverse
  formulas are `liftInducedEquiv_eval` and
  `liftInducedEquiv_symm_eval`.

`liftProductGroupEquiv` raises both group universes to their common
maximum; `liftProductSubgroupEquiv` respects their product subgroup.
`downTensorEquiv` lowers the two tensor factors after raising them to
their common carrier universe. `liftProductInducingEquiv` proves that
this lowering intertwines the pulled-back inducing action.
`liftProductInducedEquiv` performs the corresponding pre- and
postcomposition on product induction. `liftExternalInducedEquiv` lowers
the tensor of the two induced carriers using the two factor
`liftInducedEquiv` maps.

The main `equiv` applies `commonEquiv` to those lifted objects, pulls its
action back to \(G\times H\), and composes the inverse of
`liftExternalInducedEquiv` with `liftProductInducedEquiv`. All component
maps are equivalences; no new bijectivity hypothesis is introduced.

Finally, `equiv_tmul_eval` evaluates this composite on a pure tensor.
The two factor inverses give module up on values, the common-universe
formula tensors those values, and `downTensorEquiv` cancels both lifts.
Consequently the resulting formula is exactly

\[
 \operatorname{eval}(\operatorname{equiv}(f\otimes h))(g,x)
   =\operatorname{eval}(f)(g)\otimes
     \operatorname{eval}(h)(x).
\]

The internal lifts therefore introduce no change to the pointwise
product-induction map.
