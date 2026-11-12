# Coefficient automorphisms and finite Galois closed extension loci

Author: Worker 114. This is a derived supporting unit for
`HenselianExtensionPointEmbeddingStatement`. Its declarations are in the
`ExtensionClosedRange` namespace. It proves finite Galois descent of points,
constructs the coefficient-automorphism action on base-changed point carriers,
and proves closedness of the rational locus for finite Galois henselian normed
extensions. It does not claim the arbitrary-extension closedness conclusion.

## Algebraic descent

`exists_desc_of_finite_galois_fixed` applies to any finite Galois extension
`L/K` of fields in universe `u`, any separated algebraic space `X` over `K`,
and any `x : X(L)` fixed by every `K`-automorphism of `L`. It produces
`y : X(K)` whose coefficient extension is `x`. No topology, local finite type,
or henselianity is assumed here.

The implementation uses the actual self-pullback of the finite etale cover
`Spec L → Spec K`. That self-pullback is etale over `Spec L`, hence reduced.
The two pullbacks of `x` have a represented closed equalizer because `X` is
separated. On each residue-field point of the self-pullback, the two morphisms
to `Spec L` differ by a Galois automorphism (`exists_galois_of_hom`), so the
fixedness hypothesis gives a lift to the equalizer. Thus the equalizer's
closed immersion is surjective. Its reduced target makes it an isomorphism,
and the published single-cover fppf descent theorem produces `y`.

## Coefficient automorphisms and topology

In the rest of the module, `K,L : Type u` are nontrivially normed fields and
`L` is a normed `K`-algebra.

`coefficientAut σ`, for `σ : L ≃ₐ[K] L`, is the actual map

`z ↦ baseChangeRingPointsEquiv.symm (RingPoints.changeRing σ.toAlgHom
  (baseChangeRingPointsEquiv z))`

on `X_L(L)`. The carrier is not replaced by a different set of points.
`coefficientAut_chartExtensionMap` proves that this action commutes with
coefficient change on charts defined over `K`.

`chartExtensionMap c` evaluates an actual finite-type etale `K`-chart over `L`
and maps it into `X_L(L)`. If `X` is locally of finite type, these maps cover
every target point (`exists_chartExtensionMap_eq`), by the published
`FieldPointEtaleLift.exists_affine_etale_point` and local finite-type
inheritance for etale chart sources.

`continuous_coefficientAut` assumes that `L` is henselian, `X` is locally of
finite type over `K`, and `σ` is isometric. The base-changed chart maps are open,
and the coefficient map on scheme points is continuous. Their compatibility
therefore proves continuity of `coefficientAut σ` for the etale-chart topology
on `X_L(L)`. This helper does not require the extension to be algebraic,
`K` to be henselian, or `X` to be separated or quasi-separated.

## Finite Galois closedness

`isClosed_range_of_finite_galois` and `isClosedEmbedding_of_finite_galois`
assume that `L/K` is finite Galois, both fields are henselian, and `X` is
separated, quasi-separated and locally of finite type over `K`. They prove
that `extensionPointMap L X` has closed image and is a closed embedding for
the respective etale-chart topologies. No completeness or separate
closed-field-image assumption is needed in this finite Galois case.

The rational locus is exactly the intersection, over all automorphisms, of
the equalizers `coefficientAut σ z = z`, by the algebraic descent theorem.
Henselian norm uniqueness makes every automorphism isometric, hence continuous
by the chart argument. The point space is Hausdorff by separatedness, so each
equalizer is closed. The existing arbitrary-extension embedding supplies the
embedding half of the final conclusion.

The derived proof uses the published fppf descent, represented equalizer,
field-point chart, scheme coefficient-continuity, and separated-space topology
results. It introduces no new source assertion or axiom. The main task retains
arbitrary-extension closedness and the exact whole-statement proof.
