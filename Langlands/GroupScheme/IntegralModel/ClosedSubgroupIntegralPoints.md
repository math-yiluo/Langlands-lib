# Integral points of closed subgroups of an integral model

Let `R` be a domain, `K` its specified fraction field, and
`M : IntegralModel R K G` a supplied model of the group scheme `G` over
`Spec K`. All rings and schemes use one arbitrary universe `u`. This module
shows that a closed subgroup `H` of the model `M.group` cuts out its own
integral points: an integral point of the model whose generic image lies in the
generic fibre of `H` already comes from an integral section of `H`.

## The kernel of the generic point

`ker_specAlgebraMap` states that the ideal-sheaf kernel
`(Spec.algebraMap R K).ker` of the morphism `Spec K ⟶ Spec R` is `⊥`. It needs
only that `algebraMap R K` is injective, which holds for a fraction field. The
proof identifies the global-section map of `Spec.algebraMap R K` with
`algebraMap R K` through `Scheme.ΓSpecIso_naturality`, and uses that the kernel
of a morphism into an affine scheme is the kernel of its ring map on global
sections (`Scheme.ker_of_isAffine`).

`ker_specAlgebraMap_comp` states that for every morphism
`x : Spec R ⟶ X`, the kernel of `Spec.algebraMap R K ≫ x` equals the kernel of
`x`. This follows from Mathlib's `Scheme.Hom.ker_comp`, which identifies the
kernel of a composite with the image of the first kernel, and from the
previous statement.

## Generic images of closed subgroups

Let `H` be a group scheme over `Spec R` and `j : H ⟶ M.group` a homomorphism.

- `genericHom j` is the generic-fibre homomorphism into `G`: the pullback
  `(GroupScheme.baseChange (Spec.algebraMap R K)).map j` followed by the
  supplied generic identification `M.genericIso.hom`.
- `subgroupPointMap j` is the group homomorphism from the integral sections of
  `H` to the rational points of `G` that applies `j` and then the existing
  `M.integralPointMap`.
- `subgroupPointMap_apply` states that this equals the other route: restrict an
  integral section of `H` to its generic fibre with `baseChangeSectionHom`, then
  apply `genericHom j`. The proof is the Library naturality of
  `baseChangeSectionHom` (`baseChangeSectionHom_naturality`).
- `range_subgroupPointMap_le` states that the image of `subgroupPointMap j` lies
  in the intersection of `M.integralPoints` with the image of the rational points
  of the generic fibre of `H` under `genericHom j`.

## Integrality through a closed subgroup

`exists_eq_of_integralPointMap_eq` assumes that `j` is a closed subgroup
(`IsClosedSubgroup j`, i.e. its underlying scheme morphism is a closed
immersion). Let `x` be an integral section of `M.group` and `y` a rational
point of the generic fibre of `H` with `M.integralPointMap x` equal to the image
of `y` under `genericHom j`. Then there is an integral section `h` of `H` with
`rationalPoints.map j h = x`, whose restriction to the generic fibre is `y`.

The proof cancels `M.genericIso` to get the equality of generic points of the
model, then reads off on underlying schemes that
`Spec.algebraMap R K ≫ x.left` factors through the closed immersion
`j.hom.hom.left`. Mathlib's `Scheme.Hom.le_ker_comp` then gives that the kernel
of `j.hom.hom.left` is contained in the kernel of
`Spec.algebraMap R K ≫ x.left`, which equals the kernel of `x.left` by
`ker_specAlgebraMap_comp`. So `x.left` lifts through the closed immersion
(`IsClosedImmersion.lift`); the lift is a section of `H` over `Spec R`, it
maps to `x`, and its generic restriction is `y` because both have the same two
pullback projections (the first one after cancelling the monomorphism
`j.hom.hom.left`).

`integralPoints_inf_range_genericHom` is the resulting equality of subgroups of
the rational points of `G`: for a closed subgroup `j`, the intersection of
`M.integralPoints` with the image of `genericHom j` is the image of
`subgroupPointMap j`.

## Provenance

This is the standard fact that the integral points of a closed subscheme of a
scheme over a domain are the integral points of the ambient scheme whose generic
points lie in the closed subscheme (for affine schemes: an `R`-algebra map
`A → R` that kills the ideal of the subscheme after composing with the
injective map `R → K` already kills it). It is internal; the proof uses only
Mathlib's ideal-sheaf kernels and closed-immersion lifting and the Library
`IntegralModel` and `baseChangeSectionHom` interfaces, and follows the pattern of
the private closed-immersion lifting lemmas in
`Langlands.Global.AdelicFixedModelClosedImmersionProof`. It is an input for
comparing torus and root-group points inside `M.integralPoints`; the module
proves no statement about tori, root groups, buildings or stabilizers.
