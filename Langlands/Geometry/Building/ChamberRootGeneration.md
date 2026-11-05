# Actual root groups in the chamber and zero-normalizer join

For a nonarchimedean local field `F : Type u`, an affine group scheme `G`,
and `P : ParahoricBuildingData G`, this internal construction assumes precisely
`P.apartment.SatisfiesApartmentAxioms P.centralizer`. For every actual chamber
`C` and relative root `a`, `rootGroupChamberInclusion` is the monoid homomorphism

```
rootGroupPoints P.i a →*
  ↥(P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup)).
```

It preserves the underlying rational point by definition, as recorded in
`rootGroupChamberInclusion_coe`. Its construction uses the proved inequality
`rootGroup_le_parahoric_sup_zeroNormalizer`. All declarations are polymorphic
in `u`. This module establishes the root-group containment step, not generation
of the whole zero subgroup.

## Positive powers in the simply connected image

`exists_positive_power_cocharPoint_mem_simplyConnectedImage` proves that the
positive derived cocharacter supplied by `ApartmentRootCover` has a positive
integer exponent `m` for which every evaluated point raised to `m` lies in
`P.simplyConnectedImage`. The chosen cocharacter factors through the supplied
actual derived subgroup. `CentralIsogeny.KernelTorsion` gives a positive exponent
`N` killing the actual central-isogeny kernel; `CentralIsogeny.PowerLift` then
lifts the composite with multiplication by `2*N`. Composing with the actual
derived inclusion and evaluating the multiplication morphism proves the claim
with `m = 2*N`.

## Contraction into the chamber root fixer

For each root, choose a field unit `t` whose field powers converge to zero.
For the positive exponent above put `s = t^m` and `z = χ(s) = χ(t)^m`.
The preceding lift puts `z` in the simply connected image, hence in the actual
zero subgroup. Since `z` is a torus point, it centralizes the torus on every test
scheme, so it also belongs to the actual torus normalizer.

The actual root group lies in the dynamic unipotent subgroup of `χ` because
the root-cocharacter pairing is positive. The published cocharacter contraction
shows that `z^n * g * (z^n)⁻¹` converges to the identity for every root-group
element `g`. Full torus stability keeps each conjugate in the same actual root
group. In its subspace topology, the depth-zero filtration at any chamber point
is an open subgroup by the topology-compatible apartment axiom. Thus some
conjugate belongs to that filtration. Facet constancy identifies it with the
chamber root fixer, which lies in the chamber parahoric.

Both `z` and this conjugate belong to the displayed join. Conjugating back
inside this subgroup puts `g` there and supplies the inclusion homomorphism.
In particular, the argument retains the intersection with the actual zero
subgroup throughout.

## Provenance and scope

This is an internal derived construction and proof from the named published
Library results. It does not claim an independent reading or formalization of
an original-literature passage. It changes neither the exact published
`ChamberParahoricGenerationStatement` nor its hypotheses. Rational Bruhat
covering and generation of the full zero subgroup remain separate obligations.
