# Actual Pi-zero loci under structural base change

Worker 225. This derived unit proves inverse-image equality for the actual
Pi-zero loci of Deligne line-sheaf data. It combines the actual fibre
comparison of `DeligneFibreBaseChange` with the field-extension
zero-reflection theorem of `StructuralLineZeroReflection`.

The motivating original is Drinfeld, *Coverings of p-adic Symmetric
Regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4). The graded
structural sheaf has invertible homogeneous components and a degree-one
operator Pi. At the beginning of printed p.110, `S_i` is the set of zeros
of `Pi : T^i → T^(i+1)` used in condition (a). The results here are derived
compatibility lemmas for those actual point sets. They do not assert the
special-formal-module construction or Proposition 2.4 in Section 2 B,
printed p.110.

## Actual vanishing and inverse-image equality

All declarations are in `Langlands.DeligneFormalSpace.LinePiSheaf`.
Let `S` and `S'` be schemes in one universe, let `f : S' ⟶ S` be arbitrary,
let `d` be a positive natural number, let `a` be an actual global section
of the structure sheaf of `S`, and let `M : LinePiSheaf d S a`.
The pullback is the existing structural pullback `M.pullback f`, whose
homogeneous parts are actual split-range subsheaves. Each original and
pulled homogeneous component is locally the structure module.

`fibrePi_pullback_eq_zero_iff` proves, for every `i : ZMod d` and `x : S'`,
that the actual fibre Pi map of `M.pullback f` at `x` is zero if and only if
the original fibre Pi map of `M` at `f x` is zero. Both fibres are defined
by actual module-sheaf pullback along the canonical maps from the
spectra of the respective residue fields.

The implemented proof has two steps. First, the actual fibre comparison
and Pi square give equivalence with zero of the pullback of the original
fibre Pi map along

```text
Spec.map (f.residueFieldMap x) : Spec κ(x) → Spec κ(f x).
```

Second, the original homogeneous fibre sheaves are line sheaves, by
pullback of their actual local trivializations. The unconditional
field-extension zero-reflection theorem therefore removes this last
scalar pullback. No faithfulness assumption or alternative fibre
presentation is supplied as a premise.

`piZeroLocus_pullback` applies this equivalence pointwise and proves

```text
(M.pullback f).graded.piZeroLocus i = f ⁻¹' M.graded.piZeroLocus i.
```

This is equality of actual underlying point sets. It imposes no flatness,
finite-presentation, nilpotence or local-field hypothesis on `f`.
The line condition is essential to the implemented reflection argument;
this theorem does not claim the same result for the more general
`GradedPiSheaf` without line hypotheses.

## Map of zero-locus subspaces

`piZeroPullbackMap` is the continuous map from the pulled Pi-zero-locus
subspace to the original one, sending `x` to `f x`. Membership is justified
by the preceding vanishing equivalence, and continuity follows from
continuity of `f` and the subtype topology. `piZeroPullbackMap_apply`
records its underlying point formula.

These subspaces are `TopCat` objects with their actual subspace topology.
No scheme structure on a zero locus, universal object, representability
or descent theorem is asserted. Transport of condition (a), the remaining
admissibility conditions and the admissible Nilp functor are successor
work.
