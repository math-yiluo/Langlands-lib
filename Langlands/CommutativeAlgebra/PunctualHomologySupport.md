# Ideal-power torsion in homology and reversed duals

Authors: Worker 1015 and Worker 975.

For commutative rings `R,S : Type u`, a flat ring map `φ : R →+* S`,
a cochain complex `K` of `R`-modules, and any integer `n`,
`flatBaseChangeHomologyIso` constructs the actual isomorphism

```
((baseChange φ).obj K).homology n ≅
  (ModuleCat.extendScalars φ).obj (K.homology n).
```

It uses Mathlib's preservation of finite limits by flat scalar extension
and `ShortComplex.mapHomologyIso`. It requires no boundedness or
finiteness assumption on `K`.

The general support helpers work over a commutative ring `B`. For a
finite module, elementwise annihilation by powers of one element implies
annihilation by a single power: choose finitely many generators and take
the maximum of their exponents. Over a noetherian ring, applying this to
each element of an ideal `m` puts `m` inside the radical of the module
annihilator; finite generation of `m` then yields
`m ^ N ≤ Module.annihilator B M` for some natural number `N`.

`map_annihilator_le` transports annihilators through scalar extension,
by checking pure tensors. `exists_smul_eq_zero_of_isZero` uses the
localization tensor product to show that vanishing after localization
forces each original element to be killed by some member of the
multiplicative set. Specializing to `B_f` yields elementwise annihilation
by powers of `f`. The homology of a strictly perfect complex over a
noetherian ring is finite, since its cycles embed into a finite term and
surject onto its homology. Together with flat base change, these helpers
prove `exists_pow_le_annihilator_homology`: if localization at every
element of `m` makes the complex acyclic, each homology module is killed
by a power of `m`. The exponent may depend on the homology degree.

Conversely, `acyclic_away_of_pow_le_annihilator` shows that ideal-power
torsion homology vanishes after inverting an element of the ideal.
The image of a suitable annihilator element is a unit, so the extended
annihilator is the whole ring and the extended homology is zero.

Finally, for a bounded finite free complex `C`, any integer `g`, and any
ideal `m` of a noetherian ring,
`exists_pow_le_annihilator_homology_reversedDual` transports ideal-power
torsion from every homology module of `C` to every homology module of
`reversedDual g C`. Invert an element of `m`, apply
`isZero_homology_baseChange_reversedDual_of_acyclic`, and recover an
ideal power in the annihilator using the preceding support criterion.
This conclusion does not require that `m` be maximal or that the ring
be regular local.

This is internal supporting algebra. The flat-homology, finite-homology,
and localization/support helpers are adapted from Worker 975's local
algebra draft, with attribution retained. The final transport theorem
combines them with the reversed-dual scalar-extension and contraction
constructions. The module does not prove the punctual-complex
proposition or assert regular-local finite-length acyclicity.
