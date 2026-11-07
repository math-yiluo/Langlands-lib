# Local topology and Hensel lifting in an actual embedded subfield

Let `K` be a nonarchimedean local field with its supplied valuative relation
and compatible topology, and let `D` be a finite-dimensional central division
`K`-algebra. Their common universe `u` is arbitrary and their characteristic
is unrestricted. Let `L : Type uL` be a field with its original `K`-algebra
structure and an actual `K`-algebra embedding `ι : L →ₐ[K] D`; the auxiliary
universe `uL` is independent. All declarations below are in
`Langlands.CentralDivision`.

Write

```
v = localDivisionSubfieldValuation K D ι
  = (localReducedNormValuation K D).comap ι.toRingHom.
```

The integer ring `v.integer` consists of the original elements whose images
are integral in `D`. Its residue `DivisionValuation.Residue v` is its actual
quotient by the strict-value ideal.

## The compatible norm and valuation

The definition `localDivisionSubfieldAbsoluteValue K D ι` is the real absolute
value `x ↦ regularAbsoluteValue K D (ι x)`. Here the base norm is
`LocalGalois.localNormedField K`, compatible with the original valuation and
topology. The instance-reducible definition
`localDivisionSubfieldNormedField K D ι` gives `L` the corresponding normed
field structure, preserving its original field operations.

The instance-reducible definition
`localDivisionSubfieldNormedAlgebra K D ι`, with that normed field installed,
makes the original `K`-algebra action normed. The theorem
`localDivisionSubfield_norm_le_iff` states, with the same norm installed,

```
‖x‖ ≤ ‖y‖ ↔ v x ≤ v y
```

for all original `x y : L`. The theorem `localDivisionSubfield_ultrametric`
proves `IsUltrametricDist L` for this norm. These constructions and comparisons
do not require a finite-dimensionality assumption on `L`.

The instance-reducible definition
`localDivisionSubfieldValuativeRel K D ι` is `ValuativeRel.ofValuation v`.
The instance `localDivisionSubfieldValuation_isNontrivial` proves
`v.IsNontrivial` from the original scalar valuation. Thus nontriviality is
proved, rather than added as an assumption on the embedded field.

## The local field and its Henselian integer ring

With the additional hypothesis `[FiniteDimensional K L]`, the theorem
`localDivisionSubfieldIsLocalField K D ι` gives
`IsNonarchimedeanLocalField L` after installing precisely the constructed
normed field and valuative relation. It asserts compatibility of the norm
topology with that relation, local compactness, and nontriviality.

Under the same finite-dimensionality hypothesis,
`localDivisionSubfield_henselian K D ι` proves

```
HenselianLocalRing v.integer.
```

This conclusion concerns the actual integer subring of the original restricted
valuation; it does not replace it with a different ring model.

The theorem `localDivisionSubfield_hensel_lift` is the explicit lifting
consequence. Given a monic polynomial `f : Polynomial v.integer`, an element
`a₀ : DivisionValuation.Residue v`, and the conditions

```
f.eval₂ (DivisionValuation.reduction v) a₀ = 0,
f.derivative.eval₂ (DivisionValuation.reduction v) a₀ ≠ 0,
```

it proves the existence of an original `a : v.integer` with `f.IsRoot a`
and `DivisionValuation.reduction v a = a₀`. In particular the lifted root
has the specified residue class in the actual quotient.

## Implemented proofs and internal provenance

This is internal derived content from the imported actual division-algebra
valuation, normalized determinant norm, and Mathlib's finite-dimensional
topology, local-field completeness, and Henselian-ring results.

Pullback preserves multiplication, nonnegativity and the triangle inequality.
The zero test uses injectivity of the original field embedding. Compatibility
with the original scalar action follows from the scalar restriction formula
for the normalized determinant absolute value. Its ultrametric inequality
pulls back along `ι`.

For norm order, the normalized absolute value compares exactly as the absolute
value of the regular determinant norm. The base norm order agrees with the
base valuation order. The regular determinant valuation is the positive
reduced-degree power of the canonical reduced-norm valuation; cancelling that
positive power gives the exact comparison for `v`.

The norm comparison makes `NormedField.valuation` compatible with the valuative
relation obtained from `v`. The usual norm valuation topology therefore
supplies `IsValuativeTopology`. Finite-dimensional properness over the complete
locally compact base gives local compactness of `L`. To prove nontriviality,
take an original nonzero scalar of value less than one. Its image in `L`
is nonzero, and its restricted value is the positive reduced-degree power
of that scalar's original value, hence is still less than one.

The intrinsic valuation of this local field and `v` are equivalent, so their
integer subrings are equal as subrings of the original `L`. Mathlib's
`IsNonarchimedeanLocalField` instances give adic completeness of the intrinsic
integer ring at its maximal ideal. `IsAdicComplete.henselianRing` supplies
the root-lifting property there; a unit derivative remains a unit in the
quotient. Transport along equality of the integer subrings proves
`localDivisionSubfield_henselian`.

Finally, the actual quotient for `v` inherits commutativity from the original
commutative integer ring. Combining it with the existing quotient division-ring
structure gives a field without changing its operations.
`HenselianLocalRing.TFAE`, applied to the actual surjective reduction
homomorphism, gives the displayed simple-root lifting theorem.

## Scope

Every finite embedded field has the constructed local-field structure and
Henselian actual integer ring. No separability or characteristic restriction
is imposed. This pair does not construct an unramified extension, compute
residue or ramification degrees, establish cyclicity or reduced-degree
maximality, or prove local SK1 or local Kneser–Tits.
