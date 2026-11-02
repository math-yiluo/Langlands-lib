# Linear changes of generating sections

Let `K : Type u` be any commutative ring, `p : X → Spec K` a scheme morphism,
`L` a line bundle on `X`, and `s` an ordered family of `n+1` global sections.
For a `K`-linear endomorphism `f` of `Fin (n+1) → K`,
`linearChangeSections p s f` is the actual section family

```text
t_i = sum_j scalarsFromBase p (f (Pi.single j 1) i) • s_j.
```

Here the coefficients are pulled back to global functions on `X`. No field,
nontrivial-ring, affine-source, reducedness or noetherianity hypothesis is
required; `n=0` is allowed. The indices retain their order.

`linearChangeSections_id` and `linearChangeSections_comp` prove the identity
and composition laws on the actual sections. First changing by `f` and then
by `h` gives the change by `h.comp f`. The composition proof distributes the
finite sums and scalar actions, then uses standard-coordinate basis
reconstruction to identify the coefficient of each original section.
`linearChangeSections_symm` consequently recovers the original family after a
change by a linear equivalence `e` followed by its inverse.

`linearChangeSections_generate` proves preservation of generation at every
point of the scheme. If every transformed section had zero value on the
residue-field fibre at some point, the inverse-change formula would express
each original section as a linear combination of those transformed sections.
Additivity and scalar compatibility of actual section pullback would make
every original residue value zero, contradicting the original generation
hypothesis. This argument uses actual residue-field sections at all points,
without a closed-point restriction.

`chartRingHom_comp_linearSubstitution` compares polynomial evaluation after
the actual graded substitution with evaluation at the ratios of the
transformed sections to an original frame. Polynomial ring-homomorphism
extensionality reduces the comparison to constant polynomials and variables.
Constants are fixed by substitution. On variables, expansion of the
functional's degree-one polynomial and linearity of section ratios give the
required sum with exactly the displayed coefficients.

On a locus where both `s_i` and `t_j` are frames,
`chartRingHom_linearChange_scale` proves that substituted evaluation of a
homogeneous degree-`m` polynomial equals its transformed chart evaluation
times `(t_j / s_i)^m`. The denominator multiplication identity for section
ratios identifies every variable's evaluation, and homogeneous evaluation
then gives the degree power. The frame ratio is a unit.

`pointMap_linearChange` proves equality of actual chart scheme morphisms:
the original point map followed by `linearAction K n e` equals the point map
of the transformed family. Change the original chart to the chart of the
substituted variable `X_j`, use `chartMap_comp_projMap` for the actual graded
substitution, and apply homogeneous-rescaling invariance with the frame ratio.
Thus the comparison includes the structure-sheaf maps.

`linearSystemMap_linearChange_of_generate` glues this equality on intersections
of the two frame covers when both generation proofs are given. Finally,
`linearSystemMap_linearChange` uses the proved preservation of generation to
obtain, from the original generation hypothesis alone,

```text
linearSystemMap p hs ≫ linearAction K n e
  = linearSystemMap p (linearChangeSections_generate p s e hs).
```

The convention agrees with the covariant action of `e` on coordinate vectors;
no inverse or transpose is inserted in the displayed coefficients.

This is internal derived infrastructure. It combines the existing actual
section ratios and linear-system morphisms with the projective linear
substitution, graded-chart functoriality, finite basis reconstruction and
section pullback. It proves no immersion, projective-bundle gluing, or moduli
representability result and uses no representing-family premise.
