# Actual quotient maps in the split-radical reduction

Author: Worker 1478.

This internal application of the homogeneous quotient factorization construction
works over every field `k : Type u`, at arbitrary universe `u`. It retains the
published pseudo-parabolic predicate. For a supplied pseudo-parabolic inclusion
`i : P ⟶ G` and represented split ground-field unipotent radical `n : N ⟶ G`,
`IsPseudoParabolicSubgroup.splitRadical_le` proves containment of their ranges
on every relative scheme test. Its proof uses a ground-field radical from the
pseudo-parabolic product presentation: the split radical lies in that radical,
and the represented product contains the latter.

Suppose an actual group homomorphism `f : G ⟶ H` is supplied with
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range n) f` and a quasi-compact
underlying scheme map. Let `q : G.X ⟶ Q` be an actual supplied relative map
with exactly the right-coset fibers for `i` on every relative scheme test.
The exact scheme-kernel equality in the fppf quotient predicate, combined with
the containment above, gives `kernel_le`. The fpqc effective-epimorphism
instance then permits the existing factorization construction to give
`quotientMap : H.X ⟶ Q`. Its target is the original supplied `Q`.
`fac_quotientMap` states `f.hom.hom ≫ quotientMap = q`, and
`quotientMap_unique` proves uniqueness from this equation.

The public helper `quasiCompact_of_surjective_comp` proves descent of
quasi-compactness along a surjective first map and is also used by
`PseudoParabolicQuotientReductionProof`.

`quotientMap_surjective` reflects surjectivity of the original `q` through the
factorization. `quotientMap_quasiCompact` does the same for quasi-compactness:
for a compact open subset of `Q`, its preimage under the reduced projection
is the continuous image under the surjective map `f` of its compact preimage
under `q`. The theorem `groupQuotient_smooth` applies the published
`RelativeRoot.IsFppfQuotient.smooth_of_smooth_kernel`: the closed inclusion `n`
represents its own range, and the split-radical predicate supplies smoothness
of `N`. Thus `f` is smooth from the supplied data, with no extra premise.
If `q` is smooth, `quotientMap_smooth` applies the published smooth
source-descent theorem along this smooth surjective `f`.

For a supplied pseudo-parabolic inclusion `j : K ⟶ H`, assume the all-test
full preimage equality

```lean
SubgroupFunctor.range i = (SubgroupFunctor.range j).comap f
```

Then `quotientMap_fibers` gives the exact right-coset fiber condition for `j`
on every relative test scheme, including nonaffine and nonreduced schemes.
It applies the previously constructed factorization theorem; closedness of
`j`, obtained from its pseudo-parabolic predicate, supplies its monomorphism.
Consequently, if the original `q` is smooth, surjective and quasi-compact,
the reduced map retains all three properties and the exact
all-test fibers. Any separatedness and finite-type assumptions on `Q` still
concern the very same scheme with the same structure map.

Finally, `localSections_of_quotientMap` assumes actual lifting of every map
from every affine relative test scheme through `f`. Given algebraic sections
of `quotientMap` near every topological point of `Q`, the published affine
refinement and composition construction lifts these sections through `f`.
The factorization equation identifies the composite projection with the
original `q`, proving local sections of that supplied projection at every
one of the original topological points. There is no infinitude hypothesis
in this conditional transfer; obtaining the input sections is separate.

The provenance is internal: the existing ground-field radical containments,
actual homogeneous quotient factorization and all-test fiber descent,
continuous images of compact sets, the published smooth-kernel quotient and
smooth source-descent theorems, and affine refinement and composition of actual algebraic sections.
This unit does not construct the group quotient by the split radical, prove
that its kernel-free quotient has trivial split radical, construct a subgroup
`j` or prove that it is pseudo-parabolic with the full preimage equality, or
establish affine-test lifting through `f`. These structural and torsor inputs
remain explicit obligations. No unconditional local-section theorem or proof
of `PseudoParabolicQuotientRationalLiftingStatement` is claimed.
