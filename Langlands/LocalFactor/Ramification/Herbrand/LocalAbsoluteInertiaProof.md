# The index-zero absolute upper group

`Langlands.Ramification.Local.absoluteUpperInertia` proves `AbsoluteUpperInertia K Ω`
from `Herbrand.LocalAbsoluteStatement`. For a nonarchimedean local field `K` and a
specified separable closure `Ω` in an independent universe, it identifies
`localAbsoluteUpperRamificationGroup K Ω 0` with
`LocalGalois.SepClosed.absoluteInertia K Ω`, the kernel of the residue projection.
The theorem applies in either characteristic.

## Proof

For a finite Galois intermediate field `L`, `finiteValuation_isEquiv` compares the
valuation of `localTopologicalData K L` with the pullback to `L` of the spectral
valuation of `Ω`. The finite valuative relation is induced by the spectral valuation
of `L`. The lemma `spectralNorm.eq_of_tower` identifies the spectral norm on `L`
with the restriction of the spectral norm on `Ω`, using `K` as the norm base in both
cases. Thus an element of `L` is a finite integer exactly when its spectral norm in
`Ω` is at most one. A finite integer lies in the maximal ideal exactly when that
norm is strictly less than one.

The lemmas `upperRamificationGroup_zero` and `lowerRamificationGroup_zero` identify
the finite upper group at zero with the finite lower group at zero. By
`mem_lowerRamificationGroup`, a restriction of `σ` lies in this group exactly when
the difference between the image of each finite integer and the integer itself
lies in the maximal ideal. The restriction agrees with `σ` under `L → Ω` by
`AlgEquiv.restrictNormal_commutes`. The finite test is therefore
`spectralNorm K Ω (σ x - x) < 1` on the integers of `L`.

The lemma `LocalGalois.mem_inertia_iff` expresses closure inertia as equality of
residues for all closure integers. Subtracting and applying `residue_eq_zero_iff`
gives the same strict norm test on the integers of `Ω`. If the test holds at all
finite levels, each closure integer `x` can be tested in
`FiniteGaloisIntermediateField.adjoin K {x}`, since `subset_adjoin` places `x` in
that field. Conversely, the test on closure integers applies to each finite
integer through `L → Ω`. This gives equality by subgroup extensionality.

## Source

Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979), registered as
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Chapter IV, §1, Proposition 1, p. 62 identifies the finite zeroth lower group with
inertia. Chapter IV, §3, pp. 73–74 gives the upper numbering at zero, and Remark 1
on p. 75 defines the infinite upper filtration from the finite groups. The proof
uses the spectral norm to compare the Library's finite and closure residue tests.
