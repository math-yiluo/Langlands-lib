# Proof: parabolic subgroups of a reductive group and of its adjoint quotient

Authors: Worker 5600 (clauses 1, 2, 4 and this assembly) and Worker 5647
(clauses 3 and 5).

This module proves `Langlands.GroupScheme.AdjointParabolicCorrespondenceStatement`
(Conrad, *Reductive group schemes* (2014), Exercise 5.5.8) in every universe,
with no additional hypotheses. The proof is our own route through Library
results. It is split over three helper modules:

- `Reductive/ParabolicContainsCenter`: clause 1 and the descent lemma for
  clause 4 (Worker 5600).
- `Reductive/AdjointParabolicImage`: `G^ad` is affine over the base, and
  clause 2 (Worker 5600).
- `Reductive/AdjointParabolicPreimage`: clauses 3 and 5 (Worker 5647).

Each helper module's Markdown explains its proofs.

## `adjointParabolicCorrespondence_of`

Hypothesis: `hquot : RelativeCentralMultiplicativeTypeQuotientStatement`. This
is the existence of an affine fppf quotient of a smooth affine group with
connected geometric fibres by a closed central subgroup of multiplicative type.

Conclusion: `AdjointParabolicCorrespondenceStatement`.

Proof. Fix a reductive `G` over `S`.

1. Clause 1, `center G ≤ range i` for every relative parabolic `i`, is
   `IsRelativeParabolicSubgroup.center_le_range`.
2. Fix an fppf quotient `q : G ⟶ Gad` by `center G`. By
   `AdjointParabolicCorrespondence.isAffineHom_of_isFppfQuotient_center`
   (which uses `hquot`), `Gad` is affine over `S`. This instance is the extra
   hypothesis of the clause 3 and 5 lemmas.
3. Clause 2 is `AdjointParabolicCorrespondence.exists_parabolic_image hquot`.
4. Clause 3 is `AdjointParabolicPreimage.exists_relativeParabolic_preimage`.
5. Clause 4: relative parabolics are monomorphisms, and `q` is flat,
   surjective and locally of finite presentation. So
   `SubgroupFunctor.range_eq_of_comap_eq_of_fppf` turns equality of the
   inverse images under `q` into equality of the ranges.
6. Clause 5 is `AdjointParabolicPreimage.isRelativeBorelSubgroup_iff_of_comap_eq`.

## `adjointParabolicCorrespondence`

Conclusion: `AdjointParabolicCorrespondenceStatement.{u}`, with no hypotheses.

Proof. Apply `adjointParabolicCorrespondence_of` to the published proof
`relativeCentralMultiplicativeTypeQuotient` of
`RelativeCentralMultiplicativeTypeQuotientStatement` (module
`Langlands.GroupScheme.RelativeCentralMultiplicativeTypeQuotient`).
