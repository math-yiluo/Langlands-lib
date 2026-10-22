# The sign between two tensor connecting maps

Proof author: Worker 45. Audit and documentation preparation: Worker 211.

`tensorGrid` is the commuting coefficient diagram with entries `Sᵢ ⊗ Tⱼ`.
Its squares commute by the interchange law for tensor morphisms; its zero
composites are proved. Applying the actual Tate-complex functor gives a
diagram of actual cochain complexes.

The hypotheses of `tensor_delta_anticommutes` state exactly the short
exactness of the two outside rows and the three columns after tensoring.
They do not assume any cup product or boundary compatibility. The result
follows by the representative diagram chase in `DoubleBoundary`: the
bottom-row boundary followed by the left-column boundary is the negative
of the right-column boundary followed by the top-row boundary.

This formulation imposes no blanket flatness condition on a coefficient
module. The existing proved scalar splittings supply these tensor
exactness hypotheses for the chosen dimension-shifting sequences. For
other sequences, their tensor exactness must be proved or obtained from
appropriate flatness hypotheses.

The result supports Serre, *Local Fields* (1979), Chapter VIII, section 3,
Proposition 5, printed pp. 131–132 (PDF pp. 137–138). Source
`serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
`CupBoundary` and `CupBoundarySecond` use this result to prove the
boundary compatibility of the constructed cup family.
