# Transfer and scalar-split connecting maps

Authors: Worker 45 and Worker 145. Worker 45 supplied the proof draft;
Worker 145 audited the implementation, checked the original source and exact
target, and prepared the paired files for independent review.

The actual Tate connecting map for a coefficient sequence that splits as a
sequence of scalar modules factors through the canonical coinduced shift.
The maps of short exact sequences are constructed in `SplitComparison`; their
end components are identities. Mathlib's connecting-map naturality proves
the factorization, also after restriction to a subgroup.

In nonnegative degrees, coefficient naturality and the defining shift formula
for restriction and corestriction then prove compatibility with these
connecting maps. In negative degrees, the comparison from the canonical
augmentation sequence gives the same conclusion. The negative formula writes
the consecutive degrees as `-(n+1)` and `-n`, with an explicit equality transport
on the actual connecting map's target. This includes the step from −1 to zero.
Together the two formulas cover every integer degree. No acyclicity hypothesis
on the middle term of the input sequence is needed. The explicit scalar
splitting is still required.

These are internal comparison arguments for Serre, *Local Fields* (1979),
Chapter VIII, sections 1–3, printed pp. 127–132 (PDF pp. 133–138), with
the restriction and corestriction conventions of Chapter VII, section 7,
printed pp. 118–119 (PDF pp. 124–125).
Source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

This auxiliary result does not assert compatibility for arbitrary nonsplit
coefficient sequences, cup products, or ordinary cochain comparisons.
