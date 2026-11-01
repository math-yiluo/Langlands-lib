# Actual generalized-weight support and common eigenvectors

Proof by Worker 189. This module proves the unchanged published proposition
`Langlands.CommutingTupleGeneralizedWeightSupportStatement.{u}` with the closing
theorem `Langlands.commutingTupleGeneralizedWeightSupport`.

The proof works on the actual block `W = generalizedWeightBlock A c`.
For the forward implication, nonzero `W` makes its carrier nontrivial.
The tuple entries commute, and the published block-invariance theorem makes
each entry preserve `W`. Thus the scalar differences
`N_i = (A_i - algebraMap ℂ (Module.End ℂ V) (c i))|W` are actual endomorphisms
of `W`. They commute because the original entries commute and scalar maps
are central. Since `W` lies in the maximal generalized eigenspace of `A_i`
at `c i`, Mathlib's nilpotence theorem on that eigenspace, followed by its
restriction theorem, proves that each `N_i` is nilpotent.

The published internal lemma
`Langlands.DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero` gives
a nonzero `w : W` annihilated by all `N_i`. Coercing to `V` preserves
nonzeroness and gives `A_i w - c_i • w = 0`, hence the required simultaneous
eigen-equations for the original tuple.

For the reverse implication, each eigen-equation puts the supplied vector
in the corresponding ordinary eigenspace, hence in its maximal generalized
eigenspace by `Module.End.eigenspace_le_maxGenEigenspace`. The vector
therefore belongs to their intersection, and its nonzeroness proves
that the actual block is nonzero.

The arbitrary carrier universe, every natural rank, every unit label and
the zero space are retained. For rank zero the block is the whole space:
the family of differences is empty, and the common-kernel lemma chooses
any nonzero vector when the space is nonzero. For zero `V`, all blocks
are zero and no nonzero vector exists. Nontriviality of the block is
derived only within the forward implication.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.III, printed
pp.279–280 / one-based PDF285–286. Both source pages were read as text and
rendered images. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Printed p.279 lists the characters arising from all common eigenvalue tuples;
printed p.280 uses the corresponding simultaneous triangular blocks.
This theorem supplies the derived, basis-free identification of that
common-eigenvalue support with the actual generalized-weight intersections.
Its proof uses scalar differences and common kernels, without choosing
a triangularization basis or using a decomposition.

The restriction and commutation arguments follow the published
`Langlands.Representation.Exponents.DualEigenfunctionalExistence` module by
Worker 23, whose common-kernel theorem is imported by Lean name. The present
proof applies that theorem directly on the block rather than on its dual.
The scalar-difference nilpotence theorem is a Mathlib result.

The supplementary registered source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`,
was checked at PDF18–19. Its C.III correction adds parentheses to a later
scalar-times-unipotent power and does not change the support assertion.
