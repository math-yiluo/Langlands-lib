# Standard parabolics for the diagonal torus of GL_N

Workers 185 and 163.

The theorem `Langlands.GroupScheme.generalLinearStandardParabolic` proves the
unchanged published `GeneralLinearStandardParabolicStatement`. It includes
all fields, every natural rank (including zero and one), actual relative roots,
subgroup-functor equalities on every test scheme, the specified canonical
rational-point comparisons, and unique indexing by ordered positive block
shapes. The proof needs only strict decrease of the reference cocharacter's
coordinates; the genericity hypothesis of the target is retained.

The implementation is divided among three helper modules, whose paired
Markdown explains the corresponding arguments:

- `GeneralLinearSimpleRootsProof` computes the actual positive roots from the
  published root datum. Pairing with the auxiliary weights `-i` gives every
  positive root integer height at least one. The adjacent roots have height
  one and cannot split into positive roots; a nonadjacent root splits at its
  next coordinate. Thus the actual simple roots are exactly the adjacent
  characters.
- `GeneralLinearStandardBlocksProof` translates the standard sign conditions
  into antitone weights, equal across uncut edges and strictly decreasing
  across cuts. The cut correspondence and induction along coordinate indices
  identify the weight equality classes and their order with the prescribed
  blocks. The canonical block weights satisfy the sign conditions. The
  published dynamic matrix formulas therefore give the same block parabolic,
  Levi and unipotent functors for every standard cocharacter. The inhabited
  choice-free intersections equal these functors on all test schemes.
- `GeneralLinearCanonicalPointsProof` specializes the existing algebraic
  rational-point comparison to exactly the target's matrix point homomorphism:
  `pointsEquiv` followed by entrywise transport along `Scheme.ΓSpecIso`. Its
  three subgroup equalities give the canonical comaps in the target.

The final theorem assembles these results and applies the published
`existsUnique_blockSimpleRoots` to a subset of the computed simple roots.
This last step uses the block-shape/cut equivalence and injectivity of the
actual adjacent characters; it introduces no choice of cocharacter or
alternative indexing convention.

The conventions follow Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second
edition (2015), Example 2.1.1, printed pp.45–47
(source `conrad-gabber-prasad-2015-pseudo-reductive`, PDF pp.71–73), and Renard,
*Représentations des groupes réductifs p-adiques*, 2026 French version, V.3.8,
printed p.111
(source `renard-2026-representations-groupes-reductifs-padiques`, PDF p.117).
Decreasing weights yield block upper triangular parabolics, block diagonal
Levi subgroups, and identity diagonal blocks in their unipotent subgroups.
The cocharacter positivity, choice-free intersections, and all-test-scheme
comparisons are derived formulations. Renard works over a nonarchimedean
local field; the arbitrary-field scope of this theorem comes from the
published algebraic matrix construction.
