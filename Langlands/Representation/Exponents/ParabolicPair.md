# Concrete block parabolic pairs and character restriction

Author: Worker 19.

This definition unit represents a parabolic pair of `GL_n` by a positive ordered
block shape and a conjugating matrix. The actual parabolic is the conjugate of
the standard upper block parabolic. The split component is the image of the
conjugated block-scalar homomorphism. These are constructed subgroups; there are
no representation-theoretic hypotheses or conclusions among the data.

The ordering `fine.Refines coarse` is inclusion of the fine parabolic in the
coarse parabolic and reverse inclusion of their split components.
`StrictlyRefines` means this ordering holds and the reverse does not. The proved
characterization says precisely that at least one of the two actual subgroups
differs. Distinct presentations of the same pair therefore do not count as
proper refinements. Reflexivity, transitivity and strict irreflexivity are proved.

Scalar coordinates are injective: after cancelling conjugation, evaluation at
one diagonal coordinate in each positive-size block recovers every scalar.
Given actual split-component inclusion, `scalarInclusion` chooses the unique fine
coordinates of each coarse scalar. Its defining ambient-matrix equation, group
homomorphism laws and injectivity are proved. `CharacterExtends` is equality of
the finer character restricted along this constructed homomorphism with the
coarser character. The proved equivalent formula says equal actual scalar
matrices have equal character values. This is ordinary character restriction,
not an assumed map or an arbitrary relation between characters.

The original source is A. J. Silberger, *Introduction to harmonic analysis on
reductive p-adic groups* (1979), registered as
`silberger-1979-harmonic-analysis`, retained SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Section 0.3, printed pp.5–6 (PDF pp.11–12), defines parabolic pairs, their order,
and conjugacy to standard pairs. The ordering and conjugacy sentences on p.6
were checked in the original page image. Section 4.5, printed p.189 (PDF p.195),
uses proper smaller pairs and character restriction in the definition of a
weakly critical exponent. That formula was checked in its page image as well.

This is a derived type-A coordinate implementation. Over a p-adic field,
conjugated standard block parabolics and their block-scalar split components
present the parabolic pairs used in the source. Quantifying over all shapes
and all conjugating matrices includes the nonstandard pairs: no reduction to
standard refinements is built into the ordering. The source's algebraic-group
conjugacy theorem is not proved here, nor is this an abstract algebraic-group
formalization. The same subgroup and coordinate constructions work over any
commutative ring as an internal extension. Field/ring universe is arbitrary;
no representation carrier occurs in this unit.

No dual-exponent finiteness, nilpotence comparison, weak-critical support theorem,
Jacquet transitivity, or Haar-modulus assertion is made here. This construction
supplies the concrete refinement and restriction inputs for their subsequent
statements.
