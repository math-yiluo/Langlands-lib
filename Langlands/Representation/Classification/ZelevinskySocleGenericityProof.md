# Genericity of actual Zelevinsky socles

Author: Worker 1732.

The theorem `Langlands.Classification.zelevinskySocleGenericity` proves the
unchanged published proposition `Langlands.Classification.ZelevinskySocleGenericity`.
For every positive rank, compatible p-adic field topology, allowed nontrivial
unitary additive character, multisegment and actual representation satisfying
the Zelevinsky socle relation, genericity is equivalent to every segment having
length one. Field and representation universes remain independent.

The private functional comparison identifies nonzero standard Whittaker
functionals with nonzero top derivatives using actual character localization
and its linear dual. The comparison reproduces Worker 1732's private helper
from GenericSegmentProductExhaustionProof; it uses only published dependencies.

For an irreducible subrepresentation of the supplied ordered segment-socle
product, the highest possible derivative order of the product is the sum of
the base ranks. If any segment is longer than one, this sum is strictly smaller
than the total degree. The top derivative of the product is then zero, and
exactness gives an injection of the top derivative of the subrepresentation
into it. A nonzero Whittaker functional would contradict that injection.

If every segment is a singleton, the sum of base ranks equals the total degree
and the highest-derivative theorem makes the top derivative of the product
one-dimensional. Its mirabolic restriction therefore has level equal to the
full degree. Precedence ordering and integral-twist freeness imply the endpoint
separation needed by the published segment-product homogeneity theorem. The
injected irreducible representation is nonzero, so homogeneity transfers this
full level to its restriction. The restriction bridge gives its nonzero top
derivative and hence its nonzero Whittaker functional. Irreducibility is
supplied by the subrepresentation relation, and the cuspidal-embedding theorem
supplies admissibility. This proves all components of genericity.

Finally, the multiset socle relation supplies the ordered datum. Membership in
its occurrence multiset is exactly membership among its indexed segments, so
the indexed criterion proves the published multiset criterion, retaining
repetitions and allowing linked singleton segments.

The source assertion is Zelevinsky 1980, section 9.10, printed p.201, following
Theorem 8.1, p.195. The implemented proof uses the published segment derivative
and product homogeneity results (Theorems 3.5 and 6.2), rather than claiming to
reproduce the original proof verbatim. Registered source:
`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The actual localization comparison, derivative exactness and admissibility
correspond to Bernstein--Zelevinsky 1977, sections 1.8--1.9, Theorem 2.5 and
sections 3--4; registered source `bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
All lower results are imported by Lean name. The only new assertions are proved
internal consequences of those results and elementary positive-rank arithmetic.
This criterion does not prove rectangular Speh comparison or unitary exhaustion.
