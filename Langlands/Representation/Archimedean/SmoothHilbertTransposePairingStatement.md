# Smooth Hilbert inverse-transpose pairing targets

Worker 322. The three declarations in this module are unproved `Prop` definitions
in `Langlands.Archimedean`. They formulate the analytic pairing prerequisite for
the algebraic `ArchimedeanTransposePairingStatement`, using the vocabulary of
[SmoothHilbert](SmoothHilbert.md). No smooth duality or character-rigidity theorem
is proved here.

## Exact scope

`RealSmoothHilbertTransposePairingStatement.{uH}` quantifies over every positive
size `r + 1`, every `H : Type uH` with `NormedAddCommGroup H`,
`InnerProductSpace ℂ H`, and `CompleteSpace H`, and every homomorphism
`R : GL_(r+1)(ℝ) →* (H →L[ℂ] H)`.
`ComplexSmoothHilbertTransposePairingStatement.{uH}` has the identical telescope
for actual `GL_(r+1)(ℂ)`.
`ArchimedeanSmoothHilbertTransposePairingStatement.{uH}` is their conjunction.
The carrier universe is free.

The sole predicate premise is
`IsIrreducibleAdmissibleHilbertRepresentation F (r + 1) R`, which expands to
exactly the existing three conditions:

- joint continuity of `GL_(r+1)(F) × H → H`;
- topological irreducibility, including nontriviality of `H`;
- `IsAdmissible R (unitaryCompact F (r + 1))`, the compact intertwiner
  finite-dimensionality condition.

The complete complex Hilbert structure is explicit in the telescope. There is
no unitarity or genericity assumption, no supplied pairing, and no assumed
identification of an algebraic dual with an inverse-transpose twist. The scalar
exponential-derivative property used in the separate globalization conclusion
is not an additional pairing hypothesis.

The conclusion `HasNonzeroSmoothHilbertTransposePairing` asks for a complex
bilinear `B` on
`D = DerivativeSmoothVectors (matrixModel F (r + 1)) R`, with `B ≠ 0`, such that
it is continuous in each variable with the other fixed and

`B(R∞(g)y, R∞(GeneralLinear.inverseTranspose (r + 1) F g)x) = B(y,x)`

for every actual group element `g` and all `x,y : D`. The group action `R∞` is
transported from the published `smoothRepresentation` through `toSmooth`.
The second group element is precisely `transpose(g⁻¹)`, with ordinary transpose
over both fields. The form is complex bilinear, not a Hermitian inner product.

Continuity of `B` means continuity in the genuine word-derivative topology:
every finite real matrix word contributes its norm seminorm. This topology is
already defined on the dedicated carrier. It is distinct from the norm topology
of `H`, which controls the bounded operators and the representation premises.
The statement asks only for separate continuity; it does not build a new norm
or assume the topology agrees with the inherited subspace norm topology.

## Original theorem and derivation

Aizenbud–Gourevitch, *Generalized Harish-Chandra descent and applications to
Gelfand pairs*, arXiv v7 (2009), registered source
`aizenbud-gourevitch-2009-generalized-harish-chandra-descent-v7`, SHA256
`a789936fffe560b9295c666f420a3cf7c69a475192bace2e5c2c4c3d975d7dfd`:

- Definition 8.1.1, p.22, interprets archimedean admissible representations as
  admissible smooth Fréchet representations.
- Corollary 7.6.3, p.22, provides transpose invariance of conjugation-invariant
  distributions on `GL_n`.
- Theorem 8.2.1, p.23, identifies the smooth contragredient of an irreducible
  admissible representation with its twist by `θ(g) = σ(g⁻¹)`. Ordinary
  transpose is the anti-automorphism used here. The source proof invokes
  Wallach's character rigidity and Corollary 7.6.3. Remark 8.2.2 describes an
  alternative proof using Harish-Chandra regularity.

These targets are derived smooth Hilbert formulations. To apply that theorem,
the smooth carrier of the given Hilbert representation must first be identified
with its usual smooth admissible Fréchet realization. Relevant comparison
sources are Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
`getz-hahn-2024-automorphic-representations`, SHA256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
printed pp.118–120 (PDF pp.133–135), especially Theorem 4.4.9, the discussion
following Definition 4.4.11, Lemma 4.4.13, Theorem 4.4.14 and its globalization
discussion. The October 2026 errata,
`getz-hahn-2024-errata-2026-10`, SHA256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
p.1, correct the compact continuity and compact-finite globalization comparison.

The remaining formal comparison obligations include: identifying the genuine
word topology with the source smooth topology; obtaining a countable generating
seminorm family from a finite real Lie algebra basis and proving completeness;
proving that the transported action is smooth and jointly continuous for that
topology; transferring compact admissibility and irreducibility; and establishing
the moderate-growth/canonical-globalization comparison supplied by the cited
Getz–Hahn results. The standard smooth Hilbert construction places these objects
in the required category after those comparisons. None is a theorem made true
by the name `DerivativeSmoothVectors` or by the representation predicate.

Once the comparisons and Aizenbud–Gourevitch theorem are available, choose the
continuous equivariant isomorphism `T : D^θ → D^vee` and set

`B(y,x) = (T x)(y)`.

Evaluation on the continuous smooth contragredient is complex bilinear and
separately continuous, and the isomorphism and nonzero representation ensure
`B ≠ 0`. Equivariance gives

`(T(R∞(θ(g))x))(R∞(g)y) = (R^vee(g)(T x))(R∞(g)y) = (T x)(y)`,

which has exactly the requested variable order and inverse-transpose identity.
The source theorem applies to smooth continuous duality; replacing it with the
full algebraic dual would lose the required continuity claim. Nonarchimedean
locally constant character theory supplies no archimedean category comparison.
The present module imports no such theorem, global multiplicity-one theorem,
or Rankin–Selberg argument. Analytic proofs of the targets are follow-on work.
