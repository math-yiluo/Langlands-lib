# Equal-rank trilinear-form uniqueness: proof

Worker 353 authored this final composition of published Library proofs.
The theorem `Langlands.RankinSelberg.equalRankTrilinearUniqueness` has type
`EqualRankTrilinearUniquenessStatement.{uF,uV,uW} F T n`, with independent
field and carrier universes, for every prime `p`, `F : PadicField.{uF} p`,
supplied `T : F.TopologicalData` and `n : ℕ`. Its target is the unchanged
[equal-rank uniqueness statement](EqualRankTrilinearUniquenessStatement.md).
It has no additional premises.

For the actual coefficient models of two representations of Whittaker type,
and arbitrary chosen functionals, the conclusion supplies one finite set of
values of `q^(-s)` before choosing `s` or the trilinear forms. Outside that
set, every twisted invariant form is a scalar multiple of any nonzero one.
The conclusion includes reducible representations, zero functionals and
rank `n+1 = 1`.

## Implemented proof

The proof applies the published
`equalRankTrilinearUniqueness_of_mirabolic_prerequisites` from
[EqualRankTrilinearMirabolicPrerequisites](EqualRankTrilinearMirabolicPrerequisites.md).
It supplies all seven conjuncts of that adapter's premise:

| Input | Published proof supplied |
| --- | --- |
| Finite length of mirabolic restriction in each carrier universe | `Langlands.Whittaker.mirabolicFiniteLength.{uF,uV}` and `.{uF,uW}` |
| Irreducible mirabolic functional multiplicity in each carrier universe | `Langlands.Whittaker.mirabolicFunctionalMultiplicity.{uF,uV} F T n` and `.{uF,uW} F T n` |
| Finite-exception rigidity of irreducible twisted pairings | `Langlands.Whittaker.mirabolicTwistedPairingRigidity.{uF,uV,uW} F T n` |
| One-dimensional compact-model twisted pairing | `Langlands.Whittaker.mirabolicCompactTwistedPairing.{uF} F T n` |
| Frobenius reciprocity for row Schwartz functions vanishing at zero | `Langlands.RankinSelberg.equalRankFrobenius.{uF,uV,uW} F T n` |

The adapter already supplies
`Langlands.glAdmissibleFiniteLength` separately in both carrier universes.
Its underlying
[prerequisite assembly](EqualRankTrilinearPrerequisites.md) compares the
supplied field topology with the canonical topology before applying GL
finite length. It changes the inverse Whittaker character on the second
functional space to the positive character, without changing that
representation's carrier or action.

That assembly uses the functional and pairing results to bound the actual
covariant bilinear spaces of irreducible mirabolic constituents. The
published finite-filtration bound then gives a finite exceptional set for
the full restrictions. The spectral shift and Frobenius equivalence give
the corresponding bound on trilinear forms restricted to Schwartz functions
vanishing at zero, with determinant weight `1-s` on the bilinear side.
The published `Langlands.RankinSelberg.centralBilinearVanishing` eliminates
the remaining pairing supported at evaluation at zero outside another
finite set. The source assembly combines these sets before the exponent
and forms; surjectivity of the coefficient-model maps descends uniqueness
to the actual coefficient images, including zero images.

The new module only supplies the published proofs to these existing
adapters. It imports every dependency by Lean name and introduces no new
representation-theoretic hypothesis or modification of an imported pair.

## Correspondence with the literature

The target is the Proposition in Jacquet–Piatetski-Shapiro–Shalika,
*Rankin-Selberg Convolutions* (1983), §2.10, printed p.396; the proof on
pp.397–398 restricts to functions vanishing at zero, uses Frobenius
reciprocity and finite mirabolic composition series, and removes the
residual pairing at zero. The implemented composition follows that
structure through the published adapters. Its mirabolic input proofs
correspond to JPSS §1.4 and §1.5, printed pp.380–384; Frobenius has the
normalization of (2.10.5)–(2.10.6).

Bernstein–Zelevinsky, *Representations of the group GL(n,F) where F is a
non-archimedean local field* (1976), Corollary 5.22, printed p.51, supplies
the literature's finite-length restriction step. Here the imported
`mirabolicFiniteLength` proves precisely the required implication for the
actual mirabolic subgroup. Its proof and the other imported proofs are
explained in their own paired Markdown; this final module composes them.
The retained registered originals are `jpss-1983-rankin-selberg` and
`bernstein-zelevinsky-1976-representations-gln`. The statement's
paired Markdown records the exact JPSS target correspondence and the
restriction to p-adic fields.
