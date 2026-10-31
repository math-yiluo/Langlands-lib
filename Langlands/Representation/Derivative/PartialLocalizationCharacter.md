# Recursive partial-localization character restrictions

Author: Worker 321.

This internal matrix construction continues `PartialLocalizationData` in
namespace `Langlands.Derivative.PartialLocalization`. Its algebraic declarations
assume `F : Type uF` and `[CommRing F]`, and allow all natural `k,m`.
The unitary-character and topological declarations additionally assume the
supplied `[TopologicalSpace F]`. It constructs subgroup maps, exact character
restrictions and continuous group equivalences. It proves no representation
quotient, normalized action or derivative comparison.

## Concrete subgroup copies

Write `Q(k,m) = partialUpper k m F`, the actual group of matrices
`[[I_k,A],[0,u_m]]` in `GL_(k+m)`. The subgroup
`mirabolicPartialUpper k m F` is its size-`k+m+1` version, viewed inside
the actual `mirabolic (k+m) F`.

`fromMirabolic` forgets the redundant mirabolic certificate.
`mirabolicEquiv` bundles this as a group equivalence with `Q(k,m+1)`;
its inverse adds the last-row certificate obtained from upper unipotence.
Both maps preserve the underlying matrix literally.

`recursiveLevi` maps `Q(k,m)` into the mirabolic realization of `Q(k,m+1)`
by `g ↦ diag(g,1)`. Its membership certificate is the existing
`levi_mem_partialUpper`. `recursiveProjection` extracts the upper-left
`(k+m)` block using the existing actual mirabolic `projection`, with
`projection_mem_partialUpper` as its certificate.
`recursiveProjection_recursiveLevi` follows from `projection_levi` by subtype
extensionality. `recursiveRadical` includes the actual
`radical (k+m) F` into `Q(k,m+1)` using `radical_le_partialUpper`.

`partialLeviEquiv` identifies `Q(k,m)` with its actual image
`partialLeviSubgroup k m F`. Its inverse is the upper-left projection.
For its right inverse the proof unpacks image membership as `g = levi a`
and applies `projection_levi`. Its multiplication law is the multiplication
law of `levi`.

`partialLeviSubgroup_le_successor` places the recursive image of `Q(k,m+1)`
inside `successorSubgroup (k+m) F`. This follows because its smaller matrix
is mirabolic. `successorPartialSubgroup` is that same image with a second
subgroup certificate inside the successor range.
`successorPartialEquiv` gives the explicit group equivalence from `Q(k,m+1)`;
its inverse projects the underlying matrix. The proof of
`successorPartialSubgroup_map` unpacks the two membership certificates to
show that its image under the successor-range inclusion is exactly
`partialLeviSubgroup k (m+1) F`.

## Exact recursive character restrictions

The existing `character psi k m` is the adjacent-entry character on the actual
final `m` block. For every raw `psi : AddChar F ℂ`,
`finalSuperdiagonalSum_recursiveLevi` proves that appending the last identity
coordinate leaves the final-block adjacent-entry sum unchanged. The proof
splits the larger finite sum with `Fin.sum_univ_castSucc`. The last summand
vanishes by `levi_last`; the earlier summands are the original matrix entries
by `levi_first`, after reconciling `Fin.natAdd`, `castSucc` and `succ`.

`character_recursiveLevi` consequently proves the homomorphism equality

```text
(character psi k (m+1)).comp (fromMirabolic.comp recursiveLevi)
  = character psi k m.
```

For `m=0`, it uses the existing trivial rank-zero and rank-one characters.
For successor `m`, units extensionality reduces the assertion to the preceding
sum identity. No nontriviality, unitarity or continuity hypothesis is used in
this raw-character identity.

`character_recursiveRadical_one` proves

```text
(character psi k 1).comp (recursiveRadical (k := k) (m := 0)) = 1.
```

The final block has rank one, whose adjacent-entry character is trivial.
This is exactly the character restriction relevant to the final Psi-minus
step; it asserts no derivative theorem at `k=0` or at derivative order zero.

For `u : radical (k+m+1) F`,
`finalSuperdiagonalSum_recursiveRadical` proves that the final-block
adjacent-entry sum equals
`radicalCoordinates u (Fin.last (k+m))`. Splitting off the final summand,
every earlier column is an identity column by `u.property`; its row and
column indices differ, so every earlier summand is zero. The final entry
is definitionally the stated radical coordinate.

For every supplied `chi : UnitaryAdditiveCharacter F`, this yields
`character_recursiveRadical_succ`:

```text
(character chi.complex k (m+2)).comp
    (recursiveRadical (k := k) (m := m+1))
  = Langlands.Derivative.Mirabolic.theta chi (k+m).
```

Both sides evaluate the same positive final adjacent entry with the same
actual additive character. There is no inverse or complex conjugation.
The supplied topology, continuity and nontriviality remain in the bundled
character's type, although this equality uses its value formula only.

## Inherited topologies

`mirabolicContinuousEquiv` bundles `mirabolicEquiv` with continuity of
subgroup inclusions and restrictions; its inverse merely adds the redundant
certificate. `partialLeviContinuousEquiv` bundles `partialLeviEquiv` using
`continuous_levi` in the forward direction and `continuous_projection` in
the inverse direction. `successorPartialContinuousEquiv` does the same
through the second subgroup certificate. These are equivalences for the
actual inherited matrix/units topologies, and require no continuity of ring
operations or inversion on `F`.

## Source convention and derived provenance

The registered originals are Zelevinsky, *Induced representations of reductive
p-adic groups II* (1980), `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
Section 3.7 and Proposition 3.7(b), printed p.182 / one-based PDF19; and
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
Section 1.8(b) and Proposition 1.9(c), printed pp.444–445 / PDF5–6,
and Sections 3.5 and 4.3, printed pp.452,454 / PDF13,15. Their files are
respectively
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`
and
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
The parent task read the original passages and visually checked the
inverse-half normalization formulas; no applicable source-specific erratum
was found in the supplied notes or literature index.

The originals motivate successive localization by these subgroups and the
positive character convention. The declarations here are internal derived
coordinate identities, not additional theorems asserted verbatim by the
sources. Their generality over commutative rings follows from the implemented
matrix, subgroup and finite-sum proofs. No transitivity theorem or Haar-modulus
identity is assumed or proved in this module.

## Dependency and independence audit

The direct project imports are `Derivative.PartialLocalizationData` and
`Derivative.MirabolicCharacter`. The actual transitive project closure consists
of the 50 modules below. Its 49 preexisting Library pairs (98 files) agree
byte for byte with supplied Library
`7b0be54f6fdff0448d87d389ed9dc8b01c6f048f`.
The remaining pair is the unchanged concrete `PartialLocalizationData`
helper staged separately by this task, included in the candidate's repository
paths to preserve the complete dependency. Integration should publish that
focused unit before or with this one.

The actual proof inputs are the elementary mirabolic Levi/projection laws,
the partial-group membership and inclusion lemmas, the definitions of the
entrywise and mirabolic characters, subgroup-image membership, finite-sum
splitting, units/subtype extensionality and continuity under composition.
The imported representation and localization modules provide definitions and
lower smoothness constructions; no representation is an input to a new lemma
here. `Whittaker.PrerequisitesStatement` is an unproved proposition definition,
not an assumed existence or uniqueness theorem. `Dual.Definitions` supplies
algebraic dual maps, not a duality result. A mention of classification in
`LocalField.Topology.md` identifies other consumers, not an import.

The complete positive-segment/socle independence exclusions of parent task
revision 2 and the stronger shared-tower exclusions are preserved. There is
no segment or multisegment classification module in this closure and no
head/socle irreducibility, exhaustion, conversion or gluing input; no tempered
uniqueness, square-integrability classification, analytic segment criterion,
forward essential square-integrability, tensor comparison or Leibniz filtration
input. There is also no BZ77 3.8 pairing, plus-functor/adjunction result,
derivative duality, cuspidal derivative vanishing, Whittaker finiteness or
unproved derivative comparison. In particular
`Whittaker.TopDerivativeCoinvariantComparison`,
`Whittaker.UpperUnipotentCharacterFactorization` and
`Classification.SupercuspidalDerivatives` are not imported. Elementary
plus-subgroup maps happen to share `MirabolicProjection` with the projection
lemmas; none is used here as a representation theorem. The target statement
and every preexisting imported Lean/Markdown pair remain unchanged.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.RankMaps
Langlands.Group.GL.UpperUnipotent
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.Representation.Category.Basic
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Topology.Nonarchimedean.Subgroup
```
