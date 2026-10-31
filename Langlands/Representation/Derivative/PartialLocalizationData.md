# Concrete matrix data for partial character localization

Author: Worker 321.

This module supplies internal matrix data for the positive two-block comparison
of Zelevinsky (1980), Proposition 3.7(b). It constructs the actual subgroup
`[[I_k,A],[0,u_m]]`, proves both of its radical/Levi generation identities,
and identifies its character on the parabolic radical and final upper block.
It proves no quotient, derivative, or natural-functor comparison.

All algebraic constructions use an arbitrary commutative ring `F : Type uF`.
The subgroup, projection, character and mirabolic recursion support every natural
rank; only the positive two-block section assumes `0 < k` and `0 < m`, exactly
as required by the published `Shahidi.twoBlocks` shape. These all-rank matrix
constructions assert no rank-zero derivative comparison. In particular they do
not change representations of `GL_0` or identify their carriers with a point.

## Actual subgroup and final-block maps

`fixedColumns k m F` fixes the first `k` standard coordinate vectors. Its
membership equation is

```
g i (j.castAdd m) = if i = j.castAdd m then 1 else 0.
```

The column of a matrix product against a fixed identity column equals the
corresponding column of the first factor. This proves multiplication closure;
applying it to `g⁻¹ * g` proves inverse closure. `partialUpper k m F` intersects
this subgroup with the Library's full upper-unipotent subgroup. Thus its first
diagonal block is identity, its lower-left block is zero, and its final block
is upper unipotent (`firstBlock`, `lowerLeft`, `partialUpper_le_upper`). The
upper-right block is unrestricted.

`upperFinalProjection` extracts the final diagonal block from a full upper
unipotent matrix. Its inverse is the same block of the actual inverse matrix.
Splitting the multiplication sum at `k` proves the product formula: the terms
through the first block vanish by upper triangularity. Applying this formula
to both inverse identities supplies the required unit equations. Restriction
to the partial group is `finalProjection`; `finalProjection_apply` exposes its
literal entries.

`blockSum_mem_partialUpper` proves that `diag(I_k,u)` belongs to the group,
by the four block-entry cases. `finalLevi` is this actual inclusion, with
`finalLevi_val` giving its ambient matrix. `finalProjection_finalLevi` proves
that projection after inclusion is the identity.

For a raw additive character `ψ : AddChar F ℂ`, `character ψ k m` is precisely
`Whittaker.entrywiseCharacter ψ m` composed with `finalProjection`. At final
rank `m+1`, `character_succ` is `ψ` applied to the sum of the final block's
adjacent entries. `character_finalLevi` is equality of units-valued characters
with the Library's entrywise character on the final block. No new additive
character, inverse character, or topology is substituted.

## Successive mirabolic decomposition

`mirabolicPartialUpper k m F` is the comap of `partialUpper k (m+1) F` along
the actual inclusion of `mirabolic (k+m) F` in `GL_(k+m+1)`. The lemma
`partialUpper_le_mirabolic` proves that this comap represents the same ambient
matrix subgroup. `partialLeviSubgroup k m F` is the image of the smaller
`partialUpper k m F` under the published actual `levi`, namely `diag(g,1)`.

`projection_mem_partialUpper` reads the leading block and fixed-column equations.
`levi_mem_partialUpper` checks those equations after adjoining the last identity
row and column. The actual final-column radical is contained in the partial
group because it fixes all leading columns. These inclusions and the published
factorization `eq_radicalElement_mul_levi` prove

```
mirabolicPartialUpper k m F =
  radical (k+m) F ⊔ partialLeviSubgroup k m F.
```

This is `partialUpper_eq_radical_sup`, an equality of actual subgroups inside
the mirabolic group, not an assumed decomposition. The supremum is subgroup
generation; the proof supplies a radical factor followed by a Levi factor.
This module does not yet identify the character with each recursive Phi/Psi
character; those restrictions are separate from this generation identity.

## Positive parabolic decomposition and character

For `hk : 0 < k` and `hm : 0 < m`, `partialUpper_le_parabolic` uses the
published two-block lower-left criterion. Conversely the actual parabolic
radical has both diagonal blocks identity. Its lower-left block is zero by
parabolic membership. The four index cases therefore prove
`parabolicRadical_le_partialUpper`.

`finalLeviRange k m F` is the range of the actual ambient homomorphism
`u ↦ diag(I_k,u)`. `finalLeviRange_le_partialUpper` records its inclusion.
`leviProjection_first_eq_one` and `leviProjection_second_eq_final` identify the
actual block projections of an element of the partial group: they are `1`
and `finalProjection g`, respectively. The Library's two-block embedding is
exactly `blockSum`, so its embedded Levi component is `finalLevi` of that
final projection. Substituting this into the already constructed parabolic
decomposition proves

```
partialUpper k m F =
  (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F ⊔
    finalLeviRange k m F.
```

This is `partialUpper_eq_parabolicRadical_sup`. It uses the actual
`BlockShape.unipotentPart` and diagonal projections, with no abstract
subgroup-comparison premise. `finalProjection_radical` proves that the final
block of every element of this parabolic radical is identity.
`character_radical` then proves that its character is exactly `1`, by the
homomorphism identity law. Together with `character_finalLevi`, this is the
required trivial-radical/final-adjacent-entry restriction in the positive
parabolic decomposition.

## Topology

`continuous_finalProjection` and `continuous_finalLevi` hold for any supplied
`TopologicalSpace F`; no continuity of field or ring operations is needed.
The former checks continuity of both the value and inverse matrix blocks in
the units topology. The latter uses the published continuous block sum.
Subgroup topologies are the actual subspace topologies throughout.

## Provenance and scope

The original comparison motivation is A. V. Zelevinsky, *Induced
representations of reductive p-adic groups II* (1980), Section 3.7 and
Proposition 3.7(b), printed p.182, one-based PDF page 19. Registered source
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
retained at
`/home/taskhub/central-library/Zelevinsky--Induced representations of reductive p-adic groups II, irreducible representations of GL(n)--1980.pdf`.
That passage defines the partial derivative using the upper group of the last
block and the adjacent-entry character, and compares it with the Jacquet
functor. The present subgroup packages the combined localizing groups.

The transitivity motivation is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), Section 1.8(b)
and Proposition 1.9(c), printed pp.444–445, one-based PDF pages 5–6; Sections
3.5 and 4.3, printed pp.452,454, PDF pages 13,15. Registered source
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
retained at
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
The localization convention there is inverse half modulus. The present
module constructs no normalized action or modulus identity and does not
invoke the transitivity conclusion. The source passages and rendered
normalization formulas were read in the parent proof task; no applicable
source-specific erratum was found in the supplied notes or literature index.

These matrix lemmas are internal derived constructions, not separate
assertions copied verbatim from the originals. Their extension to arbitrary
commutative rings follows from the explicit matrix and subgroup proofs just
described. They introduce no hypotheses on representations, carrier universes,
finiteness, admissibility, irreducibility or genericity. The target statement,
its imported pairs and all reused Library pairs remain unchanged.

The direct project imports are `Group.GL.MirabolicProjection`,
`Representation.Shahidi.TwoBlocks`, and `Representation.Whittaker.EntrywiseCharacter`.
The complete transitive project import closure has 32 modules, listed below.
All 64 imported Lean/Markdown files match the supplied Library
`7b0be54f6fdff0448d87d389ed9dc8b01c6f048f` byte for byte. It consists of
matrix group constructions, field topology and normalization, elementary
characters, smooth-representation definitions, and elementary Whittaker
character/functional constructions. `Dual.Definitions` supplies algebraic dual
maps; it supplies no duality theorem. `PrerequisitesStatement` is an unproved
proposition definition; no uniqueness or existence clause is assumed here.
The coefficient-model and character-change constructions are not used in the
proofs. A documentation mention of `Classification.Supercuspidal` in
`LocalField.Topology.md` describes other consumers, not an import or proof input.

The closure contains no positive-segment or socle classification route, no
`SegmentHeadProductIrreducibility`, `GenericSegmentProductUniqueness`,
`SquareIntegrableLanglandsClassification`, unlinked/linked socle product result,
head or socle exhaustion, ordered conversion, tempered uniqueness, analytic
segment classification, forward essential square-integrability, BZ77 3.8
pairing, cuspidal derivative vanishing, Whittaker-finiteness proof, tensor
comparison, derivative filtration, plus/adjunction or derivative duality
result. In particular it does not import
`Whittaker.TopDerivativeCoinvariantComparison` or
`Classification.SupercuspidalDerivatives`. The complete exclusions of parent
task revision 2 and the stronger shared tower exclusions are preserved.
MirabolicProjection also contains elementary maps for a plus-induction
subgroup; the proofs here use only its projection and actual matrix
factorization, not any plus representation or adjunction theorem.

```text
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.Blocks
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
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
Langlands.Representation.Dual.Definitions
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
```
