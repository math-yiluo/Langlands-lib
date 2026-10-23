# Coupled equal-rank measure conditions

This module assembles the measure prescriptions of Shahidi, *Fourier transforms
of intertwining operators and Plancherel measures for GL(n)* (1984), printed
pages 75–77, items 1–7. It defines a predicate on actual supplied measures and
proves consequences of its equations. It does not assert that a compatible
tuple exists, extend the prescription to unequal ranks, or state the local
coefficient comparison.

## Source and provenance

Registered source: `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The original scan was read at printed pages 73–77; the seven measure items on
75–77 were reread when assembling this module. The pairing inputs are Lemma 1.1
on page 73 and Proposition 1.2 on page 74. The source works in an intermediate
unitary/supercuspidal setting, with a non-archimedean local field, its normalized
absolute value, and an additive character of conductor the ring of integers.
Those analytic hypotheses support existence statements, which are outside this
unit. The predicate itself is defined more generally for supplied data.

The assembly is **derived** content. It reuses the published definitions in
`PairingMeasure`, `KirillovMeasure`, `UnipotentProduct`, `QuotientTransport`,
`CompactMeasures`, `IwasawaMeasures`, `CoordinateMeasures` and `RadicalMeasures`.
The added condition is that these definitions concern the *same* specified
choices, together with genuine Haar and quotient-composition properties. No
result on the existence of these choices or the comparison theorem is included
as a field of a representation or measure structure.

The source's rank is `n + 1` in this module; its smaller group has rank `n`.
Thus `n = 0` is allowed in the definitions, including the trivial smaller group.
No separate claim of analytic existence in that boundary case is made.

## Actual data and Haar properties

`EqualRankMeasureData O n` contains sixteen pieces of measure data:

- `dn₁`, `dn₂`, `dn`: measures on the smaller upper unipotents, their last-column
  coordinates `Fin n → F`, and the full upper unipotents;
- `quotient`, `primedQuotient`: measures on the actual left quotient
  `N_n \ GL_n`, interpreted in the upper-left and lower-right embeddings;
- `daStar`, `dzStar`, `dk`, `dgStar`: measures on `GL_n`, `Fˣ`, the integral
  subgroup of `GL_(n+1)`, and `GL_(n+1)`;
- `dx`, `da`: families of regular additive Haar measures on the field, indexed
  by the row coordinates and matrix entries respectively;
- `intertwining`, `jacquet`, `swappedJacquet`: measures on the actual square
  matrix coordinate spaces;
- `upper`, `lower`: measures on the ambient `GL_(2n+2)` supplied as the
  pushforwards along the actual radical embeddings.

The structure imposes no equations among these choices. It does not select a
measure. Each scalar factor in `dx` and `da` is the published
`AdditiveHaarMeasure`, which includes its own Haar and regularity proofs.

`IsRegularTwoSidedHaar μ` requires left Haar invariance, finiteness on compact
sets, positivity on nonempty open sets, regularity, and right invariance.
`IsEqualRankHaarData` imposes this condition on all six group measures
`dn₁`, `dn`, `daStar`, `dzStar`, `dk`, `dgStar`. It also requires additive Haar
and regularity for `dn₂`, `jacquet`, and the whole matrix product measure from
`da`. The radical equations below transfer the corresponding properties to the
other coordinate measures. The ambient measures `upper` and `lower` are not
required to be Haar measures on the entire general linear group.

## The coupled equations

`IsPairingMeasureCompatible ψ π b ℓ d` expresses item 1:

1. The actual Whittaker functional `ℓ` on `π : GL_(n+1) → End(V)` is nonzero.
2. The full unipotent measure `dn` is the pushforward of `dn₁.prod dn₂` along
   the ordered map `(u,x) ↦ diag(u,1) u(x)`.
3. The Lemma 1.1 integral against `dn` is integrable for every pair of vectors
   and equals `ℓ(v) conjugate(ℓ(w))`, using the supplied positive invariant form
   `b` and standard unipotent character.
4. The Kirillov pairing against `primedQuotient` is integrable for every pair
   and equals `b.inner w v`. This is the same `b` and `ℓ` as in item 3; the
   reversed arguments match the source's linear-first pairing convention.
5. `quotient` is the pushforward of `primedQuotient` under the proved quotient
   involution induced by `a ↦ w_n (a⁻¹)ᵀ w_n⁻¹`.
6. `IsSmallerQuotientCompatible` imposes the Library's integrable Weil equation
   composing `dn₁` and `quotient` into `daStar`. The quotient is nonzero,
   regular, and invariant under the smaller group's right translations.

The last predicate existentially binds a proof of right invariance of `dn₁`
so that the subgroup average is well-defined. Its body is the published
`QuotientIntegration.IsCompatible`, including convergence of quotient averages
of compactly supported continuous complex functions and their integral formula.
It does not posit the existence of a new quotient or group measure.

`IsEqualRankMeasureNormalized ψ π b ℓ abv d` conjoins the Haar conditions and
item 1 with the remaining published equations:

- Items 2 and 3 are `IsCompactVolumeCompatible`: the product mass on
  `GL_n(O) × O^n × Oˣ` is one, and at some positive level the specified compact
  block set has the product ideal-box mass of row coordinates 2 through `n+1`.
- Item 4 is `IsIwasawaMeasureCompatible`: the weighted product
  `|det a|⁻¹ dn₂ d*a d*z dk` pushes forward under actual Iwasawa multiplication
  to `dgStar`, and the total integral-group masses agree.
- Items 2, 3 and 5 are coupled by `IsCoordinateMeasureCompatible`: the first
  row factor is the measure `|z| d*z` pushed into the field; the entire row
  product is self-dual for the inverse character using the Library's plus-sign
  Fourier convention; the matrix product is `|det a|^(n+1) dgStar` pushed into
  matrices; and each first-column scalar factor equals its designated row
  factor. These are product factors, not projection marginals of an infinite
  measure. No self-duality of the full matrix measure is imposed.
- Items 6 and 7 are `IsEqualRankRadicalMeasureCompatible`: `upper` is the
  pushforward both of that matrix product and of the intertwining measure,
  while `lower` is the pushforward of both Jacquet measures. The latter pair
  agrees with each other; it is not forced to equal the intertwining measure.
  This records the common lower-radical choice after the source's prescribed
  translations. The identification with functionals on actual induced spaces
  remains the responsibility of the later specialization.

## Implemented consequences

`IsPairingMeasureCompatible.primed_quotient_properties` proves that the primed
quotient measure is nonzero, regular, and right invariant. It extracts the Weil
compatibility of the unprimed quotient, reverses the reflection equation using
the proved involution, and applies the published transport results. No separate
quotient-invariance hypothesis is introduced for the primed measure.

`IsEqualRankMeasureNormalized.pairings` extracts the two equations using the
same Hermitian form and functional. `corner` derives the weighted-central
measure identity for the top-left matrix factor. `radical_coordinates` uses
injectivity of the radical pushforwards to prove that the intertwining measure
is exactly the matrix product and the two Jacquet coordinate measures agree.
These are consequences of normalization equations, not analytic existence
proofs.

## Scope and retained source issue

The field and representation universes are independent. No topology or norm is
imposed on the representation space; the integrals in the pairings are scalar.
The definition uses a topological field with continuous ring operations, supplied
measurable structures, a subring `O` with `IsLocalRing O`, and an absolute value.
It does not certify that `O` is the valuation ring, that the field is local, that
the absolute value is normalized, or that the character has conductor `O`.
Applications to the source must supply those hypotheses and the Borel
structures. No existence, independence of auxiliary choices, or independence of
the positive compact level is proved here. In particular this module must not
be used to impose the intermediate unitary/supercuspidal assumptions on the
all-rank Theorem 5.1 statement.

The primed quotient retains the documented interpretation from `KirillovMeasure`
and `QuotientTransport`: use the **upper** unipotents in the lower-right block.
The literal printed longest-Weyl conjugate of the upper-left upper subgroup is
lower unipotent and does not give the descent used by the Whittaker pairing.
The choice here is an explicit inference from the surrounding Whittaker
construction, not a claimed published erratum. The actual upper-quotient
descent and inverse-transpose transport are proved in the imported modules.
