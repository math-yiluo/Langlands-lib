# The simultaneous normal compact-open basis on supplied valid KP data

`Langlands.BruhatTits.SpecialCompact.AvailableSimultaneousStandardBasisStatement`
is a proposition target for Renard V.5.2(i)–(iv) at the geometric special
maximal compact subgroup of the same corrected KP datum. It also requests the
compact properties and geometric standard-Levi inheritance of V.5.1 at that
subgroup. The declaration states these conclusions; it supplies no proof.

## Hypotheses and the fixed geometric compact

The statement quantifies over every universe-`u` nonarchimedean local field `F`,
with its valuation relation and topology, and every actual connected reductive
`F`-group `G`. There is no restriction to split, quasi-split or tamely ramified
groups, to characteristic zero, or to large residue characteristic. Affineness
of `G` is obtained from its connected reductivity.

Next it takes an assignment `𝔅 : KPBuildingAssignment.{u}` and the explicit
proposition `𝔅.IsValid`. This is the full corrected KP Definition 4.1.26 for
every connected reductive group over every nonarchimedean local field in that
universe. Its ten clauses are Axioms 4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8,
4.1.9, 4.1.16, 4.1.17, 4.1.20 and 4.1.22, including the cross-group
comparisons and the actual integral-model and quotient families. No existence
of an assignment satisfying this predicate is asserted here.

Write `D := (𝔅.datum F G hG).base`. Its torus `D.S`, maximal split torus
inclusion `D.i`, apartment `D.apartment` and apartment map are fixed throughout.
The statement takes every generic cocharacter `ν` of `D.S`; this fixes the
positive system and the actual minimal parabolic. It then takes every
`x : D.Apartment` satisfying `D.apartment.IsSpecialApartmentVertex x`.
Specialness and vertexhood are geometric conditions, without any compactness
or simultaneous-basis property built into them.

All three conclusions use the literal subgroup

```text
K0 = D.apartment.specialCompactSubgroup x
   = G(F)^1 ∩ Stab_G(F)(D.apartmentMap x).
```

Here `G(F)^1` is `rationalCommonNormKernel G`. Thus `K0` is the shared geometric
compact stabilizer. The declaration introduces no second compact witness.
It does not identify this subgroup with the parahoric or with the full fixer.

The first conjunct is `SpecialCompactProperties F D.i ν K0`: algebraic
boundedness, openness and maximality among bounded subgroups; compactness,
openness and maximality among compact subgroups; actual relative Weyl
representatives; and the literal standard-parabolic intersection products.
The second is `SpecialLeviInheritance F D.isMaximalSplitTorus ν D.apartment x`.
The third is `SimultaneousStandardBasisAt D.i ν K0`.

## One basis and the Renard S20–S23 correspondence

The third conjunct reuses the published actual-group property in
`StandardBasisProperty`. Its quantifier order is

```text
∃ B, CompactOpenNormalBasis K0 B ∧
  ∀ J ⊆ simpleRelativeRoots D.i ν,
    InheritedCompactOpenNormalBasis K0 (standardLeviPoints D.i ν J) B ∧
    ∃ A q, IsCompatibleStandardSplitComponent D.i ν J A q ∧
      ∀ K ∈ B, StandardParabolicBasisMember D.i ν J q K.
```

There is one cofinal identity-neighborhood basis `B` before every standard
parabolic. For each `J`, its actual compatible central split component `A`
and inclusion through `q : A → D.S` are chosen before every `K ∈ B`.

| Source item | Reused conclusion |
| --- | --- |
| S20, V.5.2(i) | `CompactOpenNormalBasis K0 B` requires every `K ∈ B` to be compact and open, contained and normal in this `K0`, and requires `B` to be a basis of the full identity-neighborhood filter. |
| S21, V.5.2(ii) | `HasIwahoriIntersectionDecomposition` requires bijectivity of actual ordered multiplication `(K ∩ Nbar_J) × (K ∩ M_J) × (K ∩ N_J) → K`. `LeviIntersectionNormalization` and `WeakChamberContraction` give the normalization and both contraction directions. |
| S22, V.5.2(iii) | `StrictChamberExhaustion` gives both expanding unions for every strict element. `UniformCompactContainment` chooses a positive threshold for every compact subset of each radical, before all chamber elements satisfying that threshold. |
| S23, V.5.2(iv) | `StrictChamberNeighborhoodBases` gives both power neighborhood bases. `UniformCompactOpenCofinality` gives the stronger uniform inclusion for every compact open subgroup of each radical. |

These factors are the literal intersections with the published
`standardLeviPoints`, `standardUnipotentPoints` and
`standardOppositeUnipotentPoints`. The last is the actual standard radical
for the reversed positive system and index. The product map uses ambient
group multiplication; its bijectivity includes uniqueness of the factors.
The smaller subgroups in `B` are the basis requested by V.5.2, rather than a
choice of a chamber Iwahori.

The component is specified by `IsCompatibleStandardSplitComponent`: a split
subtorus of `D.S`, a closed representative of the actual standard Levi on
every test scheme, connected reductivity of that representative, and its
actual central split-component property. The subgroup `C_A` is the image in
`G(F)` of `CocharacterUniformizer.CA F A`. It consists of cocharacters
evaluated at the same chosen field uniformizer. The relevant characters are
the restrictions along `q` of the simple roots outside `J`. Their normalized
rational-character norms define `C_A^+` by `≤ 1`, `C_A^{++}` by `< 1`, and
`C_A^+(ε)` by `< ε`. The last has no additional `≤ 1` condition.

For each `K ∈ B`, `C_A` normalizes `K_M`. A weak positive element `m`
contracts `K_N` by `m K_N m⁻¹ ⊆ K_N`, and its inverse contracts the opposite
intersection by `m⁻¹ K_Nbar m ⊆ K_Nbar`. Every strict element satisfies

```text
N_J(F)    = ⋃ n : ℕ, m^(-n) K_N m^n,
Nbar_J(F) = ⋃ n : ℕ, m^n K_Nbar m^(-n).
```

For each compact subset `Γ` of `N_J(F)`, a positive `ε` works for every
`m ∈ C_A^+(ε)` in `Γ ⊆ m⁻¹ K_N m`; for the opposite radical the inclusion is
`Γ ⊆ m K_Nbar m⁻¹`. The contracting power families are `m^i K_N m^(-i)`
and `m^(-i) K_Nbar m^i`, respectively. For every compact open subgroup `Γ`
of either radical, the final uniform clause chooses `ε > 0` before every
`m ∈ C_A^+(ε)`, requiring `m K_N m⁻¹ ⊆ Γ` or `m⁻¹ K_Nbar m ⊆ Γ`,
respectively.

All ambient topological clauses use the named canonical
`rationalPointTopology F G.X`. The radicals and standard Levi point subgroup
carry its inherited subgroup topologies.

## Standard-Levi compatibility at the same vertex

`InheritedCompactOpenNormalBasis` uses exactly `intersectionFamily M_J B`,
whose members are `K.comap M_J.subtype`, relative to
`K0.comap M_J.subtype`. It does not choose an independent Levi basis.

The separate geometric conjunct `SpecialLeviInheritance` requests, for every
standard `J`, apartment data `DM` for the actual closed
`Standard.leviScheme D.i ν J` with the same torus
`Standard.leviTorusHom D.i ν J`. It requests a special vertex `xM` obtained
by restricting the ambient root valuations, its compact properties, and
the exact equality

```text
DM.specialCompactSubgroup xM
  = D.apartment.specialCompactLeviSubgroup ν J x.
```

The right side is the preimage of this ambient `K0` under the actual Levi
inclusion. Its image is `K0 ∩ M_J(F)`. Thus the inherited basis and the
geometric Levi compact refer to the same ambient subgroup and standard
Levi, expressed respectively as a literal point subgroup and a represented
group scheme.

The premise `𝔅.IsValid` supplies full availability for each literal standard
Levi once its connected reductivity has been established. Proving that
connected reductivity and constructing the geometric restriction remain
obligations; they are not extra input certificates hiding the conclusion.
The assignment may independently choose a torus in its datum for that Levi.
The statement imposes no equality between that arbitrary choice and the
ambient `D.S`. The conclusion instead constructs the requisite apartment
data for the prescribed inclusion of `D.S` into the Levi.

Transport between the inherited subgroup topology and the canonical
rational-point topology of the represented Levi also requires proof.
An algebraic point-group equivalence alone does not supply this comparison.

## Sources, provenance and retained obligations

The target is derived packaging of published predicates, with the full
corrected KP validity premise and a single fixed `D`, `ν`, `x` and `K0`.
It follows the same-data convention of the supplied-data Iwasawa target.
It leaves the general
`SimultaneousStandardBasisExistenceStatement` and the stronger
`JointSpecialCompactBasisExistenceStatement` unchanged. Neither unrelated
existential compact witnesses nor those statement definitions prove the
new universal conditional target.

The original source correspondence is:

- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026,
  V.5.1–V.5.2, printed pp.122–123/PDF pp.128–129: the fixed `P∅`, `A∅`, `K0`
  and the simultaneous basis, normalization, contraction, exhaustion and
  cofinality clauses. V.2.5, V.3.14 and V.3.21–V.3.23 give the common
  uniformizer section and character chambers. Source ID
  `renard-2026-representations-groupes-reductifs-padiques`, SHA256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
  Definition 1.3.39, printed p.29/PDF p.60; Definition 4.1.26;
  Theorem 4.2.15(1), printed pp.173–174/PDF pp.204–205; and §6.7,
  printed pp.233–234/PDF pp.264–265: specialness, availability, the
  geometric bounded open maximal subgroup and restriction to Levis.
  Source ID `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
- Kaletha–Prasad, *Corrections and additions*, 1 November 2024,
  PDF pp.27–29: the corrected ten-axiom availability definition;
  PDF p.33: the Chapter 7 AS5 prerequisite and positive-depth boundary
  for the additional product assertion. Source ID
  `kaletha-prasad-2024-corrections`, SHA256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

The remaining construction and proof obligations include:

1. Construct a valid corrected assignment, its maximal split torus
   comparisons and special vertices in the unrestricted generality.
   This conditional statement does not discharge those general existence
   obligations.
2. Prove the compact properties and geometric standard-Levi restriction
   at this exact `K0`, including the literal compact-preimage equality and
   canonical/inherited topology comparison.
3. Construct one cofinal normal compact-open family before all standard
   parabolics, prove the ordered intersection bijections and inherited
   Levi basis, and establish all contraction and uniform clauses above.
   Corrected availability, including its Axiom 4.1.16, is the premise for
   this structural proof, not an assumed simultaneous-basis certificate.
4. Prove the needed uniformizer, character, split-component and root-group
   comparisons without narrowing the final statement to a depth,
   characteristic or ramification specialization. Rank zero, trivial
   radicals and nonsplit groups remain included.

The existing generic compact-containment result and S22-to-Jacquet
consumer retain their separate roles. This target neither duplicates
their generic statements nor claims that forgetting openness proves the
actual simultaneous basis. Jacquet exactness and the remaining Iwasawa
and Cartan proofs are outside this focused statement contribution.
