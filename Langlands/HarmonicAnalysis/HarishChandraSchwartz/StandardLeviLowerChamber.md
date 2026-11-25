# Re-choosing the chamber of a lower Levi subgroup

Module `Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviLowerChamber`, namespace
`Langlands.HarishChandraSchwartz.LowerChamber`.

## Purpose and provenance

Waldspurger proves Proposition VI.3.1 by induction. The source is J.-L. Waldspurger, *La formule
de Plancherel pour les groupes p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2
(2003); the proof is on printed pp. 302–305. In the weak-part step on p. 304 he applies the
induction hypothesis to a proper standard Levi subgroup `M' = M_{I'}` of `G`. Inside `M'` the
relevant parabolic is `M' ∩ s·P`, where `s ∈ W(M'|G|M)` has a representative
`n ∈ N_G(S)(F)`. This parabolic is semistandard in `M'`. In general it is not standard for the
chamber `ν` that `M'` inherits from `G`.

The Library target is
`StandardLeviPlancherelWavePacketSourceNormalizedStatement`. It is stated only for standard
parabolics `P_J` of a chamber `ν` and for a compact `K` with an Iwasawa decomposition for the
minimal parabolic `P_∅(ν)`. So the induction step has to re-choose the chamber of `M'`. This
module does that and checks that nothing else changes:

1. some generic chamber `ν'` of `M'` makes the conjugated cocharacter `sζ` standard;
2. the same compact subgroup is still an Iwasawa compact for `P_∅(ν')`, and it gives the same
   function `Ξ^{M'}`;
3. the standard parabolic and Levi of `ν'` are the lower groups of the weak expansion
   (`RationalWeakExpansionLowerGeometry`);
4. the conjugated representation `sπ` of that module becomes a representation of the standard
   Levi of `ν'`. A lower density package (`LowerDensityPackage`) is then literally the density
   data that the target asks for at `M'`.

Provenance is **derived**. Waldspurger does not state any of these facts. On p. 304 he applies
the induction hypothesis to the packets `f^{M'}` for `M' ∩ s·P` directly ("l'exposant `M'`
signifie comme toujours que l'on remplace `G` par `M'` dans les définitions"); he does not
re-choose a chamber. Every result here is a short consequence of published Library theorems.
No Weyl conjugation inside `M'` is needed: the chamber is re-chosen instead.

## Section `Chamber`: a chamber in which a cocharacter is standard

Here `j : T → H` is any morphism from a commutative group scheme `T` to a group scheme `H`.

- `simpleRootFace j ν' lam` is the set of simple roots of `ν'` on which `lam` vanishes.
- `isStandardCocharacter_zeroSimpleRoots`: suppose every root of `j` that is negative on `lam`
  is also negative on `ν'`. Then `lam` is a standard cocharacter of `ν'` for
  `simpleRootFace j ν' lam`. The proof is direct: a simple root of `ν'` outside this set pairs
  nonzero with `lam`. The pairing cannot be negative, because the root is positive on `ν'`. So
  it is positive.
- `zeroLabels` and `rootSet_zeroLabels` give `Finset` labels of `SimpleRoot j ν'` whose root set
  is `simpleRootFace j ν' lam`, assuming `ν'` has finitely many simple roots.
- `StandardChamber j lam` is a structure. It records a generic cocharacter `chamber`, labels
  `labels` with `rootSet j chamber labels = simpleRootFace j chamber lam`, the resulting
  `IsStandardCocharacter` proof, and the sign refinement: every root positive (negative) on
  `lam` is positive (negative) on `chamber`.
- `nonempty_standardChamber` assumes that `T` is a split torus and that `H → Spec F` is
  locally of finite type. It proves that a `StandardChamber j lam` exists, from the published
  `Geometry.Building.exists_genericCocharacter_refining`. The finiteness of the simple roots
  comes from `IsSplitTorus.finite_relativeRoots`.
- `standardChamber` chooses one such chamber with `Classical.choice`. None of the results below
  depend on which one is chosen.

## Section `Lower`: the lower Levi `M' = M_{I'}`

Notation used here: `M'` is `Standard.leviScheme i ν (rootSet i ν I')`, and `iL` is its maximal
split torus `Standard.leviTorusHom i ν (rootSet i ν I')`. `lam` stands for
`conjugatedCocharacter i ζ n`, the cocharacter `sζ`. The hypotheses are the usual ones: `G`
connected reductive (`hG`), `i` a maximal split torus (`hi`) and `ν` generic (`hν`). `M'` is
connected reductive (`lowerAmbient_isConnectedReductive`), and `iL` is a maximal split torus of
`M'` (`lowerTorus_isMaximalSplitTorus`).

### The chamber and the compact subgroup

- `lowerChamber hi I' ζ n : StandardChamber iL lam` is the chosen chamber of `M'` for `sζ`.
  Write `ν'` for its `chamber` and `J''` for its `labels`.
- `isIwasawaPair_lowerChamber`: if `K` is an Iwasawa compact of `M'(F)` for
  `P_∅(ν)`, it is one for `P_∅(ν')`. This is the published
  `IsIwasawaPair.rationalChangeMinimal`. The chamber `ν` restricted to `iL` is generic by
  `isGenericCocharacter_leviTorusHom`.
- `rationalXi_lowerChamber`: suppose moreover that `K` is open and compact. Then both chambers
  give the same function `Ξ^{M'}`. This is the published `rationalXi_changeMinimal`.
- `lowerCompact` is the compact `K ∩ M'(F)` of `M'(F)`, as an `OpenSubgroup`. It is
  built from the published `leviSchemeCompact` and `isOpen_leviSchemeCompact`.
- `isIwasawaPair_lowerCompact` assumes the Iwasawa decomposition `hM` of `M_{I'}(F)` for
  `K ∩ M_{I'}(F)` and the minimal parabolic. It proves that `leviSchemeCompact K` is an
  Iwasawa compact of `M'(F)` for `P_∅(ν')`. The proof combines the published
  `isIwasawaPair_leviSchemeCompact` with `isIwasawaPair_lowerChamber`.
- `rationalXi_lowerCompact`: for open compact `K` and this decomposition, `Ξ^{M'}` for
  `K ∩ M'` and the chamber `ν'` equals the Levi function `rationalLeviXi hKc hM` of `G`. It is
  read through the point equivalence `leviSchemePointsEquiv`. The proof rewrites with the
  published `rationalXi_leviScheme` and then applies `rationalXi_lowerChamber`.

For the weak expansion of `RationalWeakExpansionTargets`, the lower density package has
`PM.K = leviSchemeCompact K`. This is the field `CommonCompactNormalization.lower`. So the last
two results apply with the compact of that package.

### The lower groups are standard for `ν'`

Here `hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ`.

- `standardParabolicPoints_lowerChamber` states that `P_{J''}(ν')(F)`, the standard parabolic
  of `M'` for `ν'` and `J''`, equals the rational points of
  `lowerParabolic i ν (rootSet i ν I) (rootSet i ν I') n = M' ∩ n P_I n⁻¹`. The proof composes
  two published equalities. `standardLeviPlancherelParabolic_eq` at `M'`, `iL`, `ν'`, `J''` and
  `sζ` identifies `P_{J''}(ν')(F)` with the dynamic parabolic of
  `groupHom (sζ) ≫ iL`. By definition this is `lowerCocharacter i ν (rootSet i ν I') ζ n`, and
  `lowerCocharacter_points` identifies its dynamic parabolic with the lower parabolic.
- `standardLeviPoints_lowerChamber` is the same statement for the Levi `M_{J''}(F)` and
  `lowerLevi = M' ∩ n M_I n⁻¹`. It uses `Jacquet.standardLevi_eq_dynamic` at `M'` and the
  second half of `lowerCocharacter_points`.

### The conjugated representation and the lower density package

Here `hn` says that `n M_I n⁻¹ ≤ M_{I'}`, and `π` is an irreducible admissible representation
of `M_I(F)`. `𝐌'` is the subtype of `M'(F)` cut out by `standardLeviPoints iL ν' (rootSet J'')`.
This is the form in which the target takes its inducing representation.

- `lowerChamberLeviHomeomorph` abbreviates the published `standardLeviDynamicHomeomorph` at `M'`.
  It is the identification `Z_{M'}(sζ)(F) ≃ₜ* M_{J''}(F)`, which is the identity on points of
  `M'(F)`.
- `lowerChamberRepresentation` is the representation `π' = sπ ∘ e⁻¹` of `𝐌'`, where
  `e = lowerChamberLeviHomeomorph` and `sπ = lowerRepresentation` is the published conjugated
  representation `m' ↦ π(n⁻¹ m' n)`. It is defined with the published
  `IrreducibleAdmissibleRep.pullback`.
- `pullback_lowerChamberRepresentation` proves `SmoothRep.pullback e π'.obj = sπ.obj` by `rfl`.
  The left side is the representation `Aπ` that the target's density hypotheses use at `M'`.
- `lowerDensityPackage_eq` proves by `rfl` that `LowerDensityPackage hG hi hν I I' hζ n hn π
  hRefl hCST` equals `DynamicInducedOrbit.DensityPackage iL lam hRefl hCST hM'
  (SmoothRep.pullback e π'.obj)`. The fields of this structure correspond one to one, with the
  same types, to the target's density hypotheses at `M'`, `iL`, `ν'`, `J''`, `sζ` and `π'`:
  `Ks`, `hKs`, `hPKs`, `hOppKs`, `p`, `qrev`, the open sets `DForward`, `DReverse`, `D` with
  their properties, `hirr` and `hreg`.

## What this module does not provide

These results put the lower data into the target's form at the level of groups, compact
subgroups, `Ξ`, the inducing representation and the density hypotheses. They do not prove
anything analytic. In particular:

- the lower density packages themselves (Waldspurger IV.1.1 and V.2 at `M'`) are not
  constructed here;
- the Iwasawa decomposition `hM` of `M_{I'}(F)` for `K ∩ M_{I'}(F)` is a hypothesis;
- the target at `M'` takes square integrability modulo the split component
  `rationalLeviSplitCenter J'' s'` of `M_{J''}`, with the character measure
  `standardLeviUnitaryUnramifiedCharacterHaar J'' s' …`. The weak expansion of
  `RationalWeakExpansionTargets` uses instead the conjugated subgroup `lowerCentral`, the measure
  `lowerMeasure` and the image measure `lowerCharacterMeasure`. Comparing the two is left to the
  module `StandardLeviLowerSplitCenter`;
- the target's sections `rationalInducedSmoothOrbitSections` at `M'` are not compared with the
  dynamic lower sections `LowerSectionsAt` of `RationalWeakExpansionTargets`, and the two wave
  packets are not compared. This is left to the module `StandardLeviLowerPacket`.
