import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviLowerChamber
import Langlands.Representation.Plancherel.StandardLeviCharacterMeasure
import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitCentralFiberAdapter

/-! # Split component, central quotient and character measures of a lower Levi subgroup

In the induction step of Waldspurger VI.3.1 (printed p.304) the lower packets of the weak
expansion (Task 7454, `RationalWeakExpansionLowerOrbit`) live on the literal Levi `s·M` of the
lower cocharacter `sζ` in `M' = M_{I'}`. They use the conjugated central subgroup `sC`, the
transported quotient Haar measure `sμ` and the image `sρ` of the I.1 character measure.
The source-normalized target at `M'` and the chamber of `sζ` (`StandardLeviLowerChamber`) instead
asks for a split component `s'` of the literal standard Levi scheme `M_{J''}`, the subgroup
`A_{M_{J''}}(F)`, a Haar measure on the quotient by it, and the I.1 character measure of `s'`.
This module identifies the two sets of data exactly.

* `rationalUnitaryCharacterIso`, `map_rationalUnitaryUnramifiedCharacterHaar_iso`: an isomorphism
  of group schemes carries the I.1 character Haar measure of a central subgroup to that of its
  image.
* `pullback_smul_of_apply`, `map_discreteSeriesStabilizer`, `map_discreteSeriesStabilizer_of_eq`,
  `card_discreteSeriesStabilizer`, `finite_discreteSeriesStabilizer`: pulling discrete-series
  classes back along a multiplicative homeomorphism `e` intertwines the twists by `χ` and by
  `χ ∘ e`, and identifies the stabilizers.
* `orbitTransport`, `orbitTransport_orbitMap`, `orbitTransport_val`,
  `map_discreteSeriesOrbitMeasure_orbitTransport`: discrete-series orbits and their orbit
  measures transport along a multiplicative homeomorphism, for two norm families whose unitary
  character groups are identified compatibly. The target class `ω'` is an argument, with a proof
  that it is the pullback of `ω`.
* `lowerChamberLeviEquiv`: `M_{J''}(F) ≃ Z_{M'}(sζ)(F)`, the inverse of
  `lowerChamberLeviHomeomorph`.
* `lowerLeviIso`: the scheme isomorphism `M_I ≅ M_{J''}`, conjugation by `n` followed by the
  identification of the centralizer of `sζ` with the standard Levi of the new chamber;
  `leviRationalPointHomeomorph_lowerLeviIso` and `lowerChamberLeviEquiv_lowerLeviIso` compute it
  on points.
* `lowerSplit`, `isSplitComponent_lowerSplit`, `lowerLevi_isConnectedReductive`,
  `finiteIndex_lowerSplit`: the split component `s' = s ≫ (M_I ≅ M_{J''})` and the finite-index
  premise of the I.1 measure for it.
* `map_lowerSplitCenter`, `lowerSplitCenter_normal`, `lowerSplit_range_normal`:
  `A_{M_{J''}}(F)` is the conjugated subgroup `sC` of Task 7454, and it is normal.
* `lowerChamberQuotientEquiv`, `lowerChamberQuotientMeasure`, `lowerChamberQuotientMeasure_map`,
  `lowerChamberRepresentation_isSquareIntegrable`: the quotient Haar measure on
  `M_{J''}(F)/A_{M_{J''}}(F)` corresponding to `sμ`, and square integrability of `π'` there.
* `lowerChamberCharacterTransport`, `lowerChamberCharacterTransport_apply`,
  `map_lowerCharacterMeasure`: the I.1 measure of `s'` is the image of Task 7454's
  `lowerCharacterMeasure` of the I.1 measure of `s`.
* `pullback_lowerClass`, `lowerChamberOrbitTransport`, `lowerChamberOrbitTransport_orbitMap`,
  `finite_lowerChamberStabilizer`, `map_lowerOrbitMeasure`: the class of `π'` is the pullback of
  the class of `sπ`; the orbit `sO` with its orbit measure is the orbit of `π'` with the orbit
  measure `dO'` of the target at `M'`.

Two proofs, `map_lowerCharacterMeasure` and `map_lowerOrbitMeasure`, raise `maxHeartbeats`
(to 800000 and 1000000). They are short chains of equalities, but each step elaborates terms
that contain the full lower-Levi data of Task 7454 (about 530000 and 670000 heartbeats).
-/

noncomputable section

universe u uV uG uH uI uJ

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.LowerSplitCenter

/-! ### Transport of discrete-series orbits and orbit measures -/

section OrbitTransport

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H] (e : H ≃ₜ* G)
  {I : Type uI} {J : Type uJ} {νG : I → (G →* ℝ≥0ˣ)} {νH : J → (H →* ℝ≥0ˣ)}
  (c : unitaryUnramifiedCharacters νG ≃ₜ* unitaryUnramifiedCharacters νH)
  (hc : ∀ χ h, (c χ).val h = χ.val (e h))
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  (B : Subgroup H) [B.Normal] (hB : B ≤ Subgroup.center H)
  (hAB : B.map e.toMulEquiv.toMonoidHom = A)
  [MeasurableSpace (G ⧸ A)] [BorelSpace (G ⧸ A)]
  [MeasurableSpace (H ⧸ B)] [BorelSpace (H ⧸ B)]
  (μG : Measure (G ⧸ A)) [μG.IsHaarMeasure] (μH : Measure (H ⧸ B)) [μH.IsHaarMeasure]
  (hμ : μH.map (quotientContinuousMulEquiv e A B hAB) = μG)

set_option hygiene false in
local notation "pb" => DiscreteSeriesClass.pullback e A hA B hB hAB μG μH hμ

include hc in
/-- Pullback of classes intertwines twisting by `χ` and by its transport `c χ = χ ∘ e`. -/
theorem pullback_smul_of_apply (χ : unitaryUnramifiedCharacters νG)
    (ω : DiscreteSeriesClass.{uG, uV} A hA μG) :
    pb (χ • ω) = c χ • pb ω := by
  have hhom : (c χ).val.toMonoidHom = χ.val.toMonoidHom.comp e.toMonoidHom :=
    MonoidHom.ext (hc χ)
  have hopen : IsOpen ((χ.val.toMonoidHom.comp e.toMonoidHom).ker : Set H) := by
    rw [← hhom]
    exact unramifiedCharacter_isOpen_ker νH ⟨(c χ).val, (c χ).property.1⟩
  apply Subtype.ext
  change SmoothDualClass.pullback e (SmoothDualClass.twist χ.val.toMonoidHom _ ω.val) =
    SmoothDualClass.twist (c χ).val.toMonoidHom _ (SmoothDualClass.pullback e ω.val)
  rw [SmoothDualClass.pullback_twist e _ _ hopen]
  congr 1
  exact hhom.symm

include hc in
/-- The transport `c` carries the stabilizer of `ω` onto the stabilizer of its pullback. -/
theorem map_discreteSeriesStabilizer (ω : DiscreteSeriesClass.{uG, uV} A hA μG) :
    (discreteSeriesStabilizer A hA μG νG ω).map c.toMulEquiv.toMonoidHom =
      discreteSeriesStabilizer B hB μH νH (pb ω) := by
  ext x
  constructor
  · rintro ⟨χ, hχ, rfl⟩
    change c χ • pb ω = pb ω
    rw [← pullback_smul_of_apply e c hc A hA B hB hAB μG μH hμ, hχ]
  · intro hx
    refine ⟨c.symm x, ?_, c.apply_symm_apply x⟩
    change c.symm x • ω = ω
    apply DiscreteSeriesClass.pullback_injective e A hA B hB hAB μG μH hμ
    rw [pullback_smul_of_apply e c hc A hA B hB hAB μG μH hμ, c.apply_symm_apply]
    exact hx

variable (ω : DiscreteSeriesClass.{uG, uV} A hA μG) (ω' : DiscreteSeriesClass.{uH, uV} B hB μH)
  (hω : pb ω = ω')

include hc hω in
/-- The transport `c` carries the stabilizer of `ω` onto the stabilizer of `ω' = ω ∘ e`. -/
theorem map_discreteSeriesStabilizer_of_eq :
    (discreteSeriesStabilizer A hA μG νG ω).map c.toMulEquiv.toMonoidHom =
      discreteSeriesStabilizer B hB μH νH ω' := by
  subst hω
  exact map_discreteSeriesStabilizer e c hc A hA B hB hAB μG μH hμ ω

include hc hω in
/-- The two stabilizers have the same cardinality. -/
theorem card_discreteSeriesStabilizer :
    Nat.card (discreteSeriesStabilizer A hA μG νG ω) =
      Nat.card (discreteSeriesStabilizer B hB μH νH ω') :=
  Nat.card_congr
    (((discreteSeriesStabilizer A hA μG νG ω).equivMapOfInjective c.toMulEquiv.toMonoidHom
      c.injective).trans
      (MulEquiv.subgroupCongr
        (map_discreteSeriesStabilizer_of_eq e c hc A hA B hB hAB μG μH hμ ω ω' hω))).toEquiv

include hc hω in
/-- Finiteness of the stabilizer transports. -/
theorem finite_discreteSeriesStabilizer [Finite (discreteSeriesStabilizer A hA μG νG ω)] :
    Finite (discreteSeriesStabilizer B hB μH νH ω') :=
  Finite.of_surjective _
    (((discreteSeriesStabilizer A hA μG νG ω).equivMapOfInjective c.toMulEquiv.toMonoidHom
      c.injective).trans
      (MulEquiv.subgroupCongr
        (map_discreteSeriesStabilizer_of_eq e c hc A hA B hB hAB μG μH hμ ω ω' hω))).surjective

/-- **Transport of a discrete-series orbit**: the orbit of `ω` is homeomorphic to the orbit of
`ω' = ω ∘ e`, by `χ • ω ↦ c χ • ω'`. The class `ω'` is a parameter, together with a proof of
`ω ∘ e = ω'`, so that it can be given in any form definitionally equal to the pullback. -/
def orbitTransport :
    discreteSeriesOrbit A hA μG νG ω ≃ₜ discreteSeriesOrbit B hB μH νH ω' :=
  (discreteSeriesOrbitHomeomorph A hA μG νG ω).symm.trans
    ((quotientContinuousMulEquiv c (discreteSeriesStabilizer B hB μH νH ω')
      (discreteSeriesStabilizer A hA μG νG ω)
      (map_discreteSeriesStabilizer_of_eq e c hc A hA B hB hAB μG μH hμ ω ω' hω)).toHomeomorph.trans
        (discreteSeriesOrbitHomeomorph B hB μH νH ω'))

theorem orbitTransport_orbitMap (χ : unitaryUnramifiedCharacters νG) :
    orbitTransport e c hc A hA B hB hAB μG μH hμ ω ω' hω (discreteSeriesOrbitMap A hA μG νG ω χ) =
      discreteSeriesOrbitMap B hB μH νH ω' (c χ) := by
  simp only [orbitTransport, discreteSeriesOrbitMap, Homeomorph.trans_apply,
    Homeomorph.symm_apply_apply]
  rfl

theorem orbitTransport_val (x : discreteSeriesOrbit A hA μG νG ω) :
    (orbitTransport e c hc A hA B hB hAB μG μH hμ ω ω' hω x).val = pb x.val := by
  subst hω
  obtain ⟨χ, rfl⟩ := (isOpenQuotientMap_discreteSeriesOrbitMap A hA μG νG ω).surjective x
  rw [orbitTransport_orbitMap, discreteSeriesOrbitMap_val, discreteSeriesOrbitMap_val,
    pullback_smul_of_apply e c hc A hA B hB hAB μG μH hμ]

/-- **The orbit measures correspond.** The orbit measure of `ω` for the character measure `λ`
is carried by `orbitTransport` to the orbit measure of `ω' = ω ∘ e` for the image measure
`c_* λ`. -/
theorem map_discreteSeriesOrbitMeasure_orbitTransport
    [Finite (discreteSeriesStabilizer A hA μG νG ω)]
    [Finite (discreteSeriesStabilizer B hB μH νH ω')]
    (lam : Measure (unitaryUnramifiedCharacters νG)) :
    (discreteSeriesOrbitMeasure νG A hA μG ω lam).map
        (orbitTransport e c hc A hA B hB hAB μG μH hμ ω ω' hω) =
      discreteSeriesOrbitMeasure νH B hB μH ω' (lam.map c) := by
  have hcomp : (orbitTransport e c hc A hA B hB hAB μG μH hμ ω ω' hω) ∘
      discreteSeriesOrbitMap A hA μG νG ω =
      discreteSeriesOrbitMap B hB μH νH ω' ∘ c := by
    funext χ
    exact orbitTransport_orbitMap e c hc A hA B hB hAB μG μH hμ ω ω' hω χ
  rw [discreteSeriesOrbitMeasure, discreteSeriesOrbitMeasure,
    Measure.map_smul _
      (orbitTransport e c hc A hA B hB hAB μG μH hμ ω ω' hω).continuous.measurable.aemeasurable,
    Measure.map_map (orbitTransport e c hc A hA B hB hAB μG μH hμ ω ω' hω).continuous.measurable
      (continuous_discreteSeriesOrbitMap A hA μG νG ω).measurable,
    hcomp, ← Measure.map_map (continuous_discreteSeriesOrbitMap B hB μH νH ω').measurable
      (map_continuous c).measurable,
    card_discreteSeriesStabilizer e c hc A hA B hB hAB μG μH hμ ω ω' hω]

end OrbitTransport

/-! ### The I.1 character measure along an isomorphism of group schemes -/

section SchemeIso

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {L L' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine L.X.left] [IsAffine L'.X.left]
  [LocallyOfFiniteType L.X.hom] [LocallyOfFiniteType L'.X.hom] (Φ : L ≅ L')

local instance schemeIsoTopology : TopologicalSpace (rationalPoints L) :=
  rationalPointTopology F L.X
local instance schemeIsoTopology' : TopologicalSpace (rationalPoints L') :=
  rationalPointTopology F L'.X
local instance schemeIsoCompact : CompactSpace
    (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters L psi).toMul)) :=
  compactSpace_rationalUnitaryUnramifiedCharacters L
local instance schemeIsoCompact' : CompactSpace
    (unitaryUnramifiedCharacters (fun psi => (rationalNormCharacters L' psi).toMul)) :=
  compactSpace_rationalUnitaryUnramifiedCharacters L'

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine L.X.left]
  [IsAffine L'.X.left] [LocallyOfFiniteType L.X.hom] [LocallyOfFiniteType L'.X.hom] in
theorem rationalPoints_map_inv_hom (y : rationalPoints L) :
    rationalPoints.map Φ.inv (rationalPoints.map Φ.hom y) = y := by
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine L.X.left]
  [IsAffine L'.X.left] [LocallyOfFiniteType L.X.hom] [LocallyOfFiniteType L'.X.hom] in
theorem rationalPoints_map_hom_inv (y : rationalPoints L') :
    rationalPoints.map Φ.hom (rationalPoints.map Φ.inv y) = y := by
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id]

/-- **Unitary unramified characters along `Φ : L ≅ L'`**: `z ↦ z ∘ Φ⁻¹` on rational points. -/
def rationalUnitaryCharacterIso :
    unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul) ≃ₜ*
      unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters L' ψ).toMul) where
  toFun := rationalUnitaryUnramifiedCharacterRestrict Φ.inv
  invFun := rationalUnitaryUnramifiedCharacterRestrict Φ.hom
  left_inv z := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro y
    change z.val (rationalPoints.map Φ.inv (rationalPoints.map Φ.hom y)) = z.val y
    rw [rationalPoints_map_inv_hom]
  right_inv z := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro y
    change z.val (rationalPoints.map Φ.hom (rationalPoints.map Φ.inv y)) = z.val y
    rw [rationalPoints_map_hom_inv]
  map_mul' := map_mul _
  continuous_toFun := (rationalUnitaryUnramifiedCharacterRestrict Φ.inv).continuous
  continuous_invFun := (rationalUnitaryUnramifiedCharacterRestrict Φ.hom).continuous

omit [LocallyOfFiniteType L.X.hom] [LocallyOfFiniteType L'.X.hom] in
@[simp]
theorem rationalUnitaryCharacterIso_apply
    (z : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (y : rationalPoints L') :
    (rationalUnitaryCharacterIso Φ z).val y = z.val (rationalPoints.map Φ.inv y) :=
  rfl

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ L)

omit [LocallyOfFiniteType L.X.hom] [LocallyOfFiniteType L'.X.hom] in
/-- Restriction to `T` along `s ≫ Φ.hom`, after `z ↦ z ∘ Φ⁻¹`, equals restriction of `z` along
`s`. -/
theorem restrict_comp_rationalUnitaryCharacterIso
    (z : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)) :
    rationalUnitaryUnramifiedCharacterRestrict (s ≫ Φ.hom) (rationalUnitaryCharacterIso Φ z) =
      rationalUnitaryUnramifiedCharacterRestrict s z := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro t
  change z.val (rationalPoints.map Φ.inv (rationalPoints.map (s ≫ Φ.hom) t)) =
    z.val (rationalPoints.map s t)
  congr 1
  rw [← rationalPoints_map_inv_hom Φ (rationalPoints.map s t)]
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

omit [LocallyOfFiniteType L.X.hom] [LocallyOfFiniteType L'.X.hom] in
/-- The restriction kernels for `s` and `s ≫ Φ` have the same cardinality. -/
theorem card_ker_restrict_comp_iso :
    Nat.card (rationalUnitaryUnramifiedCharacterRestrict (s ≫ Φ.hom)).toMonoidHom.ker =
      Nat.card (rationalUnitaryUnramifiedCharacterRestrict s).toMonoidHom.ker := by
  refine (Nat.card_congr (Equiv.subtypeEquiv (rationalUnitaryCharacterIso Φ).toEquiv
    (fun z => ?_))).symm
  change rationalUnitaryUnramifiedCharacterRestrict s z = 1 ↔
    rationalUnitaryUnramifiedCharacterRestrict (s ≫ Φ.hom) (rationalUnitaryCharacterIso Φ z) = 1
  rw [restrict_comp_rationalUnitaryCharacterIso]

/-- **The I.1 character measure is natural under isomorphisms.** For a central `s : T → L` and
`Φ : L ≅ L'`, the image of the I.1 Haar measure of `s` under `z ↦ z ∘ Φ⁻¹` is the I.1 Haar
measure of `s ≫ Φ`. -/
theorem map_rationalUnitaryUnramifiedCharacterHaar_iso (hs : IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) (hs' : IsCentral (s ≫ Φ.hom))
    (hindex' : (RenardCartan.splitValuationImage (s ≫ Φ.hom)).FiniteIndex) :
    (rationalUnitaryUnramifiedCharacterHaar s hs hindex).map (rationalUnitaryCharacterIso Φ) =
      rationalUnitaryUnramifiedCharacterHaar (s ≫ Φ.hom) hs' hindex' := by
  rw [rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability,
    rationalUnitaryUnramifiedCharacterHaar_eq_smul_probability,
    Measure.map_smul (f := ⇑(rationalUnitaryCharacterIso Φ)) _
      (map_continuous (rationalUnitaryCharacterIso Φ)).measurable.aemeasurable,
    card_ker_restrict_comp_iso]
  congr 1
  exact ((rationalUnitaryCharacterIso Φ).toMulEquiv.toMonoidHom.measurePreserving
    (rationalUnitaryCharacterIso Φ).continuous (rationalUnitaryCharacterIso Φ).surjective
    (by simp)).map_eq

end SchemeIso

/-! ### The lower Levi `M' = M_{I'}` and the chamber of `sζ` -/

section Lower

open Langlands.Plancherel.DynamicOppositeStandardIntertwining
open RationalPointFamily WeakExpansion LowerChamber

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerSplitLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerSplitLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hi : IsMaximalSplitTorus i) (I' : Finset (SimpleRoot i ν))
  (ζ : cocharacterLattice T) (n : normalizerPoints i)
  (hG : IsConnectedReductive G) (hν : IsGenericCocharacter i ν)
  (I : Finset (SimpleRoot i ν)) (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "M'" => Standard.leviScheme i ν (rootSet i ν I')
set_option hygiene false in
local notation "iL" => Standard.leviTorusHom i ν (rootSet i ν I')
set_option hygiene false in
local notation "c" => lowerChamber hi I' ζ n
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "hiL" => lowerTorus_isMaximalSplitTorus hi I'
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐋'" => Standard.leviScheme iL (c).chamber (rootSet iL (c).chamber (c).labels)
set_option hygiene false in
local notation "e₀" => lowerChamberLeviHomeomorph hi I' ζ n hG hν
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "Φ₁" => lowerParameterIso hG hi hν I I' hζ n hn
set_option hygiene false in
local notation "Φ₂" => standardLeviParameterIso hM' hiL (c).isGeneric (c).labels (c).isStandard

-- `M_I(F)` and `M_{J''}(F)` as subtypes, written as in the source-normalized target.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "𝐌'" => {x : rationalPoints M' //
  @Membership.mem (rationalPoints M') (Subgroup (rationalPoints M')) _
    (standardLeviPoints iL (c).chamber (rootSet iL (c).chamber (c).labels)) x}

/-- `Z_{M'}(sζ)(F) = M_{J''}(F)` read from `M_{J''}(F)`: the inverse of
`lowerChamberLeviHomeomorph`, with its codomain written as the literal Levi `(s·M)(F)` of the
lower cocharacter, on which Task 7454's lower data live. -/
abbrev lowerChamberLeviEquiv : 𝐌' ≃ₜ* levi χs := (e₀).symm

set_option hygiene false in
local notation "e₁" => lowerChamberLeviEquiv hi I' ζ n hG hν

/-! #### The scheme isomorphism `M_I ≅ M_{J''}` -/

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem rationalPoints_map_comp {L₁ L₂ L₃ : GroupScheme (Spec (CommRingCat.of F))}
    (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) (y : rationalPoints L₁) :
    rationalPoints.map (f ≫ g) y = rationalPoints.map g (rationalPoints.map f y) := by
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The identification `Z_{M'}(sζ) ≅ M_{J''}` of the centralizer scheme of `sζ` in `M'` with the
standard Levi scheme of the chamber of `sζ` (`standardLeviParameterIso` at `M'`) is, on points of
the centralizer scheme of the lower cocharacter `χ_s`, the identification
`Z_{M'}(sζ)(F) = M_{J''}(F)`. -/
theorem leviRationalPointHomeomorph_lowerParameterLeviIso
    (m : rationalPoints (parameterScheme χs)) :
    leviRationalPointHomeomorph iL (c).chamber (c).labels (rationalPoints.map (Φ₂).hom m) =
      e₀ (parameterHomeomorph (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ iL) m) :=
  leviRationalPointHomeomorph_map_standardLeviParameterIso hM' hiL (c).isGeneric (c).labels
    (c).isStandard m

/-- **`M_I ≅ M_{J''}`.** The standard Levi scheme `M_I` of `G` is identified with the standard
Levi scheme `M_{J''}` of `M'` for the chamber of `sζ`: first with the centralizer of `sζ` in `M'`
(the inverse of `lowerParameterIso`, conjugation by `n` over `G`), then with `M_{J''}`
(`standardLeviParameterIso` at `M'`). -/
def lowerLeviIso : 𝐋 ≅ 𝐋' := (Φ₁).symm ≪≫ Φ₂

/-- On points, `M_I ≅ M_{J''}` is the conjugation `m ↦ n m n⁻¹` followed by the identification
`Z_{M'}(sζ)(F) = M_{J''}(F)`. -/
theorem leviRationalPointHomeomorph_lowerLeviIso (y : rationalPoints 𝐋) :
    leviRationalPointHomeomorph iL (c).chamber (c).labels
        (rationalPoints.map (lowerLeviIso hi I' ζ n hG hν I hζ hn).hom y) =
      e₀ (eₛ (leviRationalPointHomeomorph i ν I y)) := by
  have hpar : parameterHomeomorph χs (rationalPoints.map (Φ₁).inv y) =
      eₛ (leviRationalPointHomeomorph i ν I y) := by
    rw [← ContinuousMulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [← leviRationalPointHomeomorph_lowerParameterIso hG hi hν I I' hζ n hn,
      rationalPoints_map_hom_inv]
  have hmap : rationalPoints.map (lowerLeviIso hi I' ζ n hG hν I hζ hn).hom y =
      rationalPoints.map (Φ₂).hom (rationalPoints.map (Φ₁).inv y) :=
    rationalPoints_map_comp (Φ₁).inv (Φ₂).hom y
  rw [hmap]
  exact (leviRationalPointHomeomorph_lowerParameterLeviIso hi I' ζ n hG hν _).trans
    (congrArg (e₀) hpar)

/-- The same identity read in `Z_{M'}(sζ)(F)`. -/
theorem lowerChamberLeviEquiv_lowerLeviIso (y : rationalPoints 𝐋) :
    e₁ (leviRationalPointHomeomorph iL (c).chamber (c).labels
        (rationalPoints.map (lowerLeviIso hi I' ζ n hG hν I hζ hn).hom y)) =
      eₛ (leviRationalPointHomeomorph i ν I y) := by
  rw [leviRationalPointHomeomorph_lowerLeviIso]
  exact (e₀).symm_apply_apply _

/-! #### The split component `s'` and `A_{M_{J''}}(F)` -/

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine A.X.left] (s : A.toGrp ⟶ 𝐋)

/-- **The split component `s' : A → M_{J''}`**, the image of a split component `s` of `M_I`
under `M_I ≅ M_{J''}`. -/
abbrev lowerSplit : A.toGrp ⟶ 𝐋' := s ≫ (lowerLeviIso hi I' ζ n hG hν I hζ hn).hom

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine A.X.left] in
theorem isSplitComponent_lowerSplit (hs : IsSplitComponent s) :
    IsSplitComponent (lowerSplit hi I' ζ n hG hν I hζ hn s) :=
  hs.comp_iso _

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hν in
/-- The standard Levi `M_{J''}` of `M'` is connected reductive. -/
theorem lowerLevi_isConnectedReductive : IsConnectedReductive 𝐋' :=
  BruhatTits.SpecialCompact.standardLevi_isConnectedReductive hM' iL hiL (c).chamber
    (c).isGeneric (rootSet iL (c).chamber (c).labels) (rootSet_subset iL (c).chamber (c).labels)

omit [IsAffine A.X.left] in
/-- The finite-index premise of the I.1 measure holds for `s'`. -/
theorem finiteIndex_lowerSplit (hs : IsSplitComponent s) :
    (RenardCartan.splitValuationImage (lowerSplit hi I' ζ n hG hν I hζ hn s)).FiniteIndex :=
  finiteIndex_splitValuationImage_of_isSplitComponent
    (lowerLevi_isConnectedReductive hi I' ζ n hG hν) _ (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I s
set_option hygiene false in
local notation "CM'" => rationalLeviSplitCenter (c).labels (lowerSplit hi I' ζ n hG hν I hζ hn s)

omit [IsAffine A.X.left] in
/-- **`A_{M_{J''}}(F)` is the conjugated subgroup `sC`.** Under `Z_{M'}(sζ)(F) = M_{J''}(F)`,
the image of the split component `s'` is Task 7454's `lowerCentral` of `A_{M_I}(F)`. -/
theorem map_lowerSplitCenter :
    (CM').map (e₁).toMulEquiv.toMonoidHom = lowerCentral hG hi hν I I' hζ n hn CM := by
  have hcomp : rationalPoints.map (lowerSplit hi I' ζ n hG hν I hζ hn s) =
      (rationalPoints.map (lowerLeviIso hi I' ζ n hG hν I hζ hn).hom).comp
        (rationalPoints.map s) := by
    ext y
    simp only [MonoidHom.comp_apply, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  rw [rationalLeviSplitCenter, rationalLeviSplitCenter, lowerCentral, hcomp,
    MonoidHom.range_comp, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  refine congrArg (fun f => Subgroup.map f (rationalPoints.map s).range)
    (MonoidHom.ext fun y => ?_)
  exact lowerChamberLeviEquiv_lowerLeviIso hi I' ζ n hG hν I hζ hn y

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [IsAffine A.X.left] in
/-- `A_{M_{J''}}(F)` is normal, being central. -/
theorem lowerSplitCenter_normal (hs : IsSplitComponent s) : (CM').Normal :=
  Subgroup.normal_of_le_center (rationalLeviSplitCenter_le_center (c).labels _
    (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [IsAffine A.X.left] in
/-- The image of `A(F)` in `M_{J''}`'s own points is normal, being central. -/
theorem lowerSplit_range_normal (hs : IsSplitComponent s) :
    (rationalPoints.map (lowerSplit hi I' ζ n hG hν I hζ hn s)).range.Normal :=
  Subgroup.normal_of_le_center
    (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs).isCentralSplitTorus.range_le_center

/-! #### The central quotient and square integrability -/

set_option hygiene false in
local notation "sC" => lowerCentral hG hi hν I I' hζ n hn CM
set_option hygiene false in
local notation "hAB" => map_lowerSplitCenter hi I' ζ n hG hν I hζ hn s

variable [(CM).Normal] [(CM').Normal]

/-- `M_{J''}(F)/A_{M_{J''}}(F) ≅ (s·M)(F)/sC`, induced by `Z_{M'}(sζ)(F) = M_{J''}(F)`. -/
abbrev lowerChamberQuotientEquiv : (𝐌' ⧸ CM') ≃ₜ* (levi χs ⧸ sC) :=
  quotientContinuousMulEquiv (e₁) (sC) CM' (hAB)

variable [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  [MeasurableSpace (𝐌' ⧸ CM')] [BorelSpace (𝐌' ⧸ CM')]

/-- **The quotient Haar measure on `M_{J''}(F)/A_{M_{J''}}(F)`**: the image of Task 7454's
transported measure `sμ = lowerMeasure` on `(s·M)(F)/sC`. -/
def lowerChamberQuotientMeasure : Measure (𝐌' ⧸ CM') :=
  (lowerMeasure hG hi hν I I' hζ n hn CM mu).map
    (lowerChamberQuotientEquiv hi I' ζ n hG hν I hζ hn s).symm

instance lowerChamberQuotientMeasure_isHaarMeasure :
    (lowerChamberQuotientMeasure hi I' ζ n hG hν I hζ hn s mu).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map _ _

omit [IsAffine A.X.left] [BorelSpace (𝐌 ⧸ CM)] [mu.IsHaarMeasure] in
/-- The quotient measure on `M_{J''}(F)/A_{M_{J''}}(F)` corresponds to `sμ`. -/
theorem lowerChamberQuotientMeasure_map :
    (lowerChamberQuotientMeasure hi I' ζ n hG hν I hζ hn s mu).map
        (lowerChamberQuotientEquiv hi I' ζ n hG hν I hζ hn s) =
      lowerMeasure hG hi hν I I' hζ n hn CM mu := by
  rw [lowerChamberQuotientMeasure, Measure.map_map
    (map_continuous (lowerChamberQuotientEquiv hi I' ζ n hG hν I hζ hn s)).measurable
    (map_continuous (lowerChamberQuotientEquiv hi I' ζ n hG hν I hζ hn s).symm).measurable]
  convert Measure.map_id
  ext x
  exact (lowerChamberQuotientEquiv hi I' ζ n hG hν I hζ hn s).apply_symm_apply x

variable (hs : IsSplitComponent s)

set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I s hs
set_option hygiene false in
local notation "hCM'" => rationalLeviSplitCenter_le_center (c).labels
  (lowerSplit hi I' ζ n hG hν I hζ hn s) (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
set_option hygiene false in
local notation "hsC" => lowerCentral_le_center hG hi hν I I' hζ n hn CM hCM
set_option hygiene false in
local notation "mu'" => lowerChamberQuotientMeasure hi I' ζ n hG hν I hζ hn s mu

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)

omit [IsAffine A.X.left] in
include hsq in
/-- **`π'` is square integrable modulo `A_{M_{J''}}(F)`.** The representation
`π' = lowerChamberRepresentation` of `M_{J''}(F)` is square integrable modulo the split center
`A_{M_{J''}}(F)` for `lowerChamberQuotientMeasure` when `π` is square integrable modulo
`A_{M_I}(F)` for `μ`. -/
theorem lowerChamberRepresentation_isSquareIntegrable :
    IsSquareIntegrableModCentralSubgroup CM' hCM'
      (lowerChamberRepresentation hi I' ζ n hG hν I hζ hn π).obj.representation mu' :=
  (isSquareIntegrableModCentralSubgroup_comp_iff (e₁) (sC) hsC CM' hCM' (hAB)
    (lowerMeasure hG hi hν I I' hζ n hn CM mu) mu'
    (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu)
    (lowerRepresentation hG hi hν I I' hζ n hn π).obj.representation).mpr
    (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq)

/-! #### The I.1 character measures -/

set_option hygiene false in
local notation "eX" => standardLeviUnitaryCharacterHomeomorph I
set_option hygiene false in
local notation "eX'" => standardLeviUnitaryCharacterHomeomorph (c).labels
set_option hygiene false in
local notation "Ψ" => lowerLeviIso hi I' ζ n hG hν I hζ hn

/-- **Characters of `(s·M)(F)` as characters of `M_{J''}(F)`**: `z ↦ z ∘ e₀⁻¹`, where
`e₀ : Z_{M'}(sζ)(F) = M_{J''}(F)`. It is built as the inverse of Task 7454's conjugation
`Im X(M_I) ≃ Im X(s·M)`, followed by the passage to the Levi scheme `M_I`, the scheme
isomorphism `M_I ≅ M_{J''}` and the passage back to `M_{J''}(F)`, so that it carries
`lowerCharacterMeasure` of the I.1 measure of `s` to the I.1 measure of `s'`. -/
def lowerChamberCharacterTransport :
    unitaryUnramifiedCharacters (leviNormCharacters χs) ≃ₜ*
      unitaryUnramifiedCharacters (leviRationalNormCharacters iL (c).chamber (c).labels) :=
  (lowerCharacterConjugation hG hi hν I I' hζ n hn).symm.trans
    ((eX).symm.trans ((rationalUnitaryCharacterIso (Ψ)).trans (eX')))

/-- The transported character is `z ∘ e₀⁻¹`. -/
theorem lowerChamberCharacterTransport_apply
    (z : unitaryUnramifiedCharacters (leviNormCharacters χs)) (h : 𝐌') :
    (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn z).val h = z.val (e₁ h) := by
  have key := leviRationalPointHomeomorph_lowerLeviIso hi I' ζ n hG hν I hζ hn
    (rationalPoints.map (Ψ).inv ((leviRationalPointHomeomorph iL (c).chamber (c).labels).symm h))
  rw [rationalPoints_map_hom_inv, ContinuousMulEquiv.apply_symm_apply] at key
  have key' : e₁ h = eₛ (leviRationalPointHomeomorph i ν I (rationalPoints.map (Ψ).inv
      ((leviRationalPointHomeomorph iL (c).chamber (c).labels).symm h))) := by
    conv_lhs => rw [key]
    exact (e₀).symm_apply_apply _
  rw [key']
  rfl

variable (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)

set_option maxHeartbeats 800000 in
omit [(CM).Normal] [(CM').Normal] [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  [MeasurableSpace (𝐌' ⧸ CM')] [BorelSpace (𝐌' ⧸ CM')] in
/-- **The I.1 measure of `s'` is the transported I.1 measure of `s`.** The image under
`lowerChamberCharacterTransport` of Task 7454's `lowerCharacterMeasure` of
`standardLeviUnitaryUnramifiedCharacterHaar I s` is
`standardLeviUnitaryUnramifiedCharacterHaar J'' s'`. -/
theorem map_lowerCharacterMeasure :
    (lowerCharacterMeasure hG hi hν I I' hζ n hn
        (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex)).map
        (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn) =
      standardLeviUnitaryUnramifiedCharacterHaar (c).labels (lowerSplit hi I' ζ n hG hν I hζ hn s)
        (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
        (finiteIndex_lowerSplit hi I' ζ n hG hν I hζ hn s hs) := by
  have hcomp : ⇑(lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn) ∘
      (⇑(lowerCharacterConjugation hG hi hν I I' hζ n hn) ∘ ⇑(eX)) =
      ⇑(eX') ∘ ⇑(rationalUnitaryCharacterIso (Ψ)) := by
    funext z
    simp only [Function.comp_apply, lowerChamberCharacterTransport,
      ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.symm_apply_apply]
  have h1 : lowerCharacterMeasure hG hi hν I I' hζ n hn
      (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex) =
      (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex).map
        (⇑(lowerCharacterConjugation hG hi hν I I' hζ n hn) ∘ ⇑(eX)) :=
    Measure.map_map (map_continuous (lowerCharacterConjugation hG hi hν I I' hζ n hn)).measurable
      (map_continuous (eX)).measurable
  have h2 : ((rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral
      hindex).map (⇑(lowerCharacterConjugation hG hi hν I I' hζ n hn) ∘ ⇑(eX))).map
        (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn) =
      (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex).map
        (⇑(eX') ∘ ⇑(rationalUnitaryCharacterIso (Ψ))) :=
    (Measure.map_map
      (map_continuous (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn)).measurable
      ((map_continuous (lowerCharacterConjugation hG hi hν I I' hζ n hn)).measurable.comp
        (map_continuous (eX)).measurable)).trans
      (congrArg (fun f => Measure.map f
        (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex)) hcomp)
  have h3 : (rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral
      hindex).map (⇑(eX') ∘ ⇑(rationalUnitaryCharacterIso (Ψ))) =
      ((rationalUnitaryUnramifiedCharacterHaar s hs.isCentralSplitTorus.isCentral hindex).map
        (rationalUnitaryCharacterIso (Ψ))).map (eX') :=
    (Measure.map_map (map_continuous (eX')).measurable
      (map_continuous (rationalUnitaryCharacterIso (Ψ))).measurable).symm
  have h4 := map_rationalUnitaryUnramifiedCharacterHaar_iso (Ψ) s
    hs.isCentralSplitTorus.isCentral hindex
    (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs).isCentralSplitTorus.isCentral
    (finiteIndex_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
  exact ((congrArg (fun m => m.map (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn))
    h1).trans h2).trans (h3.trans (congrArg (fun m => m.map (eX')) h4))

/-! #### The orbits and orbit measures -/

set_option hygiene false in
local notation "sω" => discreteSeriesClass (sC) hsC (lowerMeasure hG hi hν I I' hζ n hn CM mu)
  (lowerRepresentation hG hi hν I I' hζ n hn π)
  (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn CM hCM mu π hsq)
set_option hygiene false in
local notation "ω'" => discreteSeriesClass CM' hCM' mu'
  (lowerChamberRepresentation hi I' ζ n hG hν I hζ hn π)
  (lowerChamberRepresentation_isSquareIntegrable hi I' ζ n hG hν I hζ hn s mu hs π hsq)

omit [IsAffine A.X.left] in
/-- The class of `π'` modulo `A_{M_{J''}}(F)` is the pullback of the class of `sπ` modulo `sC`
along `Z_{M'}(sζ)(F) = M_{J''}(F)`. -/
theorem pullback_lowerClass :
    DiscreteSeriesClass.pullback (e₁) (sC) hsC CM' hCM' (hAB)
        (lowerMeasure hG hi hν I I' hζ n hn CM mu) mu'
        (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu) (sω) = ω' :=
  rfl

/-- **The orbit `sO` of Task 7454 is the orbit of `π'`.** The orbit of `sπ` under
`Im X(s·M)` modulo `sC` for `sμ` is homeomorphic to the orbit of `π'` under `Im X(M_{J''})`
modulo `A_{M_{J''}}(F)` for `lowerChamberQuotientMeasure`, by `ω ↦ ω ∘ e₀⁻¹`
(`orbitTransport`). -/
def lowerChamberOrbitTransport :
    discreteSeriesOrbit (sC) hsC (lowerMeasure hG hi hν I I' hζ n hn CM mu)
        (leviNormCharacters χs) (sω) ≃ₜ
      discreteSeriesOrbit CM' hCM' mu' (leviRationalNormCharacters iL (c).chamber (c).labels)
        (ω') :=
  orbitTransport (e₁) (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn)
    (lowerChamberCharacterTransport_apply hi I' ζ n hG hν I hζ hn) (sC) hsC CM' hCM' (hAB)
    (lowerMeasure hG hi hν I I' hζ n hn CM mu) mu'
    (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu) (sω) (ω')
    (pullback_lowerClass hi I' ζ n hG hν I hζ hn s mu hs π hsq)

omit [IsAffine A.X.left] in
/-- On the orbit parameterization, `sπ ⊗ z ↦ π' ⊗ (z ∘ e₀⁻¹)`. -/
theorem lowerChamberOrbitTransport_orbitMap
    (z : unitaryUnramifiedCharacters (leviNormCharacters χs)) :
    lowerChamberOrbitTransport hi I' ζ n hG hν I hζ hn s mu hs π hsq
        (discreteSeriesOrbitMap (sC) hsC (lowerMeasure hG hi hν I I' hζ n hn CM mu)
          (leviNormCharacters χs) (sω) z) =
      discreteSeriesOrbitMap CM' hCM' mu' (leviRationalNormCharacters iL (c).chamber (c).labels)
        (ω') (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn z) :=
  orbitTransport_orbitMap (e₁) (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn)
    (lowerChamberCharacterTransport_apply hi I' ζ n hG hν I hζ hn) (sC) hsC CM' hCM' (hAB)
    (lowerMeasure hG hi hν I I' hζ n hn CM mu) mu'
    (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu) (sω) (ω')
    (pullback_lowerClass hi I' ζ n hG hν I hζ hn s mu hs π hsq) z

omit [IsAffine A.X.left] in
/-- The stabilizer of `π'` is finite when that of `sπ` is. -/
theorem finite_lowerChamberStabilizer
    [Finite (discreteSeriesStabilizer (sC) hsC (lowerMeasure hG hi hν I I' hζ n hn CM mu)
      (leviNormCharacters χs) (sω))] :
    Finite (discreteSeriesStabilizer CM' hCM' mu'
      (leviRationalNormCharacters iL (c).chamber (c).labels) (ω')) :=
  finite_discreteSeriesStabilizer (e₁) (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn)
    (lowerChamberCharacterTransport_apply hi I' ζ n hG hν I hζ hn) (sC) hsC CM' hCM' (hAB)
    (lowerMeasure hG hi hν I I' hζ n hn CM mu) mu'
    (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu) (sω) (ω')
    (pullback_lowerClass hi I' ζ n hG hν I hζ hn s mu hs π hsq)

set_option maxHeartbeats 1000000 in
/-- **The orbit measures correspond.** Task 7454's orbit measure on `sO` for the transported
character measure `lowerCharacterMeasure ρ_X`, with `ρ_X` the I.1 measure of `s`, is carried by
`lowerChamberOrbitTransport` to the orbit measure `dO'` of the source-normalized target at `M'`:
the orbit of `π'` modulo `A_{M_{J''}}(F)` for `lowerChamberQuotientMeasure` and the I.1 measure
of `s'`. -/
theorem map_lowerOrbitMeasure
    [Finite (discreteSeriesStabilizer (sC) hsC (lowerMeasure hG hi hν I I' hζ n hn CM mu)
      (leviNormCharacters χs) (sω))]
    [Finite (discreteSeriesStabilizer CM' hCM' mu'
      (leviRationalNormCharacters iL (c).chamber (c).labels) (ω'))] :
    (discreteSeriesOrbitMeasure (leviNormCharacters χs) (sC) hsC
        (lowerMeasure hG hi hν I I' hζ n hn CM mu) (sω)
        (lowerCharacterMeasure hG hi hν I I' hζ n hn
          (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex))).map
        (lowerChamberOrbitTransport hi I' ζ n hG hν I hζ hn s mu hs π hsq) =
      discreteSeriesOrbitMeasure (leviRationalNormCharacters iL (c).chamber (c).labels) CM' hCM'
        mu' (ω')
        (standardLeviUnitaryUnramifiedCharacterHaar (c).labels
          (lowerSplit hi I' ζ n hG hν I hζ hn s)
          (isSplitComponent_lowerSplit hi I' ζ n hG hν I hζ hn s hs)
          (finiteIndex_lowerSplit hi I' ζ n hG hν I hζ hn s hs)) :=
  (map_discreteSeriesOrbitMeasure_orbitTransport (e₁)
    (lowerChamberCharacterTransport hi I' ζ n hG hν I hζ hn)
    (lowerChamberCharacterTransport_apply hi I' ζ n hG hν I hζ hn) (sC) hsC CM' hCM' (hAB)
    (lowerMeasure hG hi hν I I' hζ n hn CM mu) mu'
    (lowerChamberQuotientMeasure_map hi I' ζ n hG hν I hζ hn s mu) (sω) (ω')
    (pullback_lowerClass hi I' ζ n hG hν I hζ hn s mu hs π hsq)
    (lowerCharacterMeasure hG hi hν I I' hζ n hn
      (standardLeviUnitaryUnramifiedCharacterHaar I s hs hindex))).trans
    (congrArg (discreteSeriesOrbitMeasure (leviRationalNormCharacters iL (c).chamber (c).labels)
      CM' hCM' mu' (ω')) (map_lowerCharacterMeasure hi I' ζ n hG hν I hζ hn s hs hindex))

end Lower

end Langlands.HarishChandraSchwartz.LowerSplitCenter
