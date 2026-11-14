import Langlands.Representation.Plancherel.StandardLeviPlancherelWeight
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryInverseRegularity
import Langlands.Representation.Plancherel.RationalPlancherelConstantFinite

/-! # Positivity of the Plancherel weight on a dense open set

Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après Harish-Chandra)*,
J. Inst. Math. Jussieu 2 (2003), §V.2 (printed p. 292), defines the Plancherel density
`μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²` and states in Lemma V.2.1 (first item) that `μ(ω) ≥ 0` on the
orbit `O`. In §VII.2 (printed p. 319) the weighted product
`∫_O μ(ω) (ψ'[O,P]_ω, ψ[O,P]_ω) dω` is asserted to be positive definite. For that, `μ ≥ 0`
alone does not suffice; it does suffice if, in addition, `μ` is nonzero on a dense subset of
`O`. This module proves that from `j_P ≠ 0`.

The density `μ` may vanish at the unitary characters where `j_P` has a pole, so `μ` need not
be positive at every point of `O`. A continuous function `u ≥ 0` that is positive on a dense
open set still gives a definite weighted product for a measure charging every nonempty open
set: if `∫ u |q|² = 0` for continuous `q`, then `q` vanishes on the dense set `{u > 0}` and
hence everywhere.

## Main results

* `dense_rationalUnitaryValue_ne_zero`: a nonzero rational function on `X(M)` that is regular
  at every unitary character has a nonzero value on a dense subset of `Im X(M)`. The proof goes
  through circle coordinates: a numerator vanishing on a box of circle arcs is zero
  (`finiteLaurent_eq_zero_of_eval_on_box`).
* `dense_rationalUnitaryValue_pos`, `isOpen_rationalUnitaryValue_pos`: for a function whose
  unitary values are nonnegative reals, the positive set is dense and open.
* `dense_plancherelWeight_pos`, `isOpen_plancherelWeight_pos`: the same for the Plancherel
  weight `plancherelWeight` on `Im X(Z_G(ζ ∘ i))`, when `j_P ≠ 0`, the product
  `∏_α γ(M_α|M)` is finite, and `j_P⁻¹` is regular with nonnegative real values on the
  unitary characters.
* `standardLeviCharacterRestrictHomeomorph`: restriction along `Z_G(ζ ∘ i) ≅ M_I` is a
  homeomorphism `Im X(M_I) ≃ₜ Im X(Z_G(ζ ∘ i))`.
* `dense_standardLeviPlancherelWeight_pos`: the orbit Plancherel weight
  `standardLeviPlancherelWeight` is a positive real number on a dense subset of the orbit `O`
  of a square-integrable representation of the standard Levi `M_I(F)`, when `j_P ≠ 0` and
  `j_P⁻¹` is regular with nonnegative real values on the unitary characters. Here `i` is a
  maximal split torus, so `∏_α γ(M_α|M)` is finite
  (`rankOneGammaProduct_ne_top_of_isMaximalSplitTorus`) and is not a hypothesis.
* `standardLeviPlancherelWeightReal`: the real part of that weight. It is continuous and
  bounded above. Under the nonnegativity hypothesis it is nonnegative. If moreover
  `j_P ≠ 0`, its positive set is dense and open in `O`.

The hypotheses `j_P ≠ 0`, regularity of `j_P⁻¹` on the unitary characters and nonnegativity
of its unitary values are inputs here, not proved. So is finiteness of `∏_α γ(M_α|M)` in the
section on `Im X(Z_G(ζ ∘ i))`, where the torus is arbitrary.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

/-! ### Positive real numbers -/

/-- A nonzero complex number that is a nonnegative real number is a positive real number. -/
theorem exists_pos_real_of_nonneg_of_ne_zero {w : ℂ} (h : ∃ r : ℝ, 0 ≤ r ∧ w = (r : ℂ))
    (h0 : w ≠ 0) : ∃ r : ℝ, 0 < r ∧ w = (r : ℂ) := by
  obtain ⟨r, hr, rfl⟩ := h
  refine ⟨r, lt_of_le_of_ne hr ?_, rfl⟩
  rintro rfl
  exact h0 Complex.ofReal_zero

/-- For a complex number that is a nonnegative real number, being a positive real number is
the same as being nonzero. -/
theorem exists_pos_real_iff_ne_zero {w : ℂ} (h : ∃ r : ℝ, 0 ≤ r ∧ w = (r : ℂ)) :
    (∃ r : ℝ, 0 < r ∧ w = (r : ℂ)) ↔ w ≠ 0 := by
  refine ⟨?_, exists_pos_real_of_nonneg_of_ne_zero h⟩
  rintro ⟨r, hr, rfl⟩
  exact Complex.ofReal_ne_zero.mpr hr.ne'

/-! ### Nonvanishing of values on a dense open set -/

section Generic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : GroupScheme.IsConnectedReductive G)

local instance plancherelWeightPositivityPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

set_option hygiene false in
local notation "RG" => unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "UG" =>
  unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)

set_option hygiene false in
local notation "KG" =>
  rationalUnramifiedFunctionField G (continuous_rationalValuationImageProjection G) hG

set_option hygiene false in
local notation "hpG" => continuous_rationalValuationImageProjection G

set_option hygiene false in
local notation "Φ" => rationalCanonicalUnitaryUnramifiedCharacterCoordinates G hG

set_option hygiene false in
local notation "ΛG" => rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG

/-- The set of unitary characters where the value function of `f` does not vanish is open. -/
theorem isOpen_rationalUnitaryValue_ne_zero {f : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) :
    IsOpen {z : UG | rationalUnitaryValue G hG f hf z ≠ 0} :=
  isOpen_compl_singleton.preimage (continuous_rationalUnitaryValue G hG hf)

/-- **Nonvanishing on a dense set.** A nonzero rational function regular at every unitary
character has a nonzero value on a dense subset of the unitary characters. If its value
vanished on a nonempty open set, then in circle coordinates the numerator of a presentation
regular at one of its points would vanish on a box of circle arcs, so it would be zero. -/
theorem dense_rationalUnitaryValue_ne_zero {f : KG}
    (hf : RationalFunctionUnitaryRegular G hG f) (hf0 : f ≠ 0) :
    Dense {z : UG | rationalUnitaryValue G hG f hf z ≠ 0} := by
  rw [dense_iff_inter_open]
  rintro U hU ⟨z0, hz0⟩
  by_contra hempty
  have hzero : ∀ z ∈ U, rationalUnitaryValue G hG f hf z = 0 := by
    intro z hz
    by_contra h
    exact hempty ⟨z, hz, h⟩
  obtain ⟨m, n, hn, hfmn⟩ := hf z0
  have hev := regular_val_unitaryToUnramified_coordinates_symm G hG
  have hc0 : (Φ).symm ((Φ) z0) = z0 := (Φ).symm_apply_apply z0
  have hnc0 : finiteLaurentEvaluation (fun i => Circle.toUnits ((Φ) z0 i)) ((ΛG).symm n) ≠ 0 := by
    rw [← hev, hc0]
    exact hn
  have hV : {c | finiteLaurentEvaluation (fun i => Circle.toUnits (c i)) ((ΛG).symm n) ≠ 0 ∧
      (Φ).symm c ∈ U} ∈ 𝓝 ((Φ) z0) := by
    refine inter_mem ?_ ?_
    · exact (continuous_finiteLaurentEvaluation_circle _).continuousAt.eventually_ne hnc0
    · exact (Φ).symm.continuous.continuousAt.preimage_mem_nhds
        (hU.mem_nhds (hc0.symm ▸ hz0))
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, t, ht, hsub⟩ := hV
  have hm0 : (ΛG).symm m = 0 := by
    refine finiteLaurent_eq_zero_of_eval_on_box _ (fun i => Circle.toUnits '' t i)
      (fun i => (circle_infinite_of_mem_nhds (ht i)).image
        (fun x _ y _ h => Circle.coe_injective (congrArg Units.val h))) _ ?_
    intro c hc
    choose t' ht' hct' using fun i => hc i (Set.mem_univ i)
    have hct : c = fun i => Circle.toUnits (t' i) := funext fun i => (hct' i).symm
    rw [hct]
    obtain ⟨hnt, hU'⟩ := hsub (fun i _ => ht' i)
    have hv := hzero _ hU'
    have hnt' : n.val (unitaryToUnramified G ((Φ).symm t')) ≠ 0 := by
      rw [hev]
      exact hnt
    rw [rationalUnitaryValue_eq G hG hf _ hnt' hfmn, div_eq_zero_iff] at hv
    rw [← hev]
    exact hv.resolve_right hnt'
  have hm : m = 0 := (ΛG).symm.injective (by rw [hm0, map_zero])
  apply hf0
  rw [hfmn, hm, map_zero, zero_div]

/-- If `f` has a nonnegative real value at the unitary character `z`, its value there is a
positive real number exactly when it is nonzero. -/
theorem rationalUnitaryValue_pos_iff {f : KG} (hf : RationalFunctionUnitaryRegular G hG f)
    {z : UG} (hz : RationalFunctionNonnegAt G hpG hG f (unitaryToUnramified G z)) :
    (∃ r : ℝ, 0 < r ∧ rationalUnitaryValue G hG f hf z = (r : ℂ)) ↔
      rationalUnitaryValue G hG f hf z ≠ 0 :=
  exists_pos_real_iff_ne_zero (rationalUnitaryValue_nonneg G hG hf hz)

/-- **Positivity on a dense open set.** A nonzero rational function with a nonnegative real
value at every unitary character has a positive real value on a dense open set of unitary
characters. -/
theorem dense_rationalUnitaryValue_pos {f : KG} (hf : RationalFunctionUnitaryRegular G hG f)
    (hf0 : f ≠ 0) (hnn : ∀ z : UG, RationalFunctionNonnegAt G hpG hG f (unitaryToUnramified G z)) :
    Dense {z : UG | ∃ r : ℝ, 0 < r ∧ rationalUnitaryValue G hG f hf z = (r : ℂ)} :=
  (dense_rationalUnitaryValue_ne_zero G hG hf hf0).mono fun z hz =>
    (rationalUnitaryValue_pos_iff G hG hf (hnn z)).mpr hz

/-- Under the same nonnegativity hypothesis, the set where the value is a positive real number
is open. -/
theorem isOpen_rationalUnitaryValue_pos {f : KG} (hf : RationalFunctionUnitaryRegular G hG f)
    (hnn : ∀ z : UG, RationalFunctionNonnegAt G hpG hG f (unitaryToUnramified G z)) :
    IsOpen {z : UG | ∃ r : ℝ, 0 < r ∧ rationalUnitaryValue G hG f hf z = (r : ℂ)} := by
  have h : {z : UG | ∃ r : ℝ, 0 < r ∧ rationalUnitaryValue G hG f hf z = (r : ℂ)} =
      {z : UG | rationalUnitaryValue G hG f hf z ≠ 0} :=
    Set.ext fun z => rationalUnitaryValue_pos_iff G hG hf (hnn z)
  rw [h]
  exact isOpen_rationalUnitaryValue_ne_zero G hG hf

end Generic

/-! ### The Plancherel weight on the unitary characters -/

section Weight

open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource
open RationalPlancherelDensity

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
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme (CommGroupScheme.groupHom ζ ≫ i)) ψ).toMul)

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK A)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK A)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK A)
  (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK A)
  {D : Set (unramifiedCharacters νL)}
  (hne : D.Nonempty)
  (hi : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) A).IsIrreducible)

set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK A
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hi

set_option hygiene false in
local notation "μP" => plancherelDensity i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
  hDForwardΩ hneReverse hDReverseΩ hne hi

set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG

set_option hygiene false in
local notation "wP" => plancherelWeight i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
  hDForwardΩ hneReverse hDReverseΩ hne hi

/-- For a finite product `∏_α γ(M_α|M)`, the density `μ` is nonzero when `j_P` is. -/
theorem plancherelDensity_ne_zero (hj : jP ≠ 0)
    (hfin : rankOneGammaProduct i ζ K hK ≠ ⊤) : μP ≠ 0 := fun h =>
  hj ((plancherelDensity_eq_zero_iff i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
    hDForwardΩ hneReverse hDReverseΩ hne hi hfin).mp h)

/-- The set of unitary characters where the Plancherel weight does not vanish is open. -/
theorem isOpen_plancherelWeight_ne_zero (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    IsOpen {z : UL | wP hreg z ≠ 0} :=
  isOpen_rationalUnitaryValue_ne_zero MS hMS _

/-- **Nonvanishing on a dense set.** If `j_P ≠ 0` and the product `∏_α γ(M_α|M)` is finite,
the Plancherel weight is nonzero on a dense subset of the unitary characters. -/
theorem dense_plancherelWeight_ne_zero (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hj : jP ≠ 0) (hfin : rankOneGammaProduct i ζ K hK ≠ ⊤) :
    Dense {z : UL | wP hreg z ≠ 0} :=
  dense_rationalUnitaryValue_ne_zero MS hMS _
    (plancherelDensity_ne_zero i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
      hneReverse hDReverseΩ hne hi hj hfin)

/-- Where `j_P⁻¹` has a nonnegative real value, the Plancherel weight is a positive real number
exactly when it is nonzero. -/
theorem plancherelWeight_pos_iff (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    {z : UL} (hz : RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    (∃ r : ℝ, 0 < r ∧ wP hreg z = (r : ℂ)) ↔ wP hreg z ≠ 0 :=
  exists_pos_real_iff_ne_zero
    (plancherelWeight_nonneg i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
      hneReverse hDReverseΩ hne hi hreg hz)

/-- **Positivity on a dense open set** (Lemma V.2.1, first item, strengthened on a dense set).
If `j_P ≠ 0`, the product `∏_α γ(M_α|M)` is finite and `j_P⁻¹` has a nonnegative real value at
every unitary character, then the Plancherel weight is a positive real number on a dense subset
of the unitary characters. -/
theorem dense_plancherelWeight_pos (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hj : jP ≠ 0) (hfin : rankOneGammaProduct i ζ K hK ≠ ⊤)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    Dense {z : UL | ∃ r : ℝ, 0 < r ∧ wP hreg z = (r : ℂ)} :=
  (dense_plancherelWeight_ne_zero i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
    hneReverse hDReverseΩ hne hi hreg hj hfin).mono fun z hz =>
      (plancherelWeight_pos_iff i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward hDForwardΩ
        hneReverse hDReverseΩ hne hi hreg (hnn z)).mpr hz

/-- Under the same nonnegativity hypothesis, the set where the Plancherel weight is a positive
real number is open. -/
theorem isOpen_plancherelWeight_pos (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    IsOpen {z : UL | ∃ r : ℝ, 0 < r ∧ wP hreg z = (r : ℂ)} := by
  have h : {z : UL | ∃ r : ℝ, 0 < r ∧ wP hreg z = (r : ℂ)} = {z : UL | wP hreg z ≠ 0} :=
    Set.ext fun z => plancherelWeight_pos_iff i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
      hDForwardΩ hneReverse hDReverseΩ hne hi hreg (hnn z)
  rw [h]
  exact isOpen_plancherelWeight_ne_zero i ζ hRefl hCST hG K hK hPK hOppK A p q hneForward
    hDForwardΩ hneReverse hDReverseΩ hne hi hreg

end Weight

section Orbit

open MeasureTheory
open Aubert.General UnramifiedOperatorFamily
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalDynamicSource
open RationalPlancherelDensity
open HarishChandraSchwartz
  (leviRationalUnitaryCoordinates leviRationalUnitaryCoordinates_hasLaurent)

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
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

local instance plancherelWeightPositivityLeviClosed
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsClosedImmersion (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left :=
  Standard.isClosedSubgroup_leviHom i ν (RationalPointFamily.rootSet i ν I)
local instance plancherelWeightPositivityLeviAffine
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    IsAffine (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X.left :=
  isAffine_of_isAffineHom (Standard.leviHom i ν (RationalPointFamily.rootSet i ν I)).hom.hom.left
local instance plancherelWeightPositivityLeviTopology
    (I : Finset (RationalPointFamily.SimpleRoot i ν)) :
    TopologicalSpace
      (rationalPoints (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I))) :=
  rationalPointTopology F (Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)).X

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν I) ζ)

set_option hygiene false in
local notation "χ" => CommGroupScheme.groupHom ζ ≫ i
set_option hygiene false in
local notation "MS" => parameterScheme (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "MI" => Standard.leviScheme i ν (RationalPointFamily.rootSet i ν I)
set_option hygiene false in
local notation "νL" => normCharacters (CommGroupScheme.groupHom ζ ≫ i)
set_option hygiene false in
local notation "UL" => unitaryUnramifiedCharacters
  (fun ψ => (rationalNormCharacters (parameterScheme (CommGroupScheme.groupHom ζ ≫ i)) ψ).toMul)
set_option hygiene false in
local notation "UMI" =>
  unitaryUnramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I)
set_option hygiene false in
local notation "hMS" => parameterScheme_isConnectedReductive (CommGroupScheme.groupHom ζ ≫ i) hG
-- `M_I(F)` as a subtype of `G(F)`, written as in the wave-packet consumers.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

omit [LocallyOfFiniteType G.X.hom] in
/-- Restriction along the inverse of `Z_G(ζ ∘ i) ≅ M_I` undoes restriction along the
isomorphism, on unitary unramified characters of `M_I`. -/
theorem rationalUnitaryUnramifiedCharacterRestrict_inv_hom
    (y : unitaryUnramifiedCharacters (fun ψ => (rationalNormCharacters MI ψ).toMul)) :
    rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).inv
        (rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).hom
          y) = y := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro g
  change y.val ((g ≫ (standardLeviParameterIso hG hi hν I hζ).inv.hom.hom) ≫
      (standardLeviParameterIso hG hi hν I hζ).hom.hom.hom) = y.val g
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

omit [LocallyOfFiniteType G.X.hom] in
/-- Restriction along `Z_G(ζ ∘ i) ≅ M_I` undoes restriction along its inverse, on unitary
unramified characters of `Z_G(ζ ∘ i)`. -/
theorem rationalUnitaryUnramifiedCharacterRestrict_hom_inv (w : UL) :
    rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).hom
        (rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).inv
          w) = w := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro m
  change w.val ((m ≫ (standardLeviParameterIso hG hi hν I hζ).hom.hom.hom) ≫
      (standardLeviParameterIso hG hi hν I hζ).inv.hom.hom) = w.val m
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id]

/-- **The restriction `z ↦ z ∘ e` is a homeomorphism** `Im X(M_I) ≃ Im X(Z_G(ζ ∘ i))`. Its inverse
is restriction along the inverse identification. -/
def standardLeviCharacterRestrictHomeomorph : UMI ≃ₜ UL where
  toFun := standardLeviCharacterRestrict hG hi hν I hζ
  invFun w := HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
    (RationalPointFamily.leviRationalPointHomeomorph i ν I)
    (fun ψ => (rationalNormCharacters MI ψ).toMul)
    (rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).inv w)
  left_inv z := by
    change HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
        (RationalPointFamily.leviRationalPointHomeomorph i ν I)
        (fun ψ => (rationalNormCharacters MI ψ).toMul)
        (rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).inv
          (rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).hom
            ((HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
              (RationalPointFamily.leviRationalPointHomeomorph i ν I)
              (fun ψ => (rationalNormCharacters MI ψ).toMul)).symm z))) = z
    rw [rationalUnitaryUnramifiedCharacterRestrict_inv_hom]
    exact (HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
      (RationalPointFamily.leviRationalPointHomeomorph i ν I)
      (fun ψ => (rationalNormCharacters MI ψ).toMul)).apply_symm_apply z
  right_inv w := by
    change rationalUnitaryUnramifiedCharacterRestrict (standardLeviParameterIso hG hi hν I hζ).hom
        ((HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
          (RationalPointFamily.leviRationalPointHomeomorph i ν I)
          (fun ψ => (rationalNormCharacters MI ψ).toMul)).symm
          (HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
            (RationalPointFamily.leviRationalPointHomeomorph i ν I)
            (fun ψ => (rationalNormCharacters MI ψ).toMul)
            (rationalUnitaryUnramifiedCharacterRestrict
              (standardLeviParameterIso hG hi hν I hζ).inv w))) = w
    rw [ContinuousMulEquiv.symm_apply_apply, rationalUnitaryUnramifiedCharacterRestrict_hom_inv]
  continuous_toFun := (standardLeviCharacterRestrict hG hi hν I hζ).continuous
  continuous_invFun :=
    (HarishChandraSchwartz.unitaryUnramifiedCharactersHomeomorph
      (RationalPointFamily.leviRationalPointHomeomorph i ν I)
      (fun ψ => (rationalNormCharacters MI ψ).toMul)).continuous.comp
      (rationalUnitaryUnramifiedCharacterRestrict
        (standardLeviParameterIso hG hi hν I hζ).inv).continuous

omit [LocallyOfFiniteType G.X.hom] in
/-- The homeomorphism is the restriction `z ↦ z ∘ e`. -/
@[simp] theorem standardLeviCharacterRestrictHomeomorph_apply (z : UMI) :
    standardLeviCharacterRestrictHomeomorph hG hi hν I hζ z =
      standardLeviCharacterRestrict hG hi hν I hζ z := rfl

/-! ### Positivity of the Plancherel weight on the orbit -/

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)

-- The inducing representation `π ∘ e` of `Z_G(ζ ∘ i)(F)`.
set_option hygiene false in
local notation "Aπ" => SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj
-- The orbit `O = {π ⊗ z ; z ∈ Im X(M_I)}` of the class of `π`.
set_option hygiene false in
local notation "Oπ" => discreteSeriesOrbit C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)
set_option hygiene false in
local notation "orbitMapπ" => discreteSeriesOrbitMap C hC mu
  (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)

variable
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hPK : ∀ g : RationalPoint F G.X,
    ∃ p : parabolic χ, ∃ k : K, g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (hOppK : ∀ g : RationalPoint F G.X,
    ∃ p : oppositeParabolic χ, ∃ k : K,
      g = (p : RationalPoint F G.X) * (k : RationalPoint F G.X))
  (p : ForwardContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  (q : ReverseContinuation χ hRefl hCST hG K hK hPK hOppK Aπ)
  {DForward DReverse : Set (unramifiedCharacters νL)}
  (hDForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hDForwardΩ : DForward ⊆ forwardFullDomainRegion χ K hK Aπ)
  (hDReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hDReverseΩ : DReverse ⊆ reverseFullDomainRegion χ K hK Aπ)
  {D : Set (unramifiedCharacters νL)}
  (hD : IsOpen D) (hne : D.Nonempty)
  (hirr : ∀ z ∈ D,
    (UnramifiedLeviInduction (decomposition χ) (radical_isClosed χ)
      (leviNormCharacters χ) (parameterTransport χ z) Aπ).IsIrreducible)

-- The canonical scalar `j_P` of the inducing representation `π ∘ e`.
set_option hygiene false in
local notation "jP" => conditionalCanonicalRationalScalar χ hRefl hCST hG K hK hPK hOppK Aπ
  p q hneForward hDForwardΩ hneReverse hDReverseΩ hne hirr

-- The Plancherel weight on the orbit `O`.
set_option hygiene false in
local notation "wO" => standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK
  hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr

include hG hi in
/-- For the maximal split torus `i`, the product `∏_α γ(M_α|M)` is finite
(`rankOneGammaProduct_ne_top_of_isSplitTorus`). -/
theorem rankOneGammaProduct_ne_top_of_isMaximalSplitTorus :
    rankOneGammaProduct i ζ K hK ≠ ⊤ := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  exact rankOneGammaProduct_ne_top_of_isSplitTorus i ζ K hK hi.1.1

/-- The set of points of the orbit `O` where the Plancherel weight does not vanish is open. -/
theorem isOpen_standardLeviPlancherelWeight_ne_zero
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    IsOpen {x : Oπ | wO hreg x ≠ 0} :=
  isOpen_compl_singleton.preimage
    (continuous_standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)

/-- **Nonvanishing on a dense subset of the orbit.** If `j_P ≠ 0`, the Plancherel weight is
nonzero on a dense subset of `O`. -/
theorem dense_standardLeviPlancherelWeight_ne_zero
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (hj : jP ≠ 0) :
    Dense {x : Oπ | wO hreg x ≠ 0} := by
  rw [← (isOpenQuotientMap_discreteSeriesOrbitMap C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I)
    (discreteSeriesClass C hC mu π hsq)).dense_preimage_iff]
  have h := (dense_plancherelWeight_ne_zero i ζ hRefl hCST hG K hK hPK hOppK Aπ p q hneForward
    hDForwardΩ hneReverse hDReverseΩ hne hirr hreg hj
    (rankOneGammaProduct_ne_top_of_isMaximalSplitTorus hG hi K hK)).preimage
    (standardLeviCharacterRestrictHomeomorph hG hi hν I hζ).isOpenMap
  refine h.mono fun z hz => ?_
  change wO hreg (orbitMapπ z) ≠ 0
  rw [standardLeviPlancherelWeight_orbitMap]
  exact hz

/-- **Positivity on a dense subset of the orbit.** If `j_P ≠ 0` and `j_P⁻¹` has a nonnegative
real value at every unitary character, then the Plancherel weight is a positive real number on
a dense subset of `O`. -/
theorem dense_standardLeviPlancherelWeight_pos
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (hj : jP ≠ 0)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    Dense {x : Oπ | ∃ r : ℝ, 0 < r ∧ wO hreg x = (r : ℂ)} :=
  (dense_standardLeviPlancherelWeight_ne_zero hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
    hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
    hj).mono fun x hx =>
      exists_pos_real_of_nonneg_of_ne_zero
        (standardLeviPlancherelWeight_nonneg_of_forall hG hi hν I hζ π C hC mu hsq hRefl hCST K
          hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD
          hne hirr hreg hnn x) hx

/-! ### The real Plancherel weight on the orbit -/

/-- **The real Plancherel weight** on the orbit `O`: the real part of
`standardLeviPlancherelWeight`. When `j_P⁻¹` has a nonnegative real value at every unitary
character, the Plancherel weight is real (`ofReal_standardLeviPlancherelWeightReal`), so
nothing is lost. This is the form of a weight `u : O → ℝ` taken by the weighted products on
`C^∞(O, P)`. -/
def standardLeviPlancherelWeightReal (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    Oπ → ℝ :=
  fun x => (wO hreg x).re

/-- The real Plancherel weight is continuous. -/
theorem continuous_standardLeviPlancherelWeightReal
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    Continuous (standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
      hreg) :=
  Complex.continuous_re.comp
    (continuous_standardLeviPlancherelWeight hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)

/-- If `j_P⁻¹` has a nonnegative real value at every unitary character, the real Plancherel
weight recovers the Plancherel weight. -/
theorem ofReal_standardLeviPlancherelWeightReal
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) (x : Oπ) :
    (standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK p q
      hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg x : ℂ) =
      wO hreg x := by
  obtain ⟨r, -, hr⟩ := standardLeviPlancherelWeight_nonneg_of_forall hG hi hν I hζ π C hC mu hsq
    hRefl hCST K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse
    hDReverseΩ hD hne hirr hreg hnn x
  unfold standardLeviPlancherelWeightReal
  rw [hr, Complex.ofReal_re]

/-- **Nonnegativity.** If `j_P⁻¹` has a nonnegative real value at every unitary character, the
real Plancherel weight is nonnegative on `O` (Lemma V.2.1, first item). -/
theorem standardLeviPlancherelWeightReal_nonneg
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) (x : Oπ) :
    0 ≤ standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK hOppK
      p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg x := by
  obtain ⟨r, hr0, hr⟩ := standardLeviPlancherelWeight_nonneg_of_forall hG hi hν I hζ π C hC mu
    hsq hRefl hCST K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse
    hDReverseΩ hD hne hirr hreg hnn x
  unfold standardLeviPlancherelWeightReal
  rw [hr, Complex.ofReal_re]
  exact hr0

/-- **Boundedness.** The real Plancherel weight is bounded above on the compact orbit `O`. -/
theorem exists_standardLeviPlancherelWeightReal_le
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    ∃ b : ℝ, ∀ x : Oπ, standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K
      hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
      hreg x ≤ b := by
  have : CompactSpace UMI :=
    (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
  have := compactSpace_discreteSeriesOrbit C hC mu
    (RationalPointFamily.leviRationalNormCharacters i ν I) (discreteSeriesClass C hC mu π hsq)
  obtain ⟨b, hb⟩ := (isCompact_range (continuous_standardLeviPlancherelWeightReal hG hi hν I hζ
    π C hC mu hsq hRefl hCST K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse
    hneReverse hDReverseΩ hD hne hirr hreg)).bddAbove
  exact ⟨b, fun x => hb ⟨x, rfl⟩⟩

/-- The set of points of `O` where the real Plancherel weight is positive is open. -/
theorem isOpen_standardLeviPlancherelWeightReal_pos
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) :
    IsOpen {x : Oπ | 0 < standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST
      K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne
      hirr hreg x} :=
  isOpen_lt continuous_const
    (continuous_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
      hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg)

/-- **Positivity on a dense subset of the orbit.** If `j_P ≠ 0` and `j_P⁻¹` has a nonnegative
real value at every unitary character, the real Plancherel weight is positive on a dense subset
of `O`; this set is open by `isOpen_standardLeviPlancherelWeightReal_pos`. -/
theorem dense_standardLeviPlancherelWeightReal_pos
    (hreg : RationalFunctionUnitaryRegular MS hMS (jP)⁻¹) (hj : jP ≠ 0)
    (hnn : ∀ z : UL, RationalFunctionNonnegAt MS (parameterProjection_continuous χ) hMS (jP)⁻¹
      (unitaryToUnramified MS z)) :
    Dense {x : Oπ | 0 < standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST
      K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne
      hirr hreg x} :=
  (dense_standardLeviPlancherelWeight_ne_zero hG hi hν I hζ π C hC mu hsq hRefl hCST K hK hPK
    hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr hreg
    hj).mono fun x hx => by
      refine lt_of_le_of_ne (standardLeviPlancherelWeightReal_nonneg hG hi hν I hζ π C hC mu hsq
        hRefl hCST K hK hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse
        hDReverseΩ hD hne hirr hreg hnn x) fun h => hx ?_
      rw [← ofReal_standardLeviPlancherelWeightReal hG hi hν I hζ π C hC mu hsq hRefl hCST K hK
        hPK hOppK p q hDForward hneForward hDForwardΩ hDReverse hneReverse hDReverseΩ hD hne hirr
        hreg hnn x, ← h, Complex.ofReal_zero]

end Orbit

end Langlands.Plancherel
