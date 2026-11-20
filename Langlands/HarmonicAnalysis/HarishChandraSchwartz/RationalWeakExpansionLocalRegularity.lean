import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionTargets
import Langlands.Representation.Plancherel.DynamicOppositeUnitaryNonnegativity
import Langlands.Representation.Plancherel.RationalUnramifiedScalarCancellation

/-! # From pointwise to global unitary regularity of the weighted c-family

Waldspurger's proof of Corollary V.2.3 (printed p.294) shows that `c̃_{P'|P}(s, ·)` is regular at
each point `ω` of the orbit `O`. The published target `WeightedCRegularityStatement` asks for one
rational extension (`WeightedCExtension`) whose single denominator vanishes at no point of `O`.
This module bridges the two.

* Generic part (namespace `Langlands.Plancherel.UnramifiedOperatorFamily`):
  `IsRegularAtUnitary` (a presentation `N/d` of a family on the interior of a set `D₀` with
  `d(z) ≠ 0`) and `exists_unitaryRegular_of_local`: if the unitary characters form a compact
  space, presentations regular at each unitary point give one presentation regular at all of
  them, with denominator `Σ_j d_j† d_j`.
* Specialization: `WeightedCRegularAt` (regularity of `c̃_{P'|P}(s, ·)` at one unitary point),
  `nonempty_weightedCExtension_of_local`, the pointwise statement
  `WeightedCLocalRegularityStatement` (not proved here), and the proved reduction
  `WeightedCRegularityReductionStatement` (`weightedCRegularityReduction`). -/

noncomputable section

open scoped NNReal ComplexConjugate

universe uG uI uV uW

namespace Langlands.Plancherel

namespace UnramifiedOperatorFamily

variable {G : Type uG} [Group G] [TopologicalSpace G] {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A finite sum of polynomial operator families is polynomial. -/
theorem IsPolynomialOperatorOn.finset_sum {ι : Type*} (t : Finset ι)
    {U : Set (unramifiedCharacters ν)} {A : ι → U → V →ₗ[ℂ] W}
    (hA : ∀ j ∈ t, IsPolynomialOperatorOn U (A j)) :
    IsPolynomialOperatorOn U (fun χ => ∑ j ∈ t, A j χ) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using isPolynomialOperatorOn_const (U := U) (0 : V →ₗ[ℂ] W)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hA a (Finset.mem_insert_self a t)).add
      (ih fun j hj => hA j (Finset.mem_insert_of_mem hj))

/-- The inclusion `Im X → X` of the unitary unramified characters. -/
def unitaryInclusion (z : unitaryUnramifiedCharacters ν) : unramifiedCharacters ν :=
  ⟨z.val, z.property.1⟩

theorem continuous_unitaryInclusion : Continuous (unitaryInclusion (ν := ν)) :=
  continuous_subtype_val.subtype_mk _

/-- At a unitary point, `d† d` is the squared absolute value of `d`. -/
theorem unramifiedDagger_mul_self_unitary (d : unramifiedRegularFunctions ν)
    (z : unitaryUnramifiedCharacters ν) :
    (unramifiedDagger ν d * d).val (unitaryInclusion z) =
      ((Complex.normSq (d.val (unitaryInclusion z)) : ℝ) : ℂ) := by
  have hz : unramifiedConjInv ν (unitaryInclusion z) = unitaryInclusion z :=
    unramifiedConjInv_eq_self_of_mem_unitary ν (z := unitaryInclusion z) z.property
  rw [Complex.normSq_eq_conj_mul_self]
  change (unramifiedDagger ν d).val (unitaryInclusion z) * d.val (unitaryInclusion z) = _
  rw [unramifiedDagger_apply, hz]

/-- **Regularity of a family at a unitary point.** The family `A` of linear maps on a set `D₀`
of unramified characters has a presentation regular at the unitary character `z`: a regular
function `d` and a polynomial family `N` on all of `X` with `N(x) = d(x) A(x)` at every `x` in the
interior of `D₀`, and `d(z) ≠ 0`. -/
def IsRegularAtUnitary {D₀ : Set (unramifiedCharacters ν)} (A : D₀ → V →ₗ[ℂ] W)
    (z : unitaryUnramifiedCharacters ν) : Prop :=
  ∃ (d : unramifiedRegularFunctions ν) (N : unramifiedCharacters ν → V →ₗ[ℂ] W),
    IsPolynomialOperatorOn Set.univ (fun χ => N χ.val) ∧
    (∀ x (hx : x ∈ interior D₀), N x = d.val x • A ⟨x, interior_subset hx⟩) ∧
    d.val ⟨z.val, z.property.1⟩ ≠ 0

/-- **Pointwise unitary regularity gives one unitary-regular presentation.** If the unitary
characters form a compact space and, at every unitary point `z`, the family `A` on a set `D₀` has
a presentation `N_z = d_z • A` on the interior of `D₀`, with polynomial numerator `N_z` and
`d_z(z) ≠ 0`, then there is one presentation `N = d • A` on the interior of `D₀` with polynomial
numerator whose denominator vanishes at no unitary point. The denominator is `d = Σ_j d_j† d_j`
for finitely many `z_j` whose nonvanishing sets cover `Im X`; at a unitary point it equals
`Σ_j |d_j|² > 0`. -/
theorem exists_unitaryRegular_of_local [CompactSpace (unitaryUnramifiedCharacters ν)]
    {D₀ : Set (unramifiedCharacters ν)} (A : D₀ → V →ₗ[ℂ] W)
    (hloc : ∀ z : unitaryUnramifiedCharacters ν, IsRegularAtUnitary A z) :
    ∃ (d : unramifiedRegularFunctions ν) (N : unramifiedCharacters ν → V →ₗ[ℂ] W),
      IsPolynomialOperatorOn Set.univ (fun χ => N χ.val) ∧
      (∀ x (hx : x ∈ interior D₀), N x = d.val x • A ⟨x, interior_subset hx⟩) ∧
      ∀ z : unitaryUnramifiedCharacters ν, d.val ⟨z.val, z.property.1⟩ ≠ 0 := by
  choose d N hN hc hz using fun z => hloc z
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z => {w : unitaryUnramifiedCharacters ν | (d z).val (unitaryInclusion w) ≠ 0})
    (fun z => isOpen_ne_fun
      ((continuous_unramifiedRegularFunction ν (d z)).comp continuous_unitaryInclusion)
      continuous_const)
    (fun z _ => Set.mem_iUnion.2 ⟨z, hz z⟩)
  refine ⟨∑ j ∈ t, unramifiedDagger ν (d j) * d j,
    fun χ => ∑ j ∈ t, (unramifiedDagger ν (d j)).val χ • N j χ, ?_, ?_, ?_⟩
  · exact IsPolynomialOperatorOn.finset_sum t fun j _ => (hN j).regular_smul _
  · intro x hx
    simp only [hc _ x hx, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    simp
  · intro z
    have hval : (∑ j ∈ t, unramifiedDagger ν (d j) * d j).val (unitaryInclusion z) =
        ((∑ j ∈ t, Complex.normSq ((d j).val (unitaryInclusion z)) : ℝ) : ℂ) := by
      push_cast
      rw [← Finset.sum_congr rfl fun j _ => unramifiedDagger_mul_self_unitary (d j) z]
      simp
    change (∑ j ∈ t, unramifiedDagger ν (d j) * d j).val (unitaryInclusion z) ≠ 0
    rw [hval, Complex.ofReal_ne_zero]
    obtain ⟨j, hj, hjz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
    refine ne_of_gt (Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨j, hj, ?_⟩)
    exact Complex.normSq_pos.2 hjz

end UnramifiedOperatorFamily

end Langlands.Plancherel

/-! ## The weighted c-family -/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

namespace WeakExpansion

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance localRegularityAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance localRegularityLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance localRegularityLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance localRegularityLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

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

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

-- `M_I(F)` as a subtype of `G(F)`, written as in `rationalInducedSmoothOrbitSections`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "νM" => leviRationalNormCharacters i ν I
set_option hygiene false in
local notation "eM" => (leviRationalUnitaryCoordinates hG hi hν I).toMulEquiv

/-! ### Pointwise regularity of the weighted c-family -/

section Extension

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n

-- `M'`, written as `lowerAmbient` (the form of the lower cocharacter `χ_s`); every lower object
-- below is written in this form.
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn

set_option maxHeartbeats 1600000 in
/-- **`c̃_{P'|P}(s, ·)` is regular at the unitary character `z`** (Waldspurger V.2.3, printed
p.294, "régulière en `ω`"): there are a regular denominator `d` and a global polynomial numerator
`N` with `N(x) = d(x) c̃(s, π ⊗ x)` on the compact pictures at every `x` in the interior of the
domain `cWeightedDomain`, and `d(z) ≠ 0`. -/
def WeightedCRegularAt (z : unitaryUnramifiedCharacters νM) : Prop :=
  UnramifiedOperatorFamily.IsRegularAtUnitary
    (D₀ := cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)
    (fun x => weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN x) z

set_option maxHeartbeats 400000 in
/-- **Regularity at every unitary point gives a rational extension regular on the orbit.** If the
interior of the domain of `c̃_{P'|P}(s, ·)` is nonempty and `c̃_{P'|P}(s, ·)` is regular at every
unitary character (`WeightedCRegularAt`), then it has a rational extension `WeightedCExtension`
whose single denominator vanishes at no unitary character. -/
theorem nonempty_weightedCExtension_of_local
    (hint : (interior
      (cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)).Nonempty)
    (hloc : ∀ z : unitaryUnramifiedCharacters νM,
      WeightedCRegularAt hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN z) :
    Nonempty (WeightedCExtension hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN) := by
  have : CompactSpace (unitaryUnramifiedCharacters νM) :=
    (leviRationalUnitaryCoordinates hG hi hν I).toHomeomorph.symm.compactSpace
  obtain ⟨d, N, hpoly, hc, hreg⟩ := UnramifiedOperatorFamily.exists_unitaryRegular_of_local
    (D₀ := cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM)
    (fun x => weightedCompactFamily hG hi hν I I' hζ hζ' n hn K hK hRefl hCST hPK π PG PM hN x)
    hloc
  exact ⟨⟨hint, d, N, hpoly, hc, hreg⟩⟩

end Extension

/-! ### The pointwise regularity statement -/

section Targets

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "𝐋I" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐋" => lowerAmbient i ν (rootSet i ν I')
set_option hygiene false in
local notation "hM'" => lowerAmbient_isConnectedReductive hG hi hν I'

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine Tc.X.left]
  (sc : Tc.toGrp ⟶ 𝐋I) (hs : IsSplitComponent sc)
  (hindex : (RenardCartan.splitValuationImage sc).FiniteIndex)

set_option hygiene false in
local notation "CM" => rationalLeviSplitCenter I sc
set_option hygiene false in
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

variable [(CM).Normal] [(rationalPoints.map sc).range.Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ CM)] [BorelSpace (𝐌 ⧸ CM)]
  (mu : Measure (𝐌 ⧸ CM)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ T.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (rootSet i ν I') A qA)
  (R : Representatives i ν (rootSet i ν I) (rootSet i ν I'))
  (PM : ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    LowerDensityPackage hG hi hν I I' hζ (R.normalizer s) (R.levi_le s) π hRefl hCST)

set_option hygiene false in
local notation "nₛ" => R.normalizer
set_option hygiene false in
local notation "hnₛ" => R.levi_le

/-- **Pointwise regularity statement (Waldspurger, Corollary V.2.3, in the form proved on printed
p.294).** Under the premises of `WeightedCRegularityStatement`, for every `s ∈ W(M'|G|M)` the
interior of the domain of `c̃_{P'|P}(s, ·)` is nonempty and `c̃_{P'|P}(s, ·)` is regular at every
unitary character (`WeightedCRegularAt`). -/
def WeightedCLocalRegularityStatement : Prop :=
  IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu →
  (∃ α : SimpleRoot i ν, α ∉ I') →
  IsSpecialVertexCompact ν hi K →
  ∀ hN : SourceCompactNormalization hG hi hν I I' hζ (K := K) π hRefl hCST PG R PM,
  ∀ s : WeylIndex i ν (rootSet i ν I) (rootSet i ν I'),
    (interior (cWeightedDomain hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST π PG
      (PM s))).Nonempty ∧
    ∀ z : unitaryUnramifiedCharacters νM,
      WeightedCRegularAt hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST hPK π PG (PM s)
        (hN s) z

/-- **Reduction of Corollary V.2.3 to pointwise regularity**: the pointwise statement
`WeightedCLocalRegularityStatement` implies the regularity target `WeightedCRegularityStatement`,
for the same data. -/
def WeightedCRegularityReductionStatement : Prop :=
  WeightedCLocalRegularityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST PG R PM →
    WeightedCRegularityStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST PG R PM

omit [IsAffine Tc.X.left] [(rationalPoints.map sc).range.Normal] [BorelSpace (𝐌 ⧸ CM)] in
/-- Proof of `WeightedCRegularityReductionStatement`: apply
`nonempty_weightedCExtension_of_local` for each Weyl index `s`. -/
theorem weightedCRegularityReduction :
    WeightedCRegularityReductionStatement hG hi hν I I' hζ hζ' hKc hPK sc hs π mu hRefl hCST PG
      R PM := by
  intro h hsq hα hK hN s
  obtain ⟨hint, hloc⟩ := h hsq hα hK hN s
  exact nonempty_weightedCExtension_of_local hG hi hν I I' hζ hζ' (nₛ s) (hnₛ s) K hKc hRefl hCST
    hPK π PG (PM s) (hN s) hint hloc

end Targets

end WeakExpansion

end Langlands.HarishChandraSchwartz
