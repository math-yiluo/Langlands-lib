import Langlands.Group.GL.SingletonBlocks
import Langlands.Correspondence.RankOneExistence
import Langlands.Representation.Unramified.PrincipalSeries
import Langlands.Representation.Classification.SegmentSocleProductIrreducibilityProof
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.Classification.SquareIntegrableSegmentNonlinkageProof
import Langlands.Representation.Classification.BlockTensorTemperedProof
import Langlands.Representation.Classification.TemperedInductionPreservationProof
import Langlands.Representation.Classification.LeviDiscreteSeriesTemperedProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadReduction

/-! # Unitary unramified principal series as tempered blocks -/

noncomputable section

open CategoryTheory

namespace Langlands.Unramified

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- `GL_1` is commutative. -/
theorem generalLinear_one_mul_comm {R : Type*} [CommRing R] (g h : GeneralLinear 1 R) :
    g * h = h * g := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  simp [Matrix.mul_apply, mul_comm]

/-- The quotient of `GL_1` by its center has one point. -/
theorem subsingleton_centralQuotient_one (R : Type*) [CommRing R] :
    Subsingleton (GeneralLinear 1 R ⧸ Subgroup.center (GeneralLinear 1 R)) := by
  constructor
  intro a b
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [QuotientGroup.eq]
  exact Subgroup.mem_center_iff.mpr fun g => generalLinear_one_mul_comm g _

/-- An admissible representation of `GL_1` acting by a unitary character with
open kernel is square-integrable modulo the center: the central quotient is a
point. -/
theorem isSquareIntegrable_of_unitaryScalar (T : F.TopologicalData)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear 1 F.Carrier) V)
    (hadm : letI := T.topology; IsAdmissible ρ)
    (χ : GeneralLinear 1 F.Carrier →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set (GeneralLinear 1 F.Carrier)))
    (hnorm : ∀ g, ‖(χ g : ℂ)‖ = 1) (hact : ∀ g v, ρ g v = (χ g : ℂ) • v) :
    T.IsSquareIntegrable ρ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup 1
  let := T.centralQuotientMeasurableSpace 1
  have := T.centralQuotientBorelSpace 1
  intro μ _
  refine ⟨hadm, ?_⟩
  let c : UnitaryCentralCharacter ρ :=
    { character := χ.comp (Subgroup.center (GeneralLinear 1 F.Carrier)).subtype
      isOpen_ker := hχ.preimage continuous_subtype_val
      norm_eq_one := fun z => hnorm z
      acts := fun z v => hact z v }
  refine ⟨c, fun ℓ v => ?_⟩
  have := subsingleton_centralQuotient_one F.Carrier
  have : CompactSpace
      (GeneralLinear 1 F.Carrier ⧸ Subgroup.center (GeneralLinear 1 F.Carrier)) :=
    Finite.compactSpace
  have hconst : c.coefficientNorm ℓ v = fun _ => c.coefficientNorm ℓ v 1 :=
    funext fun q => congrArg _ (Subsingleton.elim q 1)
  rw [hconst]
  exact MeasureTheory.memLp_const _

/-- Square-integrability modulo the center implies temperedness. -/
theorem isTempered_of_isSquareIntegrable (T : F.TopologicalData) {n : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} (h : T.IsSquareIntegrable ρ) :
    T.IsTempered ρ := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  intro μ _
  exact isTemperedModCenter_of_squareIntegrable μ (h μ)

/-- Exact rank transport preserves square-integrability. -/
theorem isSquareIntegrable_castRank (T : F.TopologicalData) {r s : ℕ} (h : r = s)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hA : letI := T.topology; T.IsSquareIntegrable A.representation) :
    letI := T.topology
    T.IsSquareIntegrable (T.castRank h A).representation := by
  subst s
  exact hA

/-- A one-term segment's supercuspidal representative is the strong head of
its segment induction. -/
theorem singletonSegment_isSegmentHead (T : F.TopologicalData)
    (ρ : T.CuspidalDatum.{uF, uF})
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, uF} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) :
    T.IsSegmentHead (T.singletonSegment ρ)
      (T.castRank (T.singletonSegment_degree ρ).symm A.obj) := by
  let := T.topology
  let e := T.singletonSegmentInducedEquiv ρ.rank_pos A.obj
  have hB := T.isIrreducible_castRank (T.singletonSegment_degree ρ).symm A.obj A.property.1
  exact ⟨A, hA, (Classification.isIrreducibleHead_self _ hB).of_equiv e.symm⟩

section Canonical

local instance unitaryBlocksFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance unitaryBlocksGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance unitaryBlocksGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- The rank-one supercuspidal object of a norm-one unramified character is
square-integrable modulo the center. -/
theorem rankOneUnitary_isSquareIntegrable (w : ℂˣ) (hw : ‖(w : ℂ)‖ = 1) :
    F.canonicalTopologicalData.IsSquareIntegrable
      (Correspondence.rankOneSupercuspidalObject.{uF, uV} F
        (character F w)).obj.representation := by
  let T := F.canonicalTopologicalData
  refine isSquareIntegrable_of_unitaryScalar F T _
    (Correspondence.rankOneSupercuspidalObject.{uF, uV} F (character F w)).property.2.1
    (T.determinantUnramifiedCharacter 1 w)
    (T.isOpen_ker_determinantUnramifiedCharacter 1 w) ?_ ?_
  · intro g
    exact T.norm_unramifiedCharacter w hw _
  · intro g v
    rfl

/-- The rank-one cuspidal datum of the unramified character with uniformizer
value `w`. -/
def unramifiedCuspidalDatum (w : ℂˣ) : F.canonicalTopologicalData.CuspidalDatum.{uF, uF} where
  rank := 1
  rank_pos := Nat.one_pos
  cls := (Correspondence.rankOneSupercuspidalObject.{uF, uF} F (character F w)).isoClass

/-- The normalized principal series `i(χ_(w_1), …, χ_(w_m))` of `GL_m`, with the
lifted rank-one character objects as factors. -/
def unitaryBlock {m : ℕ} (w : Fin m → ℂˣ) :
    SmoothRep.{0, uF, uF} ℂ (GeneralLinear m F.Carrier) :=
  (F.canonicalTopologicalData.normalizedProductInductionFunctor (BlockShape.singletons m)).obj
    (fun k => (Correspondence.rankOneSupercuspidalObject.{uF, uF} F (character F (w k))).obj)

/-- A normalized principal series of norm-one unramified characters is
irreducible: its singleton segments are unlinked. -/
theorem unitaryBlock_isIrreducible {m : ℕ} (hm : 0 < m) (w : Fin m → ℂˣ)
    (hw : ∀ k, ‖(w k : ℂ)‖ = 1) :
    (unitaryBlock F w).representation.IsIrreducible := by
  let T := F.canonicalTopologicalData
  let := T.topology
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  let ρ : Fin (n + 1) → T.CuspidalDatum.{uF, uF} := fun k => unramifiedCuspidalDatum F (w k)
  let A := fun k => Correspondence.rankOneSupercuspidalObject.{uF, uF} F (character F (w k))
  have h : ∑ k, (ρ k).rank = n + 1 := by simp [ρ, unramifiedCuspidalDatum]
  let d : T.SegmentProductDatum.{uF, uF} (n + 1) := PadicField.TopologicalData.SegmentProductDatum.ofCuspidals T ρ h A
  have hsoc : d.HasSegmentSocles :=
    PadicField.TopologicalData.SegmentProductDatum.ofCuspidals_hasSegmentSocles T ρ h A (fun _ => rfl)
  have hhead (i : Fin (n + 1)) : T.IsSegmentHead (d.segments i) (d.blocks i) :=
    singletonSegment_isSegmentHead F T (ρ i) (A i) rfl
  have hsq (i : Fin (n + 1)) : T.IsSquareIntegrable (d.blocks i).representation :=
    isSquareIntegrable_castRank F T _ _ (rankOneUnitary_isSquareIntegrable F (w i) (hw i))
  have hunl : d.multisegment.IsUnlinked := by
    intro Δ hΔ Δ' hΔ'
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hΔ
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hΔ'
    exact Classification.squareIntegrableSegmentNonlinkage.{uF, 0} T _ _
      (d.blocks i) (d.blocks j) (hhead i) (hhead j) (hsq i) (hsq j)
  have hirr := (Classification.segmentSocleProductIrreducibility.{uF, uF} F T n d hsoc).mpr hunl
  have hEq : T.cuspidalProductInduced ρ h A = unitaryBlock F w := rfl
  have e := SmoothRep.equivOfIso
    (PadicField.TopologicalData.SegmentProductDatum.ofCuspidalsInducedIso T ρ h A)
  rw [hEq] at e
  exact (isIrreducible_iff_of_equiv e).mp hirr

/-- A normalized principal series of norm-one unramified characters is
analytically tempered. -/
theorem unitaryBlock_isTempered {m : ℕ} (hm : 0 < m) (w : Fin m → ℂˣ)
    (hw : ∀ k, ‖(w k : ℂ)‖ = 1) :
    F.canonicalTopologicalData.IsTempered (unitaryBlock F w).representation := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let B := BlockShape.singletons m
  let A := fun k => Correspondence.rankOneSupercuspidalObject.{uF, uF} F (character F (w k))
  let ρ := fun k => (A k).obj.representation
  have hirr : ∀ k, (ρ k).IsIrreducible := fun k => (A k).property.1
  have hadm : ∀ k, IsAdmissible (ρ k) := fun k => (A k).property.2.1
  have htemp : ∀ k, T.IsTempered (ρ k) := fun k =>
    isTempered_of_isSquareIntegrable F T (rankOneUnitary_isSquareIntegrable F (w k) (hw k))
  let := T.leviTopologicalGroup B
  let := hirr
  have hσirr : (B.blockTensor ρ).IsIrreducible :=
    FiniteTensor.isIrreducible_external ρ
      (fun k φ => (admissibleSchur_scalarEndomorphism _ (hadm k) (hirr k) φ).exists)
  let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  let := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  let := hμ
  have hσtemp := (glBlockTensorTempered p F T m hm B (fun k => ((A k).obj : Type uF)) ρ
    hirr hadm).mp htemp μ
  exact glTemperedInductionPreservation.{uF, uF} p F T m hm B μ _ (B.blockTensor ρ)
    hσirr hσtemp

end Canonical

end Langlands.Unramified
