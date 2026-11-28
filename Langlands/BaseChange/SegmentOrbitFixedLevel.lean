import Langlands.BaseChange.SigmaOrbitDeterminantTwist
import Langlands.BaseChange.SupercuspidalFixedLevelTwistFiniteness
import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Classification.SegmentConstituentCharacterTwistCompatibilityProof
import Langlands.Representation.Classification.SegmentSocleDecreasingHead
import Langlands.LocalField.PadicBridge

/-! # Fixed-level finiteness for orbit products with a visible segment base -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear Classification PadicField.TopologicalData

universe u v z

variable {F : Type u} [Field F] [TopologicalSpace F]
  {p : ℕ} [Fact p.Prime] {E : PadicField.{v} p}
  (T : E.TopologicalData) [Algebra F E.Carrier] (σ : E.Carrier ≃ₐ[F] E.Carrier)

set_option backward.isDefEq.respectTransparency.types false

omit [TopologicalSpace F] in
/-- The specified normalized orbit product has a seed which is a segment head
with the given supercuspidal start. -/
def HasSegmentOrbitModel {r s t n : ℕ} (hr : 0 < r) (hs : 0 < s)
    (h : t * (s * r) = n)
    (A : letI := T.topology; SupercuspidalRep.{v,max v z} (F := E.Carrier) (n := r))
    (P : letI := T.topology; SmoothRep.{0,v,z} ℂ (GeneralLinear n E.Carrier)) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  ∃ Q : SmoothRep.{0,v,z} ℂ (GeneralLinear (s * r) E.Carrier),
    IsIrreducibleHead (T.segmentInduced A.obj s hr).representation
      Q.universeLift.{v}.representation ∧
    Nonempty (P.representation.Equiv
      ((sigmaOrbitProduct σ t (Nat.mul_pos hs hr) Q.representation).comp
        (reindex (R := E.Carrier) (finCongr h)).symm.toMonoidHom))

private theorem segmentHead_detTwist {r s : ℕ} (hr : 0 < r) :
    letI := T.topology
    ∀ (A D : SupercuspidalRep.{v,max v z} (F := E.Carrier) (n := r))
      (P Q : SmoothRep.{0,v,max v z} ℂ (GeneralLinear (s * r) E.Carrier))
      (a : ℂˣ),
      Nonempty (A.obj.representation.Equiv
        (twist (T.toLocalFieldData.determinantUnramifiedCharacter r a) D.obj.representation)) →
      IsIrreducibleHead (T.segmentInduced A.obj s hr).representation P.representation →
      IsIrreducibleHead (T.segmentInduced D.obj s hr).representation Q.representation →
      Nonempty (P.representation.Equiv
        (twist (T.toLocalFieldData.determinantUnramifiedCharacter (s * r) a) Q.representation)) := by
  let := T.topology
  rintro A D P Q a ⟨e⟩ hP hQ
  let U := T.toLocalFieldData
  let χ : Induction.SmoothCharacter ℂ E.Carrierˣ :=
    ⟨U.unramifiedCharacter a, U.isOpen_ker_unramifiedCharacter a⟩
  let ψ := U.determinantUnramifiedCharacter (s * r) a
  let hχ := U.isOpen_ker_determinantUnramifiedCharacter r a
  let D' := D.obj.twist (U.determinantUnramifiedCharacter r a) hχ
  let eD : D' ≅ A.obj := SmoothRep.mkIso e.symm
  let eInd := (T.segmentInducedCharacterTwistEquiv D.obj s hr χ hχ).trans
    (SmoothRep.equivOfIso (T.segmentInducedIso eD s hr))
  have hQ' := ((isIrreducibleHead_twist_iff ψ _ _).mpr hQ).of_equiv eInd
  obtain ⟨hPi, q, hq, _⟩ := hP
  exact hQ'.nonempty_equiv_of_quotient hPi q hq

private theorem determinantTwists_mul_cancel (r : ℕ) (a b : ℂˣ) :
    T.toLocalFieldData.determinantUnramifiedCharacter r (a * b⁻¹) *
        T.toLocalFieldData.determinantUnramifiedCharacter r b =
      T.toLocalFieldData.determinantUnramifiedCharacter r a := by
  apply MonoidHom.ext
  intro g
  let j := T.ord (determinant g : E.Carrier)
  change (a * b⁻¹) ^ j * b ^ j = a ^ j
  rw [← mul_zpow, mul_assoc, inv_mul_cancel, mul_one]

private theorem ordUnits_algEquiv :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    IsModuleTopology F E.Carrier → ∀ b : E.Carrierˣ,
      T.toLocalFieldData.ordUnits (Units.map σ.toRingHom.toMonoidHom b) =
        T.toLocalFieldData.ordUnits b := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hModule b
  let U := T.toLocalFieldData
  let c := Units.map σ.toRingHom.toMonoidHom b
  have he : U.normalizedAbsUnits c = U.normalizedAbsUnits b :=
    normalizedAbsUnits_algEquiv σ b
  have hc : c / b ∈ U.normalizedAbsUnits.ker :=
    MonoidHom.mem_ker.mpr (by rw [map_div, he, div_self'])
  have hk : c / b ∈ U.ordUnits.ker := by rwa [U.ker_ordUnits]
  exact div_eq_one.mp (by simpa only [map_div] using MonoidHom.mem_ker.mp hk)

set_option maxHeartbeats 450000 in
private theorem segmentOrbitModel_detTwist {r s t n : ℕ} (hr : 0 < r) (hs : 0 < s)
    (h : t * (s * r) = n) :
    letI := T.topology
    IsModuleTopology F E.Carrier →
    ∀ (A D : SupercuspidalRep.{v,max v z} (F := E.Carrier) (n := r))
      (P R : SmoothRep.{0,v,z} ℂ (GeneralLinear n E.Carrier)) (a : ℂˣ),
      HasSegmentOrbitModel T σ hr hs h A P → HasSegmentOrbitModel T σ hr hs h D R →
      Nonempty (A.obj.representation.Equiv
        (twist (T.toLocalFieldData.determinantUnramifiedCharacter r a) D.obj.representation)) →
      Nonempty (P.representation.Equiv
        (twist (T.toLocalFieldData.determinantUnramifiedCharacter n a) R.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  rintro hModule A D P R a ⟨Q, hQ, ⟨eP⟩⟩ ⟨S, hS, ⟨eR⟩⟩ eAD
  let U := T.toLocalFieldData
  let χ : Induction.SmoothCharacter ℂ E.Carrierˣ :=
    ⟨U.unramifiedCharacter a, U.isOpen_ker_unramifiedCharacter a⟩
  let hm := Nat.mul_pos hs hr
  obtain ⟨e⟩ := segmentHead_detTwist.{v,z} T hr A D Q.universeLift.{v}
    S.universeLift.{v} a eAD hQ hS
  let eSeed := Q.universeLiftEquiv.{v}.trans
    (e.trans (twistEquiv _ S.universeLiftEquiv.{v}.symm))
  have hχ (j : ℕ) (b : E.Carrierˣ) :
      χ.toMonoidHom (Units.map (σ ^ j).toRingHom.toMonoidHom b) = χ.toMonoidHom b :=
    congrArg (zpowersHom ℂˣ a) (ordUnits_algEquiv T (σ ^ j) hModule b)
  have hTwist := sigmaOrbitDeterminantTwist.{u,v,z,z} F E.Carrier σ χ hχ t
    (s * r) n hm h S R S.representation R.representation ⟨eR⟩
  obtain ⟨eTwist⟩ := hTwist
  let B := BlockShape.uniform t (s * r) hm
  let eProduct := U.normalizedProductInducedEquiv B
    (fun j => BinaryTensor.compEquiv eSeed (entrywiseAut (σ ^ (j : ℕ)) (s * r)).toMonoidHom)
  exact ⟨eP.trans ((BinaryTensor.compEquiv eProduct
    (reindex (R := E.Carrier) (finCongr h)).symm.toMonoidHom).trans eTwist.symm)⟩

/-- At fixed segment and orbit lengths, the irreducible products whose segment
bases have fixed vectors at a compact open subgroup admit a finite cover by
determinant twists. -/
def SegmentOrbitFixedLevelStatement : Prop :=
  letI := T.topology
  IsModuleTopology F E.Carrier →
    ∀ {r s t n : ℕ} (hr : 0 < r) (hs : 0 < s) (h : t * (s * r) = n)
      (J : OpenSubgroup (GeneralLinear r E.Carrier)),
      IsCompact (J : Set (GeneralLinear r E.Carrier)) →
      ∃ C : Finset (SmoothRep.{0,v,z} ℂ (GeneralLinear n E.Carrier)),
        (∀ R ∈ C, R.IsIrreducible) ∧
        ∀ (P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E.Carrier)), P.IsIrreducible →
          ∀ A : SupercuspidalRep.{v,max v z} (F := E.Carrier) (n := r),
            fixedVectors A.obj.representation J.toSubgroup ≠ ⊥ →
            HasSegmentOrbitModel T σ hr hs h A P →
            ∃ R ∈ C, ∃ a : ℂˣ, Nonempty (P.representation.Equiv
              (twist (T.toLocalFieldData.determinantUnramifiedCharacter n a) R.representation))

set_option maxHeartbeats 450000 in
theorem segmentOrbitFixedLevel : SegmentOrbitFixedLevelStatement.{u,v,z} T σ := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hModule r s t n hr hs h J hJ
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  obtain ⟨C, hC⟩ := supercuspidalFixedLevelTwistFiniteness.{v,max v z} E.Carrier d J hJ
  let U := T.toLocalFieldData
  let Covers (D : SupercuspidalRep.{v,max v z} (F := E.Carrier) (n := d + 1))
      (P : SmoothRep.{0,v,z} ℂ (GeneralLinear n E.Carrier)) :=
    P.IsIrreducible ∧
    ∃ A : SupercuspidalRep.{v,max v z} (F := E.Carrier) (n := d + 1),
      HasSegmentOrbitModel T σ hr hs h A P ∧
      ∃ a : ℂˣ, Nonempty (A.obj.representation.Equiv
        (twist (U.determinantUnramifiedCharacter (d + 1) a) D.obj.representation))
  let I := {D : C // ∃ P, Covers D.val P}
  let R (i : I) := i.property.choose
  refine ⟨Finset.univ.image R, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hQ
    exact i.property.choose_spec.1
  · intro P hP A hA hModel
    obtain ⟨D, hD, a, ⟨eA⟩⟩ := hC A hA
    let i : I := ⟨⟨D, hD⟩, P, hP, A, hModel, a, ⟨eA⟩⟩
    obtain ⟨A', hModel', b, ⟨eA'⟩⟩ := i.property.choose_spec.2
    let c := a * b⁻¹
    have eBases : A.obj.representation.Equiv
        (twist (U.determinantUnramifiedCharacter (d + 1) c) A'.obj.representation) := by
      have e := twistEquiv (U.determinantUnramifiedCharacter (d + 1) c) eA'.symm
      rw [twist_twist, determinantTwists_mul_cancel T (d + 1) a b] at e
      exact eA.trans e
    exact ⟨R i, Finset.mem_image_of_mem R (Finset.mem_univ i), c,
      segmentOrbitModel_detTwist T σ hr hs h hModule A A' P (R i) c hModel hModel' ⟨eBases⟩⟩

end Langlands.BaseChange
