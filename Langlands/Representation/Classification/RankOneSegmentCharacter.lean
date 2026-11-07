import Langlands.Representation.Classification.RankOneSegmentEmbedding
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof
import Langlands.Representation.Classification.SegmentTensorStabilizerProof
import Langlands.Representation.Classification.ConstituentCompatibilityAlgebraicProof
import Langlands.Representation.Classification.SegmentConstituentCharacterTwistCompatibilityProof
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Category.UniverseLift

/-! Scalar characters of the increasing rank-one segment socle. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

universe uG uH uV

/-- An irreducible scalar action forces every action on its carrier to be
irreducible: every linear subspace is invariant under the scalar action. -/
private theorem irreducible_of_irreducible_scalar
    {G : Type uG} {H : Type uH} [Group G] [Group H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ H V) (hσ : Representation.IsIrreducible σ)
    (hscalar : ∀ h v, ∃ c : ℂ, σ h v = c • v)
    (ρ : Representation ℂ G V) : Representation.IsIrreducible ρ := by
  letI := hσ
  let f : Subrepresentation ρ → Subrepresentation σ := fun S =>
    ⟨S.toSubmodule, fun h v hv => by
      obtain ⟨c, hc⟩ := hscalar h v
      rw [hc]
      exact S.toSubmodule.smul_mem c hv⟩
  have hf : Function.Injective f := by
    intro S U h
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation σ => U.toSubmodule) h)
  have hbot : f ⊥ = ⊥ := rfl
  have htop : f ⊤ = ⊤ := rfl
  haveI : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun h => (bot_ne_top : (⊥ : Subrepresentation σ) ≠ ⊤)
      (hbot.symm.trans ((congrArg f h).trans htop))⟩⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (f S) with h | h
  · exact Or.inl (hf (h.trans hbot.symm))
  · exact Or.inr (hf (h.trans htop.symm))

end Langlands.Classification

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The scalar midpoint action on the full tensor carrier. -/
abbrev rankOneSegmentScalarRepresentation
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier))
    (m : ℕ) (χ : F.Carrierˣ →* ℂˣ) :=
  letI := T.topology
  twist (T.rankOneSegmentCharacter m χ)
    (Representation.trivial ℂ (GeneralLinear (m * 1) F.Carrier)
      (PiTensorProduct ℂ (fun i => T.segmentFactors A m (by omega) i)))

/-- Irreducibility of the actual cuspidal tensor makes the midpoint scalar
source irreducible. -/
theorem rankOneSegmentScalarRepresentation_irreducible
    (A : letI := T.topology; SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := 1))
    (m : ℕ) (hm : 0 < m) (χ : F.Carrierˣ →* ℂˣ)
    (hA : letI := T.topology; HasScalarCharacter A.obj.representation (MonoidHom.id _)
      (χ.comp determinant)) :
    letI := T.topology
    Representation.IsIrreducible (T.rankOneSegmentScalarRepresentation A.obj m χ) := by
  letI := T.topology
  let B := BlockShape.uniform m 1 (by omega)
  let σ := B.blockTensor (fun i => (T.segmentFactors A.obj m (by omega) i).representation)
  have hσ : Representation.IsIrreducible σ :=
    (Classification.segmentFactors_isIrreducible_isLeviCuspidal F T m hm (by omega) A).1
  have hproj : Function.Surjective (B.leviProjection F.Carrier) := by
    intro l
    exact ⟨B.leviInParabolic F.Carrier l, B.leviProjection_section F.Carrier l⟩
  let σP := twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))
  have hσP : Representation.IsIrreducible σP :=
    (isIrreducible_twist_iff _ _).mpr
      (CuspidalSupport.isIrreducible_comp_of_surjective σ
        (hρ := hσ) (B.leviProjection F.Carrier) hproj)
  apply Classification.irreducible_of_irreducible_scalar σP hσP
  intro g v
  exact ⟨(T.rankOneSegmentCharacter m χ (g : GeneralLinear (m * 1) F.Carrier) : ℂ),
    T.rankOneSegment_inducing_scalar A.obj m χ hA g v⟩

/-- The character embedding with its source carrier in the same universe as
segment constituents, retaining the same scalar action. -/
def rankOneSegmentLiftedEmbedding
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier))
    (m : ℕ) (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ))
    (hA : letI := T.topology; HasScalarCharacter A.representation (MonoidHom.id _)
      (χ.comp determinant)) :
    letI := T.topology
    (universeLiftRepresentation.{uF} (T.rankOneSegmentScalarRepresentation A m χ)).IntertwiningMap
      (T.segmentInduced A m (by omega)).representation :=
  letI := T.topology
  (T.rankOneSegmentEmbedding A m χ hχ hA).comp
    (universeLiftEquiv.{uF} (T.rankOneSegmentScalarRepresentation A m χ)).symm.toIntertwiningMap

theorem rankOneSegmentLiftedEmbedding_injective
    (A : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear 1 F.Carrier))
    (m : ℕ) (χ : F.Carrierˣ →* ℂˣ)
    (hχ : letI := T.topology; IsOpen (χ.ker : Set F.Carrierˣ))
    (hA : letI := T.topology; HasScalarCharacter A.representation (MonoidHom.id _)
      (χ.comp determinant)) :
    Function.Injective (T.rankOneSegmentLiftedEmbedding A m χ hχ hA) :=
  letI := T.topology
  (T.rankOneSegmentEmbedding_injective A m χ hχ hA).comp
    (universeLiftEquiv.{uF} (T.rankOneSegmentScalarRepresentation A m χ)).symm.injective

end Langlands.PadicField.TopologicalData

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every increasing rank-one segment constituent acts by the midpoint
character, as in the exact published statement. -/
theorem segmentRankOneZelevinskyCharacter :
    SegmentRankOneZelevinskyCharacter.{uF,uV} F T := by
  letI := T.topology
  intro Δ χ A h1 hrep hA π hπ
  obtain ⟨⟨r, hr, c⟩, m, hm⟩ := Δ
  change r = 1 at h1
  subst r
  letI := T.generalLinearTopologicalGroup 1
  letI := T.generalLinearTopologicalGroup (m * 1)
  have hχ : IsOpen (χ.ker : Set F.Carrierˣ) := by
    letI : Nontrivial A.obj :=
      CuspidalSupport.nontrivial_of_isIrreducible A.obj.representation (hρ := A.property.1)
    exact T.isOpen_ker_of_isOpen_ker_comp_determinant (by omega) χ
      (hA.isOpen_ker continuous_id A.obj.isSmooth)
  let ρ := universeLiftRepresentation.{uF} (T.rankOneSegmentScalarRepresentation A.obj m χ)
  let j := T.rankOneSegmentLiftedEmbedding A.obj m χ hχ hA
  have hj : Function.Injective j := T.rankOneSegmentLiftedEmbedding_injective A.obj m χ hχ hA
  have hρ : Representation.IsIrreducible ρ :=
    (isIrreducible_universeLift_iff _).mpr
      (T.rankOneSegmentScalarRepresentation_irreducible A m hm χ hA)
  obtain ⟨π₀, hsocle, -⟩ := segmentZelevinskyConstituentExistence F T
    (⟨⟨1, hr, c⟩, m, hm⟩ : T.Segment)
  obtain ⟨_, j₀, hj₀, hu⟩ := (T.isSegmentSocle_iff _ π₀ A hrep).mp hsocle
  obtain ⟨hπirr, jπ, hjπ⟩ := (T.isSegmentSubrepresentation_iff _ π A hrep).mp hπ
  have hrange : j.toLinearMap.range = jπ.toLinearMap.range :=
    (hu _ ρ hρ j hj).trans (hu _ π.representation hπirr jπ hjπ).symm
  intro g v
  apply hjπ
  obtain ⟨w, hw⟩ : ∃ w, j w = jπ v := by
    have hv : jπ v ∈ j.toLinearMap.range := by
      rw [hrange]
      exact ⟨v, rfl⟩
    exact hv
  rw [jπ.isIntertwining, ← hw, ← j.isIntertwining]
  change j (ULift.up ((T.rankOneSegmentCharacter m χ g : ℂ) • w.down)) = _
  change j ((T.rankOneSegmentCharacter m χ g : ℂ) • w) = _
  rw [map_smul, hw, map_smul]
  rfl

end Langlands.Classification
