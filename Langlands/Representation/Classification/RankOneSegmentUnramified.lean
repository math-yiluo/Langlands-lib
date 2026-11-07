import Langlands.Representation.Classification.RankOneSegmentCharacter
import Langlands.Representation.Classification.SegmentSocleDecreasingHead
import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.Group.GL.IntegralSubgroup

/-! Fixed vectors and decreasing heads for unramified rank-one segments. -/

noncomputable section

namespace Langlands.Classification

universe uG uV

/-- A scalar action is trivial on every subgroup in its character kernel. -/
theorem HasScalarCharacter.fixedVectors_eq_top
    {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {χ : G →* ℂˣ}
    (hρ : HasScalarCharacter ρ (MonoidHom.id G) χ)
    (K : Subgroup G) (hK : K ≤ χ.ker) : fixedVectors ρ K = ⊤ := by
  apply top_unique
  intro v _ k
  have h := hρ k v
  change ρ k v = (χ k : ℂ) • v at h
  change ρ k v = v
  rw [h, show χ k = 1 from hK k.property, Units.val_one, one_smul]

end Langlands.Classification

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A determinant norm twist of an unramified character is trivial on the
norm-one determinant subgroup. -/
theorem ker_determinantNorm_le_ker_power_mul_unramified
    (n : ℕ) (s : ℝ) (χ : F.Carrierˣ →* ℂˣ) (hχ : T.IsUnramifiedCharacter χ) :
    (T.determinantNorm n).ker ≤
      (T.determinantPowerCharacter n s * χ.comp determinant).ker := by
  intro g hg
  have hp := ker_le_realPowerCharacter_ker (T.determinantNorm n) s hg
  have hc : χ (determinant g) = 1 := hχ hg
  change T.determinantPowerCharacter n s g * χ (determinant g) = 1
  rw [hp, hc, mul_one]

/-- Every vector of an unramified rank-one segment subrepresentation is fixed
by all matrices with determinant norm one. -/
theorem IsSegmentSubrepresentation.normOne_fixedVectors
    {Δ : T.Segment.{uV,uF}}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology; SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hrep : Δ.base.IsRepresentedBy A) (h1 : Δ.rank = 1)
    (χ : F.Carrierˣ →* ℂˣ) (hχ : T.IsUnramifiedCharacter χ)
    (hA : letI := T.topology
      HasScalarCharacter A.obj.representation (MonoidHom.id _) (χ.comp determinant)) :
    letI := T.topology
    fixedVectors π.representation (T.determinantNorm Δ.degree).ker = ⊤ := by
  letI := T.topology
  exact (Classification.segmentRankOneZelevinskyCharacter F T Δ χ A h1 hrep hA π hπ
    ).fixedVectors_eq_top _
      (T.ker_determinantNorm_le_ker_power_mul_unramified _ _ χ hχ)

/-- The actual integral matrix subgroup fixes every vector of an unramified
rank-one segment subrepresentation. -/
theorem IsSegmentSubrepresentation.integral_fixedVectors
    {Δ : T.Segment.{uV,uF}}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology; SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hrep : Δ.base.IsRepresentedBy A) (h1 : Δ.rank = 1)
    (χ : F.Carrierˣ →* ℂˣ) (hχ : T.IsUnramifiedCharacter χ)
    (hA : letI := T.topology
      HasScalarCharacter A.obj.representation (MonoidHom.id _) (χ.comp determinant)) :
    letI := T.topology
    fixedVectors π.representation
      (GeneralLinearGroup.integralSubgroup (Fin Δ.degree) T.Integers) = ⊤ := by
  letI := T.topology
  apply top_unique
  intro v _ k
  have hv : v ∈ fixedVectors π.representation (T.determinantNorm Δ.degree).ker := by
    rw [hπ.normOne_fixedVectors T A hrep h1 χ hχ hA]
    trivial
  have hk := (GeneralLinearGroup.mem_integralSubgroup
    (Fin Δ.degree) T.Integers k.val).mp k.property
  exact hv ⟨k.val, Unramified.SphericalExistence.determinantNorm_eq_one_of_integral
    F T (k.val : GeneralLinear Δ.degree F.Carrier) hk.1 hk.2⟩

/-- Unramified rank-one segment subrepresentations have nonzero actual integral
fixed vectors. -/
theorem IsSegmentSubrepresentation.integral_fixedVectors_ne_bot
    {Δ : T.Segment.{uV,uF}}
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSubrepresentation Δ π)
    (A : letI := T.topology; SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hrep : Δ.base.IsRepresentedBy A) (h1 : Δ.rank = 1)
    (χ : F.Carrierˣ →* ℂˣ) (hχ : T.IsUnramifiedCharacter χ)
    (hA : letI := T.topology
      HasScalarCharacter A.obj.representation (MonoidHom.id _) (χ.comp determinant)) :
    letI := T.topology
    fixedVectors π.representation
      (GeneralLinearGroup.integralSubgroup (Fin Δ.degree) T.Integers) ≠ ⊥ := by
  letI := T.topology
  have hi := ((T.isSegmentSubrepresentation_iff Δ π A hrep).mp hπ).1
  letI := CuspidalSupport.nontrivial_of_isIrreducible π.representation (hρ := hi)
  rw [hπ.integral_fixedVectors T A hrep h1 χ hχ hA]
  exact top_ne_bot

/-- Choose an actual strong socle of an unramified rank-one segment, together
with its norm-one fixed space and its strong decreasing head. -/
def unramifiedRankOneSegmentSocle
    (Δ : T.Segment.{uV,uF})
    (A : letI := T.topology; SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := Δ.rank))
    (hrep : Δ.base.IsRepresentedBy A) (h1 : Δ.rank = 1)
    (χ : F.Carrierˣ →* ℂˣ) (hχ : T.IsUnramifiedCharacter χ)
    (hA : letI := T.topology
      HasScalarCharacter A.obj.representation (MonoidHom.id _) (χ.comp determinant)) :
    letI := T.topology
    {π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier) //
      T.IsSegmentSocle Δ π ∧
      fixedVectors π.representation (T.determinantNorm Δ.degree).ker = ⊤ ∧
      IsIrreducibleHead
        (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).representation π.representation} := by
  letI := T.topology
  let hex := Classification.segmentZelevinskyConstituentExistence F T
  let π := (hex Δ).choose
  have hs := (hex Δ).choose_spec.1
  have hh := (hex Δ).choose_spec.2
  exact ⟨π, hs, hs.isSegmentSubrepresentation.normOne_fixedVectors T A hrep h1 χ hχ hA,
    hh A hrep⟩

end Langlands.PadicField.TopologicalData
