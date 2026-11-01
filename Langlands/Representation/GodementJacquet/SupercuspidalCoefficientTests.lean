import Langlands.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
import Langlands.Representation.Smooth.Transfer.GroupEquivalence
import Langlands.Group.GL.OneBlockShape

/-! # Compact determinant-unit coefficients of supercuspidal representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open GeneralLinear CuspidalSupport

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {d : ℕ} (hd : 0 < d)

private theorem oneBlock_embedding_eval
    (m : (LeviAdmissibility.oneBlock d hd).Levi F.Carrier) :
    (LeviAdmissibility.oneBlock d hd).leviEmbedding F.Carrier m =
      m ⟨0, Nat.zero_lt_one⟩ := by
  let B := LeviAdmissibility.oneBlock d hd
  have hB : B.length = 1 := rfl
  let b : Fin B.length := ⟨0, Nat.zero_lt_one⟩
  apply Units.ext
  ext i j
  have hi : B.index b i = i := Fin.ext (B.singleBlock_index_val hB b i)
  have hj : B.index b j = j := Fin.ext (B.singleBlock_index_val hB b j)
  have h := B.leviEmbedding_apply_same F.Carrier m b i j
  rw [hi, hj] at h
  exact h

/-- The determinant-unit subgroup of the positive one-block Levi is the
actual determinant-unit subgroup of GL, with its induced topology. -/
def oneBlockDeterminantUnitHomeomorph :
    letI := T.topology
    (T.determinantNorm d).ker ≃ₜ
      determinantUnitSubgroup T (LeviAdmissibility.oneBlock d hd) := by
  letI := T.topology
  refine
    { toFun := fun g => ⟨fun _ => g.val, ?_⟩
      invFun := fun m => ⟨m.val ⟨0, Nat.zero_lt_one⟩, ?_⟩
      left_inv := fun _ => rfl
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · rw [mem_determinantUnitSubgroup]
    intro i
    exact g.property
  · exact (mem_determinantUnitSubgroup T _ m.val).mp m.property
      ⟨0, Nat.zero_lt_one⟩
  · intro m
    apply Subtype.ext
    funext i
    have hi : i = (⟨0, Nat.zero_lt_one⟩ : Fin 1) :=
      @Subsingleton.elim (Fin 1) inferInstance i _
    subst i
    rfl
  · exact (continuous_pi fun _ => continuous_subtype_val).subtype_mk _
  · exact ((continuous_apply (⟨0, Nat.zero_lt_one⟩ : Fin 1)).comp
      continuous_subtype_val).subtype_mk _

include hd in
/-- The published product-Levi Harish-Chandra theorem implies compact
support for every smooth-dual supercuspidal coefficient on `|det| = 1`. -/
theorem hasCompactSupport_determinantUnit_coefficient
    {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    letI := T.topology
    ∀ (ρ : Representation ℂ (GeneralLinear d F.Carrier) V),
      IsSupercuspidal ρ → ∀ (v : V) (ℓ : Module.Dual ℂ V),
      IsSmoothVector ρ.dual ℓ →
      HasCompactSupport (fun g : (T.determinantNorm d).ker => ℓ (ρ g.val v)) := by
  let := T.topology
  intro ρ hρ v ℓ hℓ
  let B := LeviAdmissibility.oneBlock d hd
  let ρB : Representation ℂ (B.Levi F.Carrier) V :=
    ρ.comp (B.leviEmbedding F.Carrier)
  have hB : IsLeviCuspidal B ρB :=
    (singleBlockCuspidalityClause T d B rfl V ρ).mpr hρ
  have hc := (leviHarishChandraTheorem p F T d B
    (SmoothRep.of ρB hB.1.1)).mp hB.2
  have hℓB : IsSmoothVector ρB.dual ℓ := by
    rw [dual_comp_monoidHom]
    exact isSmoothVector_comp _ (B.leviEmbeddingContinuous F.Carrier).continuous hℓ
  have hℓD : IsSmoothVector (determinantUnitRestriction T B ρB).dual ℓ := by
    rw [determinantUnitRestriction, dual_comp_monoidHom]
    exact isSmoothVector_comp _ continuous_subtype_val hℓB
  have h := (hc v ℓ hℓD).comp_homeomorph (oneBlockDeterminantUnitHomeomorph T hd)
  convert h using 1
  funext g
  change ℓ (ρ g.val v) =
    ℓ (ρ (B.leviEmbedding F.Carrier (fun _ => g.val)) v)
  rw [oneBlock_embedding_eval hd]

end Langlands.GodementJacquet
