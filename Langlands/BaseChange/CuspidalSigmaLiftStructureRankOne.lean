import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.TwistedCharacter
import Langlands.JacquetLanglands.EssentiallySquareIntegrable
import Langlands.Group.GL.RankReindex
import Langlands.Representation.RankinSelberg.HighlyRamified.PairInductionGenericity
import Langlands.Representation.Smooth.Schur.Proof

/-! # Rank-one σ-lift structure -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

universe u v uV uW

section RankOne

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type v} [Field E] [Algebra F E]

/-- In rank one the norm-twist stabilizer of an irreducible admissible representation is trivial. -/
theorem normTwistStabilizer_card_rankOne {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear 1 F) V) (hπ : IsAdmissible π)
    (hπi : π.IsIrreducible) : Nat.card (normTwistStabilizer E π) = 1 := by
  obtain ⟨χ, ⟨-, hχ⟩, -⟩ := admissibleSchur_centralCharacter π hπ hπi
  let : π.IsIrreducible := hπi
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear 1 F)) π.asModule
  have hone (κ : normTwistStabilizer E π) : κ = 1 := by
    obtain ⟨-, ⟨e⟩⟩ := (mem_normTwistStabilizer E π κ.1).mp κ.2
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    let g : GeneralLinear 1 F := scalar x
    have hdet : determinant g = x := by
      apply Units.ext
      simp [g, determinant, scalar]
    let z : Subgroup.center (GeneralLinear 1 F) :=
      ⟨g, JacquetLanglands.mem_center_generalLinear_one F g⟩
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans (map_zero e).symm))
    have he := LinearMap.congr_fun (e.isIntertwining' g) w
    change e (π g w) = (κ.1 (determinant g) : ℂ) • π g (e w) at he
    change (_ : Fˣ →* ℂˣ) x = 1
    change e (π (z : GeneralLinear 1 F) w) =
      (κ.1 (determinant g) : ℂ) • π (z : GeneralLinear 1 F) (e w) at he
    rw [hdet, hχ, hχ, map_smul] at he
    have hχw : (χ z : ℂ) • e w ≠ 0 := smul_ne_zero (χ z).ne_zero hew
    apply Units.ext
    change (κ.1 x : ℂ) = 1
    exact (smul_left_injective ℂ hχw) (he.symm.trans (one_smul ℂ _).symm)
  exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hone a).trans (hone b).symm⟩, ⟨1⟩⟩

end RankOne

private theorem isSigmaStable_pow {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {P : Representation ℂ (GeneralLinear n E) W} (A : SigmaIntertwiner σ n P) (i : ℕ) :
    Nonempty (P.Equiv (P.comp (entrywiseAut (σ ^ i) n).toMonoidHom)) := by
  induction i with
  | zero =>
    exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ W) (fun g => by
      simp [pow_zero, entrywiseAut_one_apply])⟩
  | succ i ih =>
    obtain ⟨e⟩ := ih
    refine ⟨e.trans (Representation.Equiv.mk A.toLinearEquiv (fun g => ?_))⟩
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, pow_succ',
      entrywiseAut_mul_apply] using A.comp_apply_eq (entrywiseAut (σ ^ i) n g)

private def rankOneOrbitConclusion {F : Type u} [Field F]
    {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] (σ : E ≃ₐ[F] E)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear 1 E) W) (s l : ℕ) : Prop :=
    s ∣ l ∧
      ∃ (n₁ : ℕ) (hn₁ : 0 < n₁) (h : s * n₁ = 1)
        (W₁ : Type uW) (_ : AddCommGroup W₁) (_ : Module ℂ W₁)
        (P₁ : Representation ℂ (GeneralLinear n₁ E) W₁),
        GeneralLinear.IsSupercuspidal P₁ ∧ P₁.IsIrreducible ∧
        (∀ i : ℕ, Nonempty (P₁.Equiv (P₁.comp (entrywiseAut (σ ^ i) n₁).toMonoidHom)) ↔
          s ∣ i) ∧
        Nonempty (P.Equiv
          ((sigmaOrbitProduct σ (s) hn₁ P₁).comp
            (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom))

/-- Rank one of the supercuspidal σ-lift structure theorem. A σ-intertwiner already supplies
all the required stability. -/
def CuspidalSigmaLiftStructureRankOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (l : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear 1 F) V), IsAdmissible π → π.IsIrreducible →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (P : Representation ℂ (GeneralLinear 1 E) W), IsAdmissible P → P.IsIrreducible →
    SigmaIntertwiner σ 1 P →
    rankOneOrbitConclusion σ P (Nat.card (normTwistStabilizer E π)) l

/-- The one-block structure and exact stabilizer period in rank one. -/
theorem cuspidalSigmaLiftStructure_rankOne : CuspidalSigmaLiftStructureRankOneStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l V _ _ π hπ hπi W _ _ P hP hPi A
  rw [normTwistStabilizer_card_rankOne π hπ hπi]
  unfold rankOneOrbitConclusion
  refine ⟨one_dvd _, 1, Nat.one_pos, rfl, W, inferInstance, inferInstance, P,
    RankinSelberg.HighlyRamified.isSupercuspidal_rankOne hP, hPi,
    fun i => ⟨fun _ => one_dvd i, fun _ => isSigmaStable_pow A i⟩, ?_⟩
  obtain ⟨e⟩ := sigmaOrbitProduct_one_equiv σ Nat.one_pos P hP.1
  have hreindex (h : 1 * 1 = 1) :
      (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom =
        MonoidHom.id (GeneralLinear 1 E) := by
    rw [GeneralLinear.reindex_finCongr_rfl]
    rfl
  rw [hreindex, MonoidHom.comp_id] at e ⊢
  exact ⟨e.symm⟩

end Langlands.BaseChange
