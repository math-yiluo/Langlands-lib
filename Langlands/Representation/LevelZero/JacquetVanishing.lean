import Langlands.Representation.LevelZero.Basic
import Langlands.Representation.FiniteGeneralLinear.Cuspidal
import Langlands.Representation.Classification.Supercuspidal
import Langlands.Group.GL.TriangularParabolic
import Langlands.Group.GL.Transvection

/-!
# Vanishing of Jacquet coinvariants for level-zero induction

Let `σ` be a cuspidal representation of `GL_{m+1}(k)` and `Λ` its inflation to
`J = ϖ^ℤ GL_{m+1}(𝒪)`. For every proper standard block parabolic with unipotent radical
`U`, every `g`, every `y` and every `v`, the translates of `y · f_v` (where `f_v` is the
function supported on `J` with value `v` at `1`) by a finite family of elements of `gUg⁻¹`
sum to zero. The family is indexed by the residue unipotent radical `U(k)`: with the
Iwasawa decomposition `g⁻¹y = b k`, the elements are `g b γ̂ b⁻¹ g⁻¹` for integral lifts `γ̂`
of `γ ∈ U(k)`, and the sum reduces to the average of `σ` over `U(k)`, which is zero by
cuspidality.
-/

noncomputable section

namespace Langlands.LevelZero

open GeneralLinear ValuativeRel Langlands.Induction

universe u uW

/-- Properness of a block parabolic does not depend on the (nonzero) coefficient ring. -/
theorem _root_.Langlands.GeneralLinear.BlockShape.parabolic_ne_top_of_ne_top {n : ℕ}
    (B : BlockShape n) {R S : Type*} [CommRing R] [Field S]
    (h : B.parabolic R ≠ ⊤) : B.parabolic S ≠ ⊤ := by
  obtain ⟨g, hg⟩ : ∃ g, g ∉ B.parabolic R := by
    by_contra hall
    push Not at hall
    exact h (eq_top_iff.mpr fun g _ => hall g)
  rw [B.mem_parabolic_iff] at hg
  push Not at hg
  obtain ⟨i, j, a, b, hji, -⟩ := hg
  have hne : B.index i a ≠ B.index j b := fun he =>
    (ne_of_gt hji) (congrArg Sigma.fst (B.indexEquiv.injective he))
  intro htop
  have hmem : transvectionUnit (B.index i a) (B.index j b) hne (1 : S) ∈ B.parabolic S :=
    htop ▸ Subgroup.mem_top _
  have h0 := (B.mem_parabolic_iff S _).mp hmem i j a b hji
  change Matrix.transvection (B.index i a) (B.index j b) (1 : S) (B.index i a)
    (B.index j b) = 0 at h0
  simp [Matrix.transvection, Matrix.one_apply_ne hne] at h0

/-- An element of a parabolic normalizes its unipotent radical. -/
theorem _root_.Langlands.GeneralLinear.BlockShape.conj_mem_unipotentSubgroup {n : ℕ}
    (B : BlockShape n) {R : Type*} [CommRing R] {b u : GeneralLinear n R}
    (hb : b ∈ B.parabolic R) (hu : u ∈ B.unipotentSubgroup R) :
    b * u * b⁻¹ ∈ B.unipotentSubgroup R := by
  obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.mp hu
  have hc : (⟨b, hb⟩ : B.parabolic R) * u' * (⟨b, hb⟩ : B.parabolic R)⁻¹ ∈
      B.unipotentRadical R :=
    (B.unipotentRadicalNormal R).conj_mem u' hu' ⟨b, hb⟩
  refine Subgroup.mem_map.mpr ⟨_, hc, ?_⟩
  rw [← hu'eq]
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]

section CuspidalSum

variable {k : Type*} [Field k] {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The sum of a cuspidal representation over a proper block unipotent radical vanishes. -/
theorem cuspidal_sum_eq_zero {σ : Representation ℂ (GeneralLinear n k) W}
    (hσ : FiniteGeneralLinear.IsCuspidal σ) (B : BlockShape n) (hB : B.parabolic k ≠ ⊤)
    [Fintype (B.unipotentSubgroup k)] (w : W) :
    ∑ γ : B.unipotentSubgroup k, σ γ w = 0 := by
  apply hσ B hB
  intro γ₀ hγ₀
  rw [map_sum]
  refine (Fintype.sum_equiv (Equiv.mulLeft (⟨γ₀, hγ₀⟩ : B.unipotentSubgroup k)) _ _ ?_)
  intro γ
  simp [← Module.End.mul_apply, ← map_mul]

end CuspidalSum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {m : ℕ} {ϖ : Fˣ} (hϖ : Iwasawa.IsUniformizingElement (valuation F) ϖ)
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (GeneralLinear (m + 1) (IsLocalRing.ResidueField (integers F))) W)
omit [IsNonarchimedeanLocalField F] in
theorem openSubgroup_le_inducingSubgroup (L : OpenSubgroup (GeneralLinear (m + 1) F))
    (hLK : (L : Subgroup (GeneralLinear (m + 1) F)) ≤ maximalCompact (F := F) m) :
    (L : Subgroup (GeneralLinear (m + 1) F)) ≤ inducingSubgroup m ϖ :=
  hLK.trans (maximalCompact_le_inducingSubgroup m ϖ)

theorem inducingRep_openSubgroup (L : OpenSubgroup (GeneralLinear (m + 1) F))
    (hLK : (L : Subgroup (GeneralLinear (m + 1) F)) ≤ maximalCompact (F := F) m)
    (hLred : ∀ (g : GeneralLinear (m + 1) F) (hg : g ∈ L), residueReduction m ⟨g, hLK hg⟩ = 1)
    (g : GeneralLinear (m + 1) F) (hg : g ∈ L) :
    inducingRep m hϖ σ ⟨g, openSubgroup_le_inducingSubgroup (ϖ := ϖ) L hLK hg⟩ = 1 := by
  rw [inducingRep_of_mem hϖ σ (hLK hg), hLred g hg, map_one]

/-- The level-zero induced function supported on `J` with value `v` at the identity. -/
def levelZeroIndicator (L : OpenSubgroup (GeneralLinear (m + 1) F))
    (hLK : (L : Subgroup (GeneralLinear (m + 1) F)) ≤ maximalCompact (F := F) m)
    (hLred : ∀ (g : GeneralLinear (m + 1) F) (hg : g ∈ L), residueReduction m ⟨g, hLK hg⟩ = 1) :
    W →ₗ[ℂ] SmoothFunctions (inducingSubgroup m ϖ) (inducingRep m hϖ σ) :=
  indicatorLinear (inducingSubgroup m ϖ) (inducingRep m hϖ σ) L
    (openSubgroup_le_inducingSubgroup L hLK) (inducingRep_openSubgroup hϖ σ L hLK hLred)

/-- **Key vanishing.** For a proper block shape `B`, every `g`, `y` and `v`, a nonempty finite
family of elements of `g U_B g⁻¹` has translates of `y · f_v` summing to zero. -/
theorem exists_sum_translate_eq_zero [Finite (IsLocalRing.ResidueField (integers F))]
    (hσ : FiniteGeneralLinear.IsCuspidal σ) (L : OpenSubgroup (GeneralLinear (m + 1) F))
    (hLK : (L : Subgroup (GeneralLinear (m + 1) F)) ≤ maximalCompact (F := F) m)
    (hLred : ∀ (g : GeneralLinear (m + 1) F) (hg : g ∈ L), residueReduction m ⟨g, hLK hg⟩ = 1)
    (B : BlockShape (m + 1)) (hB : B.parabolic F ≠ ⊤) (g y : GeneralLinear (m + 1) F)
    (v : W) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : Nonempty ι) (c : ι → B.conjugateUnipotent g),
      ∑ i, smoothInduced (inducingSubgroup m ϖ) (inducingRep m hϖ σ) (c i)
        (smoothInduced (inducingSubgroup m ϖ) (inducingRep m hϖ σ) y
          (levelZeroIndicator hϖ σ L hLK hLred v)) = 0 := by
  classical
  set J := inducingSubgroup m ϖ
  set Λ := inducingRep m hϖ σ
  set E := smoothInduced J Λ
  set k := IsLocalRing.ResidueField (integers F)
  have hBk : B.parabolic k ≠ ⊤ := B.parabolic_ne_top_of_ne_top hB
  -- Iwasawa decomposition of `g⁻¹ y`.
  obtain ⟨u, hu, lam, κ, hκ, hx⟩ := Iwasawa.exists_iwasawa hϖ (g⁻¹ * y)
  set b := u * Iwasawa.torus ϖ lam
  have hb : b ∈ B.parabolic F := by
    apply B.upperTriangularSubgroup_le_parabolic F
    refine (upperTriangularSubgroup (m + 1) F).mul_mem hu.1 ?_
    intro i j hji
    change (Iwasawa.torus ϖ lam).val i j = 0
    rw [Iwasawa.torus_val]
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hji)
  have hκK : κ ∈ maximalCompact (F := F) m := hκ
  let κK : maximalCompact (F := F) m := ⟨κ, hκK⟩
  have hFin : Fintype (B.unipotentSubgroup k) := Fintype.ofFinite _
  refine ⟨B.unipotentSubgroup k, inferInstance, ⟨1⟩, fun γ => ?_, ?_⟩
  · -- the element `g b γ̂ b⁻¹ g⁻¹`
    let γhat : GeneralLinear (m + 1) F := IntegralReduction.lift (integers F) m γ
    have hγ : γhat ∈ B.unipotentSubgroup F :=
      IntegralReduction.lift_mem_unipotentSubgroup (integers F) m B γ.2
    exact ⟨g * (b * γhat * b⁻¹) * g⁻¹,
      ⟨b * γhat * b⁻¹, B.conj_mem_unipotentSubgroup hb hγ, rfl⟩⟩
  · -- reduce to an average of `σ`
    have hterm : ∀ γ : B.unipotentSubgroup k,
        E (g * (b * (IntegralReduction.lift (integers F) m γ : GeneralLinear (m + 1) F) * b⁻¹) *
            g⁻¹) (E y (levelZeroIndicator hϖ σ L hLK hLred v)) =
          E y (levelZeroIndicator hϖ σ L hLK hLred
            (σ (residueReduction m κK)⁻¹ (σ γ (σ (residueReduction m κK) v)))) := by
      intro γ
      set γhat : maximalCompact (F := F) m := IntegralReduction.lift (integers F) m γ
      have hmem : κ⁻¹ * (γhat : GeneralLinear (m + 1) F) * κ ∈ maximalCompact (F := F) m :=
        (maximalCompact m).mul_mem ((maximalCompact m).mul_mem
          ((maximalCompact m).inv_mem hκK) γhat.2) hκK
      have hy : y = g * b * κ := by
        rw [mul_assoc, ← hx, mul_inv_cancel_left]
      have hprod : g * (b * (γhat : GeneralLinear (m + 1) F) * b⁻¹) * g⁻¹ * y =
          y * (κ⁻¹ * (γhat : GeneralLinear (m + 1) F) * κ) := by
        rw [hy]; group
      rw [← Module.End.mul_apply, ← map_mul, hprod, map_mul, Module.End.mul_apply]
      congr 1
      have hJ := maximalCompact_le_inducingSubgroup m ϖ hmem
      have h1 := smoothInduced_indicator J Λ L (openSubgroup_le_inducingSubgroup L hLK)
        (inducingRep_openSubgroup hϖ σ L hLK hLred) ⟨_, hJ⟩ v
      have hred : residueReduction m ⟨κ⁻¹ * (γhat : GeneralLinear (m + 1) F) * κ, hmem⟩ =
          (residueReduction m κK)⁻¹ * γ * residueReduction m κK := by
        have : (⟨κ⁻¹ * (γhat : GeneralLinear (m + 1) F) * κ, hmem⟩ :
            maximalCompact (F := F) m) = κK⁻¹ * γhat * κK := rfl
        rw [this, map_mul, map_mul, map_inv, IntegralReduction.reduction_lift]
      refine h1.trans (congrArg (indicator J Λ L (openSubgroup_le_inducingSubgroup L hLK)
        (inducingRep_openSubgroup hϖ σ L hLK hLred)) ?_)
      rw [inducingRep_of_mem hϖ σ hmem, hred, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply]
    rw [Finset.sum_congr rfl fun γ _ => hterm γ]
    rw [← map_sum, ← map_sum, ← map_sum, cuspidal_sum_eq_zero hσ B hBk, map_zero, map_zero,
      map_zero]

end Langlands.LevelZero
