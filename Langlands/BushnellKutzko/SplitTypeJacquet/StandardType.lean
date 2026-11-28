import Langlands.BushnellKutzko.SplitTypeJacquet.StandardReduction
import Langlands.BushnellKutzko.SplitTypeJacquet.CoarseInjectivity
import Langlands.BushnellKutzko.SplitTypeJacquet.FiniteMackey
import Langlands.Representation.FiniteGeneralLinear.FiniteProductIrreducibles

/-! # The level-zero type of a cuspidal datum on the unit group of a standard order

For a finite cuspidal datum `E` with block shape `B`, the representation `stdType E` of the
unit group `J0 F (blkOf B)` of the standard order is the Levi tensor of `E` inflated through reduction to the
parabolic `P_B(k)`. When no block among the first `j` carries the label of a later block, every
nonzero intertwiner from `stdType E` passes the vanishing test of the coarse injectivity
criterion: the retraction comes from Maschke averaging over `P_B(k)`, and the lower corner terms
vanish by the finite Mackey lemma. -/

open Matrix ValuativeRel Langlands.GeneralLinear Langlands.Geometric Langlands.FiniteGeneralLinear
  Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- Reduction from the unit group of the standard order to the standard parabolic over the
residue field. -/
def redJ0 (B : BlockShape (m + 1)) : J0 F (blkOf B) →* B.parabolic 𝓀[F] :=
  ((red F m).comp (Subgroup.inclusion (J0_le_Kint (blkOf B)))).codRestrict (B.parabolic 𝓀[F])
    (fun g => (red_mem_parabolic_iff _).mpr g.2)

theorem coe_redJ0 (B : BlockShape (m + 1)) (g : J0 F (blkOf B)) :
    (redJ0 B g : GeneralLinear (m + 1) 𝓀[F]) =
      red F m ⟨(g : GL (Fin (m + 1)) F), J0_le_Kint (blkOf B) g.2⟩ := rfl

/-- The type of a cuspidal datum on the unit group of the standard order. -/
def stdType (E : HarishChandraDatum (m + 1) 𝓀[F]) :
    Representation ℂ (J0 F (blkOf E.shape)) E.leviRep :=
  (parabolicRep E).comp (redJ0 E.shape)

theorem leviProjection_eq_one_of_mem_unipotentSubgroup {k : Type*} [Field k] {n : ℕ}
    {B : BlockShape n} (p : B.parabolic k) (hp : (p : GeneralLinear n k) ∈ B.unipotentSubgroup k) :
    B.leviProjection k p = 1 := by
  obtain ⟨q, hq, hqp⟩ := hp
  have : q = p := Subtype.ext hqp
  rw [← this]
  exact hq

theorem stdType_eq_one_of_mem_J1 (E : HarishChandraDatum (m + 1) 𝓀[F])
    (x : J0 F (blkOf E.shape)) (hx : (x : GL (Fin (m + 1)) F) ∈ J1 F (blkOf E.shape)) :
    stdType E x = 1 := by
  change E.leviRep.ρ (E.shape.leviProjection 𝓀[F] (redJ0 E.shape x)) = 1
  have hu : ((redJ0 E.shape x : E.shape.parabolic 𝓀[F]) : GeneralLinear (m + 1) 𝓀[F]) ∈
      E.shape.unipotentSubgroup 𝓀[F] := by
    rw [coe_redJ0]
    exact red_mem_unipotentSubgroup_of_mem_J1 (B := E.shape)
      ⟨(x : GL (Fin (m + 1)) F), J0_le_Kint (blkOf E.shape) x.2⟩ hx
  rw [leviProjection_eq_one_of_mem_unipotentSubgroup _ hu, map_one]

/-- Subrepresentations of a pullback along a surjective homomorphism are those of the
original representation. -/
def subrepCompOrderIso {G H W : Type*} [Monoid G] [Monoid H] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ H W) (f : G →* H) (hf : Function.Surjective f) :
    Subrepresentation (ρ.comp f) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun h v hv => by
    obtain ⟨g, rfl⟩ := hf h
    exact S.apply_mem_toSubmodule g hv⟩
  invFun T := ⟨T.toSubmodule, fun g v hv => T.apply_mem_toSubmodule (f g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The Levi tensor of a cuspidal datum, inflated to the parabolic, is irreducible. -/
theorem isIrreducible_parabolicRep {k : Type*} [Field k] [Finite k] {n : ℕ}
    (E : HarishChandraDatum n k) : Representation.IsIrreducible (parabolicRep E) := by
  classical
  have hL : Representation.IsIrreducible E.leviRep.ρ := by
    let : ∀ i, Fintype (GeneralLinear (E.shape.size i) k) := fun i => Fintype.ofFinite _
    exact FiniteRep.isIrreducible_externalRep _
      (fun i => FiniteRep.VirtualCharacter.isIrreducible_rep _)
  have hsurj : Function.Surjective (E.shape.leviProjection k) := fun l =>
    ⟨E.shape.leviInParabolic k l, by simp⟩
  exact (OrderIso.isSimpleOrder_iff
    (subrepCompOrderIso E.leviRep.ρ (E.shape.leviProjection k) hsurj)).mpr hL

section Corner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {blk : ι → ℕ} {j : ℕ}

omit [ValuativeRel F] in
theorem upperC_apply (Z : Matrix (Late blk j) (Early blk j) F) (p q : ι) :
    ((upperC blk j Z : GL ι F) : Matrix ι ι F) p q = (1 : Matrix ι ι F) p q +
      (if hp : j ≤ blk p then (if hq : j ≤ blk q then 0 else Z ⟨p, hp⟩ ⟨q, hq⟩) else 0) := by
  rw [upperC, coe_coarseReindex_symm_apply, coe_upperHom, coarse_entry (fromBlocks 1 Z 0 1) p q]
  by_cases hp : j ≤ blk p <;> by_cases hq : j ≤ blk q
  · simp only [hp, hq, dite_true, fromBlocks_apply₁₁, add_zero]
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [Matrix.one_apply_ne hpq,
        Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]
  · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₁₂]
    rw [Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hp)), zero_add]
  · simp only [hp, hq, dite_true, dite_false, fromBlocks_apply₂₁, Matrix.zero_apply, add_zero]
    rw [Matrix.one_apply_ne (fun h => hp (by rw [h]; exact hq))]
  · simp only [hp, hq, dite_false, fromBlocks_apply₂₂, add_zero]
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [Matrix.one_apply_ne hpq,
        Matrix.one_apply_ne (fun h => hpq (congrArg Subtype.val h))]

theorem upperC_mem_J0_zero {Z : Matrix (Late blk j) (Early blk j) F}
    (hZ : ∀ a b, valuation F (Z a b) ≤ 1) : upperC blk j Z ∈ J0 F (fun _ : ι => 0) := by
  have key : ∀ Z : Matrix (Late blk j) (Early blk j) F, (∀ a b, valuation F (Z a b) ≤ 1) →
      InOrd (fun _ : ι => 0) ((upperC blk j Z : GL ι F) : Matrix ι ι F) := by
    intro Z hZ p q
    refine ⟨?_, fun h => absurd h (lt_irrefl 0)⟩
    rw [upperC_apply]
    refine Valuation.map_add_le _ (by by_cases hpq : p = q <;> simp [hpq, Matrix.one_apply]) ?_
    by_cases hp : j ≤ blk p
    · by_cases hq : j ≤ blk q
      · simp [hp, hq]
      · simp only [hp, hq, dite_true, dite_false]; exact hZ _ _
    · simp [hp]
  refine ⟨key Z hZ, ?_⟩
  have hinv : (upperC blk j Z)⁻¹ = upperC blk j (-Z) := by
    rw [upperC, upperC, ← map_inv, ← map_inv]
    rfl
  rw [hinv]
  exact key (-Z) fun a b => by simpa using hZ a b

end Corner

section Residue

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem upperC_mem_Kint {B : BlockShape (m + 1)} {j : ℕ}
    {Z : Matrix (Late (blkOf B) j) (Early (blkOf B) j) F} (hZ : ∀ a b, valuation F (Z a b) ≤ 1) :
    upperC (blkOf B) j Z ∈ Kint F m :=
  J0_le_Kint _ (upperC_mem_J0_zero hZ)

/-- The residues of a late-early corner, as a lower corner of the finite group. -/
def resCorner {B : BlockShape (m + 1)} {j : ℕ}
    (Z : Matrix (Late (blkOf B) j) (Early (blkOf B) j) F) : Corner B j 𝓀[F] :=
  fun a b => resF (Z ⟨a.1, by have := a.2; unfold InFirst at this; simp only [blkOf]; omega⟩
    ⟨b.1, by have := b.2; unfold InFirst at this; simp only [blkOf]; omega⟩)

theorem red_upperC {B : BlockShape (m + 1)} {j : ℕ}
    {Z : Matrix (Late (blkOf B) j) (Early (blkOf B) j) F} (hZ : ∀ a b, valuation F (Z a b) ≤ 1) :
    red F m ⟨upperC (blkOf B) j Z, upperC_mem_Kint hZ⟩ = lowerUnip (resCorner Z) := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [red_apply_resF, coe_lowerUnip, Matrix.add_apply, cornerMatrix_apply]
  change resF (((upperC (blkOf B) j Z : GL (Fin (m + 1)) F) : Matrix _ _ F) a b) = _
  rw [upperC_apply]
  have h1 : valuation F ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) F) a b) ≤ 1 := by
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  have hc : valuation F (if hp : j ≤ blkOf B a then (if hq : j ≤ blkOf B b then 0 else
      Z ⟨a, hp⟩ ⟨b, hq⟩) else 0) ≤ 1 := by
    by_cases hp : j ≤ blkOf B a
    · by_cases hq : j ≤ blkOf B b
      · simp [hp, hq]
      · simp only [hp, hq, dite_true, dite_false]; exact hZ _ _
    · simp [hp]
  rw [resF_add h1 hc, resF_one_apply]
  congr 1
  by_cases ha : InFirst B j a
  · have ha' : ¬ j ≤ blkOf B a := by unfold InFirst at ha; simp only [blkOf]; omega
    simp [ha, ha', resF_zero]
  · have ha' : j ≤ blkOf B a := by unfold InFirst at ha; simp only [blkOf]; omega
    by_cases hb : InFirst B j b
    · have hb' : ¬ j ≤ blkOf B b := by unfold InFirst at hb; simp only [blkOf]; omega
      simp [ha, ha', hb, hb', resCorner]
    · have hb' : j ≤ blkOf B b := by unfold InFirst at hb; simp only [blkOf]; omega
      simp [ha, ha', hb, hb', resF_zero]

theorem resCorner_eq_zero_iff {B : BlockShape (m + 1)} {j : ℕ}
    {Z : Matrix (Late (blkOf B) j) (Early (blkOf B) j) F} (hZ : ∀ a b, valuation F (Z a b) ≤ 1) :
    resCorner Z = 0 ↔ ∀ a b, valuation F (Z a b) < 1 := by
  constructor
  · intro h a b
    have := congrFun (congrFun h ⟨a.1, by
      have := a.2; unfold InFirst; simp only [blkOf] at this; omega⟩) ⟨b.1, by
      have := b.2; unfold InFirst; simp only [blkOf] at this; omega⟩
    exact (resF_eq_zero_iff (hZ a b)).mp this
  · intro h
    funext a b
    exact (resF_eq_zero_iff (hZ _ _)).mpr (h _ _)

end Residue

section Test

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (m + 1)) F) V)

/-- **Every nonzero intertwiner from a separated type passes the vanishing test.** -/
theorem stdType_test (E : HarishChandraDatum (m + 1) 𝓀[F]) (j : ℕ)
    (hdisj : ∀ i i' : Fin E.shape.length, (i : ℕ) < j → j ≤ (i' : ℕ) →
      E.blockLabel i ≠ E.blockLabel i')
    (g : E.leviRep →ₗ[ℂ] V)
    (hg : ∀ (x : J0 F (blkOf E.shape)) (w : E.leviRep), g (stdType E x w) = π x (g w))
    (hg0 : g ≠ 0) :
    ∃ ψ : V →ₗ[ℂ] E.leviRep, (∀ w, ψ (g w) = w) ∧
      (∀ h ∈ J1 F (blkOf E.shape), ∀ Z : Matrix (Late (blkOf E.shape) j)
          (Early (blkOf E.shape) j) F, (∀ a b, valuation F (Z a b) ≤ 1) → ∀ w,
        ψ (π h (π (upperC (blkOf E.shape) j Z) (g w))) =
          ψ (π (upperC (blkOf E.shape) j Z) (g w))) ∧
      (∀ Z : Matrix (Late (blkOf E.shape) j) (Early (blkOf E.shape) j) F,
        (∀ a b, valuation F (Z a b) ≤ 1) → (¬ ∀ a b, valuation F (Z a b) < 1) → ∀ w,
          ψ (π (upperC (blkOf E.shape) j Z) (g w)) = 0) := by
  classical
  -- the values of `g` are fixed by the principal congruence subgroup
  have hfix : ∀ w, g w ∈ fixK1 π := by
    intro w
    rw [mem_fixK1_iff]
    intro k hk
    have hkJ1 : k ∈ J1 F (blkOf E.shape) := principalLevel_one_le_J1 _ hk
    rw [← hg ⟨k, J1_le_J0 hkJ1⟩, stdType_eq_one_of_mem_J1 E _ hkJ1]
    rfl
  let gb : E.leviRep →ₗ[ℂ] fixK1 π := g.codRestrict (fixK1 π) hfix
  have hgb : ∀ w, (gb w : V) = g w := fun w => rfl
  -- equivariance for the parabolic over the residue field
  have hP : ∀ q : E.shape.parabolic 𝓀[F],
      gb ∘ₗ parabolicRep E q = descended π (q : GeneralLinear (m + 1) 𝓀[F]) ∘ₗ gb := by
    intro q
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    let x : Kint F m := IntegralReduction.lift (ValuativeRel.valuation F).integer m q
    have hxred : red F m x = q :=
      IntegralReduction.reduction_lift (ValuativeRel.valuation F).integer m q
    have hxJ : (x : GL (Fin (m + 1)) F) ∈ J0 F (blkOf E.shape) :=
      (red_mem_parabolic_iff x).mp (by rw [hxred]; exact q.2)
    have e1 : stdType E ⟨x, hxJ⟩ = parabolicRep E q := by
      change parabolicRep E (redJ0 E.shape ⟨x, hxJ⟩) = _
      congr 1
      apply Subtype.ext
      rw [coe_redJ0]
      exact hxred
    change g (parabolicRep E q w) = ((descended π (q : GeneralLinear (m + 1) 𝓀[F]) (gb w) :
      fixK1 π) : V)
    rw [← e1, hg, ← hxred, descended_red]
    rfl
  -- injectivity
  have hinj : Function.Injective gb := by
    let I : Representation.IntertwiningMap (parabolicRep E)
        ((descended π).comp (E.shape.parabolic 𝓀[F]).subtype) :=
      ⟨gb, fun q => hP q⟩
    have := isIrreducible_parabolicRep E
    rcases Representation.IsIrreducible.injective_or_eq_zero I with h | h
    · exact h
    · exfalso
      apply hg0
      apply LinearMap.ext
      intro w
      have hw : (I w : fixK1 π) = 0 := by rw [h]; rfl
      have hw' : ((I w : fixK1 π) : V) = 0 := by rw [hw]; rfl
      rw [LinearMap.zero_apply]
      exact hw'
  -- Maschke averaging over the finite parabolic
  obtain ⟨ψ0, hψ0, hψ0f⟩ := exists_equivariant_leftInverse (parabolicRep E)
    ((descended π).comp (E.shape.parabolic 𝓀[F]).subtype) gb hP hinj
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend ψ0
  have hψx : ∀ x : fixK1 π, ψ (x : V) = ψ0 x := fun x => LinearMap.congr_fun hψ x
  refine ⟨ψ, fun w => ?_, fun h hh Z hZ w => ?_, fun Z hZ hZlt w => ?_⟩
  · rw [← hgb, hψx]
    exact LinearMap.congr_fun hψ0f w
  · have hKZ := upperC_mem_Kint (B := E.shape) (j := j) hZ
    let y : fixK1 π := ⟨π (upperC (blkOf E.shape) j Z) (g w), apply_mem_fixK1 π hKZ (hfix w)⟩
    have hhK : h ∈ Kint F m := J0_le_Kint _ (J1_le_J0 hh)
    have e1 : π h (y : V) = ((descended π (red F m ⟨h, hhK⟩) y : fixK1 π) : V) :=
      (descended_red π ⟨h, hhK⟩ y).symm
    have hpar : red F m ⟨h, hhK⟩ ∈ E.shape.parabolic 𝓀[F] :=
      (red_mem_parabolic_iff _).mpr (J1_le_J0 hh)
    have hunip : red F m ⟨h, hhK⟩ ∈ E.shape.unipotentSubgroup 𝓀[F] :=
      red_mem_unipotentSubgroup_of_mem_J1 ⟨h, hhK⟩ hh
    change ψ (π h (y : V)) = ψ (y : V)
    rw [e1, hψx, hψx]
    have := LinearMap.congr_fun (hψ0 ⟨_, hpar⟩) y
    simp only [LinearMap.comp_apply] at this
    refine this.trans ?_
    change E.leviRep.ρ (E.shape.leviProjection 𝓀[F] ⟨_, hpar⟩) (ψ0 y) = ψ0 y
    rw [leviProjection_eq_one_of_mem_unipotentSubgroup _ hunip, map_one]
    rfl
  · have hKZ := upperC_mem_Kint (B := E.shape) (j := j) hZ
    have hY : resCorner (B := E.shape) Z ≠ 0 := fun h => hZlt ((resCorner_eq_zero_iff hZ).mp h)
    have e1 : π (upperC (blkOf E.shape) j Z) (g w) =
        ((descended π (lowerUnip (resCorner Z)) (gb w) : fixK1 π) : V) := by
      rw [← red_upperC hZ, descended_red]
      rfl
    rw [e1, hψx]
    have := retraction_lowerUnip_eq_zero E j hdisj (descended π) gb hP ψ0 hψ0 _ hY
    exact LinearMap.congr_fun this w

end Test

end Langlands.BushnellKutzko.SplitTypeJacquet
