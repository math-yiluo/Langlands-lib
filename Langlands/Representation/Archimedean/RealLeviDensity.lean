import Langlands.Representation.Archimedean.RealLeviProducts

/-!
# Density over the classes of a block diagonal Levi subgroup

States and proves `RealLeviDensityStatement`. If every twisted class standard module is
irreducible, a proper `(𝔤𝔩_N, O(N))`-stable subspace of the standard module of a concatenated
list has an annihilator in the dual principal series. On the compact Levi subgroup, its jointly
allowed iterated block Fourier coefficients are those of any prescribed product of class vectors.
Internal infrastructure for Task 6749; see `RealLeviDensity.md`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealLeviDensity

open RealLeviChart RealLeviSlices RealLeviProducts RealInducedBlockBound RealInducedTorusCore
  RealInducedTorusReduction RealInducedStandardBound

/-! ## Modes along concatenated slot lists -/

section Modes

variable {N : ℕ}

/-- The block and the weight of a slot. -/
def key (s : Slot N) : ℕ × ℕ := (s.p, s.M)

/-- The block, the weight and the mode of a slot. -/
def key3 (s : Slot N) : ℕ × ℕ × ℤ := (s.p, s.M, s.j)

theorem withModes_append : ∀ (A B : List (Slot N)) (J J' : List ℤ), J.length = A.length →
    withModes (A ++ B) (J ++ J') = withModes A J ++ withModes B J'
  | [], B, [], J', _ => by simp [withModes]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | s :: A, B, j :: J, J', h => by
    simp only [List.cons_append, withModes]
    rw [withModes_append A B J J' (by simpa using h)]

/-- Slot lists with the same blocks and weights carry the same blocks, weights and modes after
setting the modes. -/
theorem map_key3_withModes : ∀ (L L' : List (Slot N)) (J : List ℤ),
    L.map key = L'.map key → (withModes L J).map key3 = (withModes L' J).map key3
  | [], [], _, _ => by simp [withModes]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: _, _ :: _, [], _ => by simp [withModes]
  | s :: L, t :: L', j :: J, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [withModes, List.map_cons, map_key3_withModes L L' J h.2, List.cons.injEq,
      and_true]
    simp only [key, Prod.mk.injEq] at h
    simp [key3, setMode, h.1.1, h.1.2]

theorem allowed_of_map_key3 {L L' : List (Slot N)} (h : L.map key3 = L'.map key3)
    (hL : ∀ t ∈ L, (t.M : ℤ) ≤ |t.j|) : ∀ t ∈ L', (t.M : ℤ) ≤ |t.j| := by
  intro t ht
  have hmem : key3 t ∈ L.map key3 := by
    rw [h]
    exact List.mem_map_of_mem ht
  obtain ⟨t', ht', e⟩ := List.mem_map.mp hmem
  simp only [key3, Prod.mk.injEq] at e
  rw [← e.2.1, ← e.2.2]
  exact hL t' ht'

theorem coeffs_congr_key3 {L L' : List (Slot N)} (h : L.map key3 = L'.map key3)
    (F : Langlands.GeneralLinear N ℝ → ℂ) : coeffs L F = coeffs L' F := by
  refine coeffs_congr_map L L' ?_ F
  have := congrArg (List.map fun x : ℕ × ℕ × ℤ => (x.1, x.2.2)) h
  simpa only [List.map_map, Function.comp_def, key3] using this

end Modes

/-! ## Lifted slot lists -/

section Lift

variable {c : ℕ} {sz : Fin c → ℕ}

theorem withModes_map_liftSlot (i : Fin c) : ∀ (L : List (Slot (sz i))) (J : List ℤ),
    withModes (L.map (liftSlot sz i)) J = (withModes L J).map (liftSlot sz i)
  | [], _ => by simp [withModes]
  | _ :: _, [] => by simp [withModes]
  | s :: L, j :: J => by
    simp only [List.map_cons, withModes]
    rw [withModes_map_liftSlot i L J]
    rfl

theorem withModes_globalSlots (Ls : ∀ i, List (Slot (sz i))) (Js : Fin c → List ℤ) :
    ∀ l : List (Fin c), (∀ i ∈ l, (Js i).length = (Ls i).length) →
      withModes (globalSlots Ls l) (l.map Js).flatten =
        globalSlots (fun i => withModes (Ls i) (Js i)) l
  | [], _ => by simp [globalSlots, withModes]
  | i :: l, h => by
    have ih := withModes_globalSlots Ls Js l fun j hj => h j (List.mem_cons_of_mem _ hj)
    simp only [globalSlots] at ih ⊢
    simp only [List.map_cons, List.flatten_cons]
    rw [withModes_append _ _ _ _ (by rw [List.length_map]; exact h i List.mem_cons_self),
      withModes_map_liftSlot, ih]

theorem length_globalSlots (Ls : ∀ i, List (Slot (sz i))) :
    (globalSlots Ls (List.finRange c)).length = ∑ i, (Ls i).length := by
  simp only [globalSlots, List.length_flatten, List.map_map, Function.comp_def, List.length_map]
  rw [Fin.sum_univ_def]

theorem liftSlot_mem_globalSlots (Ls : ∀ i, List (Slot (sz i))) {l : List (Fin c)} {i : Fin c}
    (hi : i ∈ l) {t : Slot (sz i)} (ht : t ∈ Ls i) : liftSlot sz i t ∈ globalSlots Ls l := by
  simp only [globalSlots, List.mem_flatten, List.mem_map]
  exact ⟨_, ⟨i, hi, rfl⟩, List.mem_map_of_mem ht⟩

/-- A list of length `∑_i ls_i` is the concatenation of lists of lengths `ls_i`. -/
theorem exists_split : ∀ {c : ℕ} (ls : Fin c → ℕ) (J : List ℤ), J.length = ∑ i, ls i →
    ∃ Js : Fin c → List ℤ, (∀ i, (Js i).length = ls i) ∧ J = (List.ofFn Js).flatten
  | 0, _, J, h => ⟨fun i => i.elim0, fun i => i.elim0, by simpa using h⟩
  | c + 1, ls, J, h => by
    rw [Fin.sum_univ_succ] at h
    obtain ⟨Js, hJs, e⟩ := exists_split (fun i => ls i.succ) (J.drop (ls 0))
      (by rw [List.length_drop, h]; omega)
    refine ⟨(Fin.cons (J.take (ls 0)) Js : Fin (c + 1) → List ℤ), fun i => ?_, ?_⟩
    · induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, List.length_take, h]
        omega
      | succ i => simp only [Fin.cons_succ, hJs]
    · rw [List.ofFn_succ, Fin.cons_zero, List.flatten_cons]
      simp only [Fin.cons_succ]
      rw [← e, List.take_append_drop]

end Lift

/-! ## Blocks and weights of the slots of a concatenated list -/

section Keys

theorem map_key_slots (ds : List RealBlock) {N : ℕ} (h : realRank ds ≤ N) :
    (slots ds N).map key = (List.range N).filterMap fun p =>
      (realInducedBlockAt ds p).map fun d => (p, d.weight.natAbs) := by
  unfold slots
  rw [List.map_filterMap]
  refine List.filterMap_congr fun p _ => ?_
  rcases hd : realInducedBlockAt ds p with _ | d
  · simp [slotAt, hd]
  · have hp : p + 1 < N := lt_of_lt_of_le (realInducedBlockAt_lt hd) h
    simp [slotAt, hd, hp, key, mkSlot]

theorem range_sum : ∀ {c : ℕ} (sz : Fin c → ℕ), List.range (∑ j, sz j) =
    ((List.finRange c).map fun i => (List.range (sz i)).map (start sz i + ·)).flatten
  | 0, _ => by simp
  | c + 1, sz => by
    rw [Fin.sum_univ_succ, List.range_add, List.finRange_succ, List.map_cons, List.flatten_cons,
      range_sum (fun i => sz i.succ), List.map_flatten]
    simp only [List.map_map]
    congr 1
    · simp [start_zero']
    · congr 1
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      simp only [Function.comp_apply, Fin.val_succ, start_succ']
      omega

variable {c : ℕ}

/-- The slots of the concatenated list have the blocks and weights of the lifted slots of the
twisted class lists. -/
theorem map_key_flat (dss : Fin c → List RealBlock) :
    (slots (flat dss) (∑ j, sz dss j)).map key =
      (globalSlots (fun i => slots (cl dss i) (sz dss i)) (List.finRange c)).map key := by
  rw [map_key_slots _ (realRank_flat dss).le, range_sum, List.filterMap_flatten, globalSlots,
    List.map_flatten]
  simp only [List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, List.filterMap_map]
  have e : List.map key (List.map (liftSlot (sz dss) i) (slots (cl dss i) (sz dss i))) =
      List.map (fun x : ℕ × ℕ => (start (sz dss) i + x.1, x.2))
        ((slots (cl dss i) (sz dss i)).map key) := by
    simp only [List.map_map]
    rfl
  rw [e, map_key_slots _ (realRank_cl dss i).le, List.map_filterMap]
  refine List.filterMap_congr fun p hp => ?_
  rw [List.mem_range] at hp
  rw [realInducedBlockAt_flat dss i p hp, cl, realInducedBlockAt_twist]
  cases realInducedBlockAt (dss i) p <;> simp

theorem length_slots_flat (dss : Fin c → List RealBlock) :
    (slots (flat dss) (∑ j, sz dss j)).length = ∑ i, (slots (cl dss i) (sz dss i)).length := by
  have := congrArg List.length (map_key_flat dss)
  rw [List.length_map, List.length_map, length_globalSlots] at this
  exact this

theorem map_key3_flat (dss : Fin c → List RealBlock) (Js : Fin c → List ℤ)
    (hJs : ∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length) :
    (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten).map key3 =
      (globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i))
        (List.finRange c)).map key3 := by
  rw [map_key3_withModes _ _ _ (map_key_flat dss), List.ofFn_eq_map,
    withModes_globalSlots _ _ _ fun i _ => hJs i]

end Keys

/-! ## Coefficients of the dual space -/

section Coeffs

open RealPrincipalSeriesDuality RealLeviDuality

variable {N : ℕ}

theorem coeffs_add {F G : Langlands.GeneralLinear N ℝ → ℂ} (hF : Continuous F)
    (hG : Continuous G) : ∀ (L : List (Slot N)) (g : Langlands.GeneralLinear N ℝ),
      coeffs L (F + G) g = coeffs L F g + coeffs L G g
  | [], _ => rfl
  | s :: L, g => by
    simp only [coeffs]
    rw [show coeffs L (F + G) = coeffs L F + coeffs L G from
      funext fun x => coeffs_add hF hG L x]
    unfold blockFourierCoefficient
    simp only [Pi.add_apply, add_mul]
    exact intervalIntegral.integral_add
      (intervalIntegrable_blockFourier (continuous_coeffs hF L) s.p s.j g 0 (2 * Real.pi))
      (intervalIntegrable_blockFourier (continuous_coeffs hG L) s.p s.j g 0 (2 * Real.pi))

/-- The coefficient `v ↦ coeffs L v 1` on the dual space. -/
def muC (ds : List RealBlock) (L : List (Slot N)) : DualSpace N ds →ₗ[ℂ] ℂ where
  toFun v := coeffs L v 1
  map_add' v w := by
    rw [Submodule.coe_add]
    exact coeffs_add (continuous_of_mem_dualSpace v.2) (continuous_of_mem_dualSpace w.2) L 1
  map_smul' r v := by
    rw [Submodule.coe_smul]
    exact coeffs_const_mul r L v 1

theorem muC_apply (ds : List RealBlock) (L : List (Slot N)) (v : DualSpace N ds) :
    muC ds L v = coeffs L v 1 :=
  rfl

variable {ds : List RealBlock}

theorem coeffs_eq_zero_of_mem_nullSpace (hN : realRank ds = N)
    {v : DualSpace N ds} (hv : v ∈ nullSpace N ds) {J : List ℤ}
    (hJ : J.length = (slots ds N).length)
    (hall : ∀ t ∈ withModes (slots ds N) J, (t.M : ℤ) ≤ |t.j|)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    coeffs (withModes (slots ds N) J) v k = 0 :=
  RealLeviModes.isNull_of_annihilates hN v.2 hv J hJ hall k hk

theorem coeffs_eq_mul_of_sub_mem (hN : realRank ds = N)
    {v φ : DualSpace N ds} {r : ℂ} (hv : v - r • φ ∈ nullSpace N ds) {J : List ℤ}
    (hJ : J.length = (slots ds N).length)
    (hall : ∀ t ∈ withModes (slots ds N) J, (t.M : ℤ) ≤ |t.j|)
    {k : Langlands.GeneralLinear N ℝ} (hk : k ∈ unitaryCompact ℝ N) :
    coeffs (withModes (slots ds N) J) v k = r * coeffs (withModes (slots ds N) J) φ k := by
  have e : (v : Langlands.GeneralLinear N ℝ → ℂ) =
      ((v - r • φ : DualSpace N ds) : Langlands.GeneralLinear N ℝ → ℂ) +
        fun x => r * (φ : Langlands.GeneralLinear N ℝ → ℂ) x := by
    funext x
    simp
  rw [e, coeffs_add (G := fun x => r * (φ : Langlands.GeneralLinear N ℝ → ℂ) x)
    (continuous_of_mem_dualSpace (v - r • φ).2)
    (continuous_const.mul (continuous_of_mem_dualSpace φ.2)), coeffs_const_mul,
    coeffs_eq_zero_of_mem_nullSpace hN hv hJ hall hk, zero_add]

end Coeffs

/-! ## Annihilators of subspaces of the standard module -/

section Ann

open RealPrincipalSeriesDuality RealLeviDuality PartialJacquet

attribute [local instance] measurableSpaceK

variable {N : ℕ} {ds : List RealBlock}

/-- The annihilator in the dual space of a subspace `W` of the standard module. -/
def annW (W : Submodule ℂ (StdSpace N ds)) : Submodule ℂ (DualSpace N ds) :=
  annihilator N ds (Subtype.val '' (W : Set (StdSpace N ds))) (by
    rintro _ ⟨w, _, rfl⟩
    exact continuous_of_mem_stdSpace w.2)

theorem mem_annW {W : Submodule ℂ (StdSpace N ds)} {v : DualSpace N ds} :
    v ∈ annW W ↔ ∀ w ∈ W, ∫ κ : unitaryCompact ℝ N,
      (v : Langlands.GeneralLinear N ℝ → ℂ) κ * (w : Langlands.GeneralLinear N ℝ → ℂ) κ
        ∂haarK N = 0 :=
  ⟨fun h w hw => h _ ⟨w, hw, rfl⟩, fun h _ ⟨w, hw, e⟩ => e ▸ h w hw⟩

theorem annW_rep {W : Submodule ℂ (StdSpace N ds)}
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin N) ℝ), ∀ w ∈ W, realStandardRep N ds k w ∈ W)
    (k : Matrix.unitaryGroup (Fin N) ℝ) {v : DualSpace N ds} (hv : v ∈ annW W) :
    principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)) k v ∈ annW W := by
  rw [mem_annW] at hv ⊢
  intro w hw
  rw [principalSeriesRep_apply_coe]
  have hk : (Unitary.toUnits k : Langlands.GeneralLinear N ℝ) ∈ unitaryCompact ℝ N := k.2
  rw [integral_rightTranslation_mul _ _ hk]
  have h := hv _ (hWK k⁻¹ w hw)
  have e : ((realStandardRep N ds k⁻¹ w : StdSpace N ds) : Langlands.GeneralLinear N ℝ → ℂ) =
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear N ℝ)
        (Unitary.toUnits k : Langlands.GeneralLinear N ℝ)⁻¹
        (w : Langlands.GeneralLinear N ℝ → ℂ) := by
    rw [← map_inv]
    rfl
  rw [e] at h
  exact h

theorem annW_lie {W : Submodule ℂ (StdSpace N ds)}
    (hWL : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ), ∀ w ∈ W, realStandardLie N ds X w ∈ W)
    (X : ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ) {v : DualSpace N ds} (hv : v ∈ annW W) :
    principalSeriesLie ℝ N (dualChar (realPositionCharacter ds)) X v ∈ annW W := by
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  induction X using TensorProduct.inductionOn with
  | tmul z Y =>
    rw [mem_annW] at hv ⊢
    intro w hw
    rw [coe_principalSeriesLie_tmul]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_rightDerivative_mul hχ v.2.1 w.2.1.1 Y]
    have h := hv _ (hWL ((1 : ℂ) ⊗ₜ Y) w hw)
    rw [coe_realStandardLie_tmul, one_smul] at h
    rw [h, neg_zero, mul_zero]
  | add X Y hX hY =>
    rw [map_add, LinearMap.add_apply]
    exact (annW W).add_mem hX hY

end Ann

/-! ## Density in one class -/

section Class

open RealPrincipalSeriesDuality RealLeviDuality PartialJacquet

variable {N : ℕ} {ds : List RealBlock}

/-- **Density in one class.** If the standard module is irreducible, for finitely many `w_a` of
the dual space and every `φ` some element `b` of the free algebra on `O(N)` and
`ℂ ⊗ 𝔤𝔩_N(ℝ)` maps every `w_a` to `μ(w_a) φ` modulo the annihilator of the standard module,
where `μ(v)` is the iterated coefficient of `v` at `1` for jointly allowed modes. -/
theorem exists_class_density (hN : realRank ds = N)
    (hX : IsIrreducibleGKModule (realStandardRep N ds) (realStandardLie N ds))
    {J : List ℤ} (hJ : J.length = (slots ds N).length)
    (hall : ∀ t ∈ withModes (slots ds N) J, (t.M : ℤ) ≤ |t.j|)
    {n : ℕ} (w : Fin n → DualSpace N ds) (φ : DualSpace N ds) :
    ∃ b : FreeAlgebra ℂ (Matrix.unitaryGroup (Fin N) ℝ ⊕ (ℂ ⊗[ℝ] Matrix (Fin N) (Fin N) ℝ)),
      ∀ a, FreeAlgebra.lift ℂ (GKModuleDensity.gens
          (principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)))
          (principalSeriesLie ℝ N (dualChar (realPositionCharacter ds)))) b (w a) -
        muC ds (withModes (slots ds N) J) (w a) • φ ∈ nullSpace N ds := by
  classical
  have hμ : nullSpace N ds ≤ LinearMap.ker (muC ds (withModes (slots ds N) J)) := fun v hv =>
    coeffs_eq_zero_of_mem_nullSpace hN hv hJ hall (one_mem _)
  let f : Module.End ℂ (Zq N ds) :=
    ((nullSpace N ds).liftQ (muC ds (withModes (slots ds N) J)) hμ).smulRight
      ((nullSpace N ds).mkQ φ)
  obtain ⟨b, hb⟩ := GKModuleDensity.exists_freeAlgebra_eq (hyp_z N ds hN hX)
    (Finset.univ.image fun a => (nullSpace N ds).mkQ (w a)) f
  refine ⟨b, fun a => ?_⟩
  have hint := lift_intertwine (nullSpace N ds).mkQ
    (GKModuleDensity.gens (principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)))
      (principalSeriesLie ℝ N (dualChar (realPositionCharacter ds))))
    (GKModuleDensity.gens (zRep N ds) (zLie N ds))
    (fun x v => by rcases x with k | X <;> rfl) b (w a)
  have h1 := hb _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  have h2 : f ((nullSpace N ds).mkQ (w a)) =
      muC ds (withModes (slots ds N) J) (w a) • (nullSpace N ds).mkQ φ := by
    simp [f]
  have h3 : (nullSpace N ds).mkQ (FreeAlgebra.lift ℂ (GKModuleDensity.gens
      (principalSeriesRep ℝ N (dualChar (realPositionCharacter ds)))
      (principalSeriesLie ℝ N (dualChar (realPositionCharacter ds)))) b (w a) -
        muC ds (withModes (slots ds N) J) (w a) • φ) = 0 := by
    rw [map_sub, map_smul, hint, h1, h2, sub_self]
  exact (Submodule.Quotient.mk_eq_zero _).mp h3

end Class

/-! ## Density over all classes -/

section Main

open RealPrincipalSeriesDuality RealLeviDuality PartialJacquet

attribute [local instance] measurableSpaceK

variable {c : ℕ} {dss : Fin c → List RealBlock}

theorem gensG_mem_annW {W : Submodule ℂ (StdSpace (∑ j, sz dss j) (flat dss))}
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardRep (∑ j, sz dss j) (flat dss) k w ∈ W)
    (hWL : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardLie (∑ j, sz dss j) (flat dss) X w ∈ W)
    (i : Fin c) (x : Gens dss i) {v : DualSpace (∑ j, sz dss j) (flat dss)}
    (hv : v ∈ annW W) : gensG dss i x v ∈ annW W := by
  rcases x with k | X
  · rw [gensG_inl]
    exact annW_rep hWK _ hv
  · rw [gensG_inr]
    exact annW_lie hWL _ hv

/-- Product forms whose factors are multiples of `φ_j` modulo the annihilators have the product
coefficients of the `φ_j`. -/
theorem coeffs_globalSlots_of_sub_mem {u : DualSpace (∑ j, sz dss j) (flat dss)} {n : ℕ}
    {C : Fin n → ℂ} {v : Fin n → ∀ j, DualSpace (sz dss j) (cl dss j)}
    (hu : IsProdForm (sz dss) u C fun a j => (v a j : Langlands.GeneralLinear (sz dss j) ℝ → ℂ))
    {r : Fin n → Fin c → ℂ} {φ : ∀ j, DualSpace (sz dss j) (cl dss j)}
    (hv : ∀ a j, v a j - r a j • φ j ∈ nullSpace (sz dss j) (cl dss j))
    {Js : Fin c → List ℤ} (hJs : ∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length)
    (hall : ∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j|)
    {κ : ∀ j, Langlands.GeneralLinear (sz dss j) ℝ}
    (hκ : ∀ j, κ j ∈ unitaryCompact ℝ (sz dss j)) :
    coeffs (globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i))
        (List.finRange c)) u (blockDiagGL (sz dss) κ) =
      (∑ a, C a * ∏ j, r a j) *
        ∏ j, coeffs (withModes (slots (cl dss j) (sz dss j)) (Js j)) (φ j) (κ j) := by
  rw [coeffs_globalSlots hu (fun a j => continuous_of_mem_dualSpace (v a j).2) _ hκ,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  exact coeffs_eq_mul_of_sub_mem (realRank_cl dss j) (hv a j) (hJs j) (hall j) (hκ j)

/-- **Density over all classes.** If every class standard module is irreducible, for every
family `φ_i` of the class dual spaces and every proper `(𝔤𝔩_N, O(N))`-stable subspace `W` of
the standard module of the concatenated list, some `u` of the global dual space annihilates `W`
and has the jointly allowed coefficients of `⊗_i φ_i` on `∏_i O(sz_i)`. -/
theorem exists_density
    (hX : ∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i)))
    (φ : ∀ i, DualSpace (sz dss i) (cl dss i))
    (W : Submodule ℂ (StdSpace (∑ j, sz dss j) (flat dss)))
    (hWK : ∀ (k : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardRep (∑ j, sz dss j) (flat dss) k w ∈ W)
    (hWL : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardLie (∑ j, sz dss j) (flat dss) X w ∈ W)
    (hW : W ≠ ⊤) :
    ∃ u : DualSpace (∑ j, sz dss j) (flat dss), u ∈ annW W ∧
      ∀ Js : Fin c → List ℤ, (∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length) →
        (∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j|) →
        ∀ κ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ,
          (∀ i, κ i ∈ unitaryCompact ℝ (sz dss i)) →
          coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten) u
              (blockDiagGL (sz dss) κ) =
            ∏ i, coeffs (withModes (slots (cl dss i) (sz dss i)) (Js i)) (φ i) (κ i) := by
  classical
  -- a vector of the annihilator of `W` which is not null
  obtain ⟨u0, hu0, hu0W, x, hx, hux⟩ := exists_annihilator_not_null W hWK hW
  have hnn : ¬ RealLeviModes.IsNull (slots (flat dss) (∑ j, sz dss j)) u0 := fun h =>
    hux (RealLeviModes.integral_mul_eq_zero_of_mem_standard hu0 h hx)
  unfold RealLeviModes.IsNull at hnn
  push Not at hnn
  obtain ⟨J, hJlen, hJall, k, hk, hne⟩ := hnn
  obtain ⟨Js, hJs, rfl⟩ := exists_split (fun i => (slots (cl dss i) (sz dss i)).length) J
    (hJlen.trans (length_slots_flat dss))
  have h3 := map_key3_flat dss Js hJs
  have hJsall : ∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i),
      (t.M : ℤ) ≤ |t.j| := fun i t ht =>
    allowed_of_map_key3 h3 hJall _
      (liftSlot_mem_globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i))
        (List.mem_finRange i) ht)
  -- translate the nonzero coefficient to `1`
  let m : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ :=
    ⟨(k : Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ), hk⟩
  let u1 : DualSpace (∑ j, sz dss j) (flat dss) := repG dss m ⟨u0, hu0⟩
  have hu1W : u1 ∈ annW W := annW_rep hWK m (mem_annW.mpr hu0W)
  have hu1 : (u1 : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) = fun y => u0 (y * k) := by
    show Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (∑ j, sz dss j) ℝ)
      (Unitary.toUnits m) u0 = _
    rw [toUnits_mk k hk]
    rfl
  have hc1 : coeffs (globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i))
      (List.finRange c)) u1 1 ≠ 0 := by
    rw [← coeffs_congr_key3 h3, hu1, ← coeffs_mul_right, one_mul]
    exact hne
  -- product form and density in every class
  obtain ⟨n, C, w, hw⟩ := exists_isProdForm u1
  have hb := fun i => exists_class_density (realRank_cl dss i) (hX i) (hJs i) (hJsall i)
    (fun a => w a i) (φ i)
  choose b hb using hb
  have hstar : IsProdForm (sz dss) (applyAll b (List.finRange c) u1) C fun a j =>
      ((FreeAlgebra.lift ℂ (GKModuleDensity.gens (repC dss j) (lieC dss j)) (b j) (w a j) :
        DualSpace (sz dss j) (cl dss j)) : Langlands.GeneralLinear (sz dss j) ℝ → ℂ) := by
    have := isProdForm_applyAll hw b (List.finRange c) (List.nodup_finRange c)
    simpa only [List.mem_finRange, ↓reduceIte] using this
  have hstarW : applyAll b (List.finRange c) u1 ∈ annW W :=
    applyAll_mem b (annW W) (fun i x _ hv => gensG_mem_annW hWK hWL i x hv) _ hu1W
  -- the constant
  set Cst : ℂ := ∑ a, C a * ∏ j, muC (cl dss j)
    (withModes (slots (cl dss j) (sz dss j)) (Js j)) (w a j) with hCst
  have hC1 : coeffs (globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i))
      (List.finRange c)) u1 1 = Cst := by
    have e := coeffs_globalSlots hw (fun a j => continuous_of_mem_dualSpace (w a j).2)
      (fun i => withModes (slots (cl dss i) (sz dss i)) (Js i)) (κ := fun _ => 1)
      (fun _ => one_mem _)
    have h1 : blockDiagGL (sz dss) (fun _ => 1) = 1 := map_one _
    rw [h1] at e
    rw [e, hCst]
    rfl
  have hCne : Cst ≠ 0 := hC1 ▸ hc1
  refine ⟨Cst⁻¹ • applyAll b (List.finRange c) u1, (annW W).smul_mem _ hstarW,
    fun Js' hJs' hall' κ hκ => ?_⟩
  rw [coeffs_congr_key3 (map_key3_flat dss Js' hJs'), Submodule.coe_smul]
  have e1 := coeffs_const_mul Cst⁻¹
    (globalSlots (fun i => withModes (slots (cl dss i) (sz dss i)) (Js' i)) (List.finRange c))
    (applyAll b (List.finRange c) u1 : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ)
    (blockDiagGL (sz dss) κ)
  refine e1.trans ?_
  rw [coeffs_globalSlots_of_sub_mem hstar (fun a j => hb j a) hJs' hall' hκ, ← mul_assoc,
    inv_mul_cancel₀ hCne, one_mul]

end Main

end RealLeviDensity

open RealPrincipalSeriesDuality RealInducedStandardBound PartialJacquet RealLeviChart
  RealLeviSlices RealInducedBlockBound RealInducedTorusCore in
attribute [local instance] measurableSpaceK in
/-- **Density over the classes of a block diagonal Levi subgroup.** Let `dss_0, …, dss_{c-1}`
be lists of real blocks of ranks `sz_i`, `N = ∑_i sz_i`, `ds = dss_0 ++ ⋯ ++ dss_{c-1}`, and
let `cl_i = |·|^{s_i} ⊗ dss_i` be the class lists twisted by
`s_i = (sz_0 + ⋯ + sz_{i-1}) - (N - sz_i)/2`. Assume every class standard module `X_i` (of
`cl_i`) is irreducible. Then for every family `φ_i` of `O(sz_i)`-finite functions of the
principal series of the inverse position characters of `cl_i` and every proper subspace `W` of
the `O(N)`-finite standard module of `ds` stable under `O(N)` and `ℂ ⊗ 𝔤𝔩_N(ℝ)`, there is an
`O(N)`-finite function `u` of the principal series of the inverse position characters of `ds`
with `∫_{O(N)} u w = 0` for all `w ∈ W` whose iterated block Fourier coefficients along the
induction slots of `ds` at every `diag(κ_0, …, κ_{c-1})`, `κ_i ∈ O(sz_i)`, are the products
`∏_i` of the coefficients of `φ_i` at `κ_i` along the induction slots of `cl_i`, for all modes
`Js_i` (one list per class, concatenated in the order of the classes) that are jointly allowed
(`|j| ≥ m` at every slot of weight `m`). -/
def RealLeviDensityStatement : Prop :=
  ∀ (c : ℕ) (dss : Fin c → List RealBlock),
    (∀ i, IsIrreducibleGKModule (realStandardRep (sz dss i) (cl dss i))
      (realStandardLie (sz dss i) (cl dss i))) →
    ∀ φ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ → ℂ,
    (∀ i, φ i ∈ kFiniteFunctions (principalSeries ℝ (sz dss i)
      (dualChar (realPositionCharacter (cl dss i)))) (unitaryCompact ℝ (sz dss i))) →
    ∀ W : Submodule ℂ (kFiniteFunctions (realStandardModule (∑ j, sz dss j) (flat dss))
      (unitaryCompact ℝ (∑ j, sz dss j))),
    (∀ (k : Matrix.unitaryGroup (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardRep (∑ j, sz dss j) (flat dss) k w ∈ W) →
    (∀ (X : ℂ ⊗[ℝ] Matrix (Fin (∑ j, sz dss j)) (Fin (∑ j, sz dss j)) ℝ), ∀ w ∈ W,
      realStandardLie (∑ j, sz dss j) (flat dss) X w ∈ W) →
    W ≠ ⊤ →
    ∃ u ∈ kFiniteFunctions (principalSeries ℝ (∑ j, sz dss j)
        (dualChar (realPositionCharacter (flat dss)))) (unitaryCompact ℝ (∑ j, sz dss j)),
      (∀ w ∈ W, ∫ k : unitaryCompact ℝ (∑ j, sz dss j),
        u k * (w : Langlands.GeneralLinear (∑ j, sz dss j) ℝ → ℂ) k
          ∂haarK (∑ j, sz dss j) = 0) ∧
      ∀ Js : Fin c → List ℤ,
        (∀ i, (Js i).length = (slots (cl dss i) (sz dss i)).length) →
        (∀ i, ∀ t ∈ withModes (slots (cl dss i) (sz dss i)) (Js i), (t.M : ℤ) ≤ |t.j|) →
        ∀ κ : ∀ i, Langlands.GeneralLinear (sz dss i) ℝ,
          (∀ i, κ i ∈ unitaryCompact ℝ (sz dss i)) →
          coeffs (withModes (slots (flat dss) (∑ j, sz dss j)) (List.ofFn Js).flatten) u
              (blockDiagGL (sz dss) κ) =
            ∏ i, coeffs (withModes (slots (cl dss i) (sz dss i)) (Js i)) (φ i) (κ i)

theorem realLeviDensity : RealLeviDensityStatement := by
  intro c dss hX φ hφ W hWK hWL hW
  obtain ⟨u, hu, hcoeffs⟩ :=
    RealLeviDensity.exists_density hX (fun i => ⟨φ i, hφ i⟩) W hWK hWL hW
  exact ⟨u, u.2, RealLeviDensity.mem_annW.mp hu, hcoeffs⟩

end Langlands.Archimedean
