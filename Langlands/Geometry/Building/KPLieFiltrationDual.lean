import Langlands.Geometry.Building.KPLieFiltration

/-!
# Periodicity, real indices and the dual Moy–Prasad lattices

For supplied `L : P.LieFiltrationData` with lattices `𝔤_{x,r}` (`r ≥ 0`), this module states
the periodicity `𝔤_{x,r+1} = 𝔪 • 𝔤_{x,r}` of KP 13.3.1 as a predicate, extends `𝔤_{x,r}` to
real `r` as KP 13.3.1 does, and defines the dual lattices
`𝔤*_{x,r} = {X ∈ 𝔤* | X(Y) ∈ 𝔪 for all Y ∈ 𝔤_{x,(-r)+}}`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} (L : P.LieFiltrationData)

/-- The periodicity `𝔤_{x,r+1} = 𝔪 • 𝔤_{x,r}` of KP 13.3.1 (KP Proposition 8.5.16 for the
models `𝒢_{x,r}`), for the supplied data. -/
def IsPeriodic : Prop :=
  ∀ (x : P.Apartment) (r : NNReal), L.lieFiltration x (r + 1) = 𝓂[F] • L.lieFiltration x r

/-! ### Real indices -/

/-- The shift `n(r) = ⌈-r⌉₊`, the least natural number with `r + n(r) ≥ 0`. -/
abbrev indexShift (r : ℝ) : ℕ := ⌈-r⌉₊

theorem add_indexShift_nonneg (r : ℝ) : 0 ≤ r + indexShift r := by
  have := Nat.le_ceil (-r)
  linarith

/-- The non-negative index `r + n(r)`. -/
def shiftedIndex (r : ℝ) : NNReal := ⟨r + indexShift r, add_indexShift_nonneg r⟩

theorem indexShift_coe (r : NNReal) : indexShift (r : ℝ) = 0 :=
  Nat.ceil_eq_zero.2 (by simp)

theorem shiftedIndex_coe (r : NNReal) : shiftedIndex (r : ℝ) = r := by
  apply NNReal.eq
  change (r : ℝ) + (indexShift (r : ℝ) : ℝ) = r
  rw [indexShift_coe, Nat.cast_zero, add_zero]

/-- `𝔤_{x,r}` for real `r` (KP 13.3.1): the `X` with `𝔪^n X ⊆ 𝔤_{x,r+n}`, `n = ⌈-r⌉₊`. For
`r ≥ 0` this is the original lattice (`lieFiltrationReal_coe`); for `r < 0` it is
`ϖ^{-n} 𝔤_{x,r+n}` for a uniformizer `ϖ`. -/
def lieFiltrationReal (x : P.Apartment) (r : ℝ) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ⨅ a ∈ 𝓂[F] ^ indexShift r,
    (L.lieFiltration x (shiftedIndex r)).comap (a • LinearMap.id)

theorem mem_lieFiltrationReal {x : P.Apartment} {r : ℝ} {X : GenericLie 𝒪[F] G} :
    X ∈ L.lieFiltrationReal x r ↔
      ∀ a ∈ 𝓂[F] ^ indexShift r, a • X ∈ L.lieFiltration x (shiftedIndex r) := by
  simp [lieFiltrationReal, Submodule.mem_iInf]

/-- On non-negative indices the extension is the original lattice. -/
theorem lieFiltrationReal_coe (x : P.Apartment) (r : NNReal) :
    L.lieFiltrationReal x r = L.lieFiltration x r := by
  ext X
  rw [mem_lieFiltrationReal, indexShift_coe, shiftedIndex_coe, pow_zero, Ideal.one_eq_top]
  exact ⟨fun h => by simpa using h 1 Submodule.mem_top,
    fun h a _ => Submodule.smul_mem _ a h⟩

/-- Under periodicity, `𝔪^k • 𝔤_{x,t} ≤ 𝔤_{x,t+k}`. -/
theorem smul_lieFiltration_le (hL : L.IsPeriodic) (x : P.Apartment) (k : ℕ) (t : NNReal) :
    𝓂[F] ^ k • L.lieFiltration x t ≤ L.lieFiltration x (t + k) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Submodule.mul_smul, ← hL x t]
    refine (ih (t + 1)).trans (le_of_eq ?_)
    congr 1
    push_cast
    ring

/-- Under periodicity, the extension to real indices is decreasing. -/
theorem lieFiltrationReal_antitone (hL : L.IsPeriodic) (x : P.Apartment) :
    Antitone (L.lieFiltrationReal x) := by
  intro r s hrs X hX
  rw [mem_lieFiltrationReal] at hX ⊢
  have hn : indexShift s ≤ indexShift r := Nat.ceil_mono (neg_le_neg hrs)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  intro b hb
  rw [hk, pow_add] at hb
  have hle : L.lieFiltration x (shiftedIndex s + k) ≤ L.lieFiltration x (shiftedIndex r) := by
    apply L.lieFiltration_antitone x
    rw [← NNReal.coe_le_coe]
    have hk' : (indexShift r : ℝ) = indexShift s + k := by exact_mod_cast hk
    change r + (indexShift r : ℝ) ≤ s + (indexShift s : ℝ) + k
    linarith
  refine hle ?_
  refine Submodule.mul_induction_on hb ?_ ?_
  · intro a ha c hc
    rw [mul_comm, mul_smul]
    exact L.smul_lieFiltration_le hL x k (shiftedIndex s) (Submodule.smul_mem_smul hc (hX a ha))
  · intro b b' h h'
    rw [add_smul]
    exact add_mem h h'

/-- `𝔤_{x,r+}` for real `r`: the supremum of the submodules `𝔤_{x,s}`, `s > r`. When the real
family is decreasing, for instance under `IsPeriodic` (`lieFiltrationReal_antitone`), this is
KP's union `⋃_{s > r} 𝔤_{x,s}` (`mem_lieFiltrationPlusReal`); for arbitrary supplied data the
supremum can be larger than the union. -/
def lieFiltrationPlusReal (x : P.Apartment) (r : ℝ) : Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ⨆ (s : ℝ) (_ : r < s), L.lieFiltrationReal x s

/-- For an antitone family of submodules indexed by `ℝ`, membership in the supremum over
`s > r` is membership in one of them: the family is directed by `min`. -/
theorem mem_biSup_lt_of_antitone {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {f : ℝ → Submodule R M} (hf : Antitone f) {r : ℝ} {X : M} :
    X ∈ ⨆ (s : ℝ) (_ : r < s), f s ↔ ∃ s, r < s ∧ X ∈ f s := by
  have : Nonempty {s : ℝ // r < s} := ⟨⟨r + 1, lt_add_one r⟩⟩
  rw [iSup_subtype', Submodule.mem_iSup_of_directed]
  · exact ⟨fun ⟨s, hs⟩ => ⟨s.1, s.2, hs⟩, fun ⟨s, hs, h⟩ => ⟨⟨s, hs⟩, h⟩⟩
  · intro s s'
    exact ⟨⟨min s.1 s'.1, lt_min s.2 s'.2⟩, hf (min_le_left _ _), hf (min_le_right _ _)⟩

/-- Under periodicity, `𝔤_{x,r+}` is KP's union `⋃_{s > r} 𝔤_{x,s}`. -/
theorem mem_lieFiltrationPlusReal (hL : L.IsPeriodic) {x : P.Apartment} {r : ℝ}
    {X : GenericLie 𝒪[F] G} :
    X ∈ L.lieFiltrationPlusReal x r ↔ ∃ s, r < s ∧ X ∈ L.lieFiltrationReal x s :=
  mem_biSup_lt_of_antitone (L.lieFiltrationReal_antitone hL x)

theorem lieFiltrationPlusReal_antitone (x : P.Apartment) : Antitone (L.lieFiltrationPlusReal x) :=
  fun _ _ h => iSup₂_le fun s hs => le_iSup₂_of_le s (h.trans_lt hs) le_rfl

theorem lieFiltrationReal_le_lieFiltrationPlusReal (x : P.Apartment) {r s : ℝ} (h : r < s) :
    L.lieFiltrationReal x s ≤ L.lieFiltrationPlusReal x r :=
  le_iSup₂_of_le s h le_rfl

/-- Under periodicity, `𝔤_{x,r+} ≤ 𝔤_{x,r}` for real `r`. -/
theorem lieFiltrationPlusReal_le (hL : L.IsPeriodic) (x : P.Apartment) (r : ℝ) :
    L.lieFiltrationPlusReal x r ≤ L.lieFiltrationReal x r :=
  iSup₂_le fun _ hs => L.lieFiltrationReal_antitone hL x hs.le

/-! ### Dual lattices -/

/-- The maximal ideal `𝔪` as an `𝒪`-submodule of `F`. -/
def maximalIdealSubmodule : Submodule 𝒪[F] F :=
  Submodule.map (Algebra.linearMap 𝒪[F] F) (𝓂[F])

/-- The `Y ∈ 𝔤` with `X(Y) ∈ 𝔪`, for a linear form `X ∈ 𝔤* = Module.Dual F 𝔤`. -/
def dualPairingSubmodule (X : Module.Dual F (GenericLie 𝒪[F] G)) :
    Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  maximalIdealSubmodule.comap (X.restrictScalars 𝒪[F])

theorem mem_dualPairingSubmodule (X : Module.Dual F (GenericLie 𝒪[F] G))
    (Y : GenericLie 𝒪[F] G) :
    Y ∈ dualPairingSubmodule X ↔ ∃ m ∈ 𝓂[F], (m : F) = X Y := by
  rw [dualPairingSubmodule, Submodule.mem_comap, maximalIdealSubmodule, Submodule.mem_map]
  rfl

/-- The dual lattice `𝔤*_{x,r} = {X ∈ 𝔤* | X(Y) ∈ 𝔪 for all Y ∈ 𝔤_{x,(-r)+}}` (KP 13.3.1). -/
def dualLieFiltration (x : P.Apartment) (r : ℝ) :
    Submodule 𝒪[F] (Module.Dual F (GenericLie 𝒪[F] G)) where
  carrier := {X | L.lieFiltrationPlusReal x (-r) ≤ dualPairingSubmodule X}
  zero_mem' := by
    intro Y _
    exact (mem_dualPairingSubmodule 0 Y).2 ⟨0, Submodule.zero_mem _, by simp⟩
  add_mem' := by
    intro X X' hX hX' Y hY
    obtain ⟨m, hm, e⟩ := (mem_dualPairingSubmodule X Y).1 (hX hY)
    obtain ⟨m', hm', e'⟩ := (mem_dualPairingSubmodule X' Y).1 (hX' hY)
    exact (mem_dualPairingSubmodule _ Y).2 ⟨m + m', add_mem hm hm', by simp [e, e']⟩
  smul_mem' := by
    intro c X hX Y hY
    obtain ⟨m, hm, e⟩ := (mem_dualPairingSubmodule X Y).1 (hX hY)
    refine (mem_dualPairingSubmodule _ Y).2 ⟨c * m, Ideal.mul_mem_left _ c hm, ?_⟩
    have h : (c • X) Y = (c : F) * X Y := by
      rw [LinearMap.smul_apply, Algebra.smul_def]
      rfl
    rw [h, ← e]
    rfl

theorem mem_dualLieFiltration {x : P.Apartment} {r : ℝ}
    {X : Module.Dual F (GenericLie 𝒪[F] G)} :
    X ∈ L.dualLieFiltration x r ↔
      ∀ s : ℝ, -r < s → ∀ Y ∈ L.lieFiltrationReal x s, ∃ m ∈ 𝓂[F], (m : F) = X Y := by
  change L.lieFiltrationPlusReal x (-r) ≤ dualPairingSubmodule X ↔ _
  rw [lieFiltrationPlusReal, iSup₂_le_iff]
  simp only [SetLike.le_def, mem_dualPairingSubmodule]

theorem dualLieFiltration_antitone (x : P.Apartment) : Antitone (L.dualLieFiltration x) :=
  fun _ _ h _ hX => (L.lieFiltrationPlusReal_antitone x (neg_le_neg h)).trans hX

/-- `𝔤*_{x,r+}`: the supremum of the submodules `𝔤*_{x,s}`, `s > r`. The dual family is
decreasing without hypotheses (`dualLieFiltration_antitone`), so this is KP's union
`⋃_{s > r} 𝔤*_{x,s}` (`mem_dualLieFiltrationPlus`). -/
def dualLieFiltrationPlus (x : P.Apartment) (r : ℝ) :
    Submodule 𝒪[F] (Module.Dual F (GenericLie 𝒪[F] G)) :=
  ⨆ (s : ℝ) (_ : r < s), L.dualLieFiltration x s

/-- `𝔤*_{x,r+} = ⋃_{s > r} 𝔤*_{x,s}`. -/
theorem mem_dualLieFiltrationPlus {x : P.Apartment} {r : ℝ}
    {X : Module.Dual F (GenericLie 𝒪[F] G)} :
    X ∈ L.dualLieFiltrationPlus x r ↔ ∃ s, r < s ∧ X ∈ L.dualLieFiltration x s :=
  mem_biSup_lt_of_antitone (L.dualLieFiltration_antitone x)

theorem dualLieFiltrationPlus_le (x : P.Apartment) (r : ℝ) :
    L.dualLieFiltrationPlus x r ≤ L.dualLieFiltration x r :=
  iSup₂_le fun _ hs => L.dualLieFiltration_antitone x hs.le

end Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData
