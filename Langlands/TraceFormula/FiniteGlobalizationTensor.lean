import Langlands.TraceFormula.GlobalizationTensor

/-! # Finite adelic tensor tests with prescribed local factors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open Langlands.Global Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula.GlobalizationTensor

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private local instance : DecidableEq (Langlands.Global.FinitePlace K) := Classical.decEq _

variable (s : Finset (Langlands.Global.FinitePlace K))

/-- The away part of a finite adelic matrix, outside the places of `s`. -/
def finiteAway : FiniteAdelicGL K n →ₜ* FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s) :=
  { toMonoidHom := (MonoidHom.snd _ _).comp (FiniteAdelicGL.splitAtPlaces K n (· ∈ s)).toMonoidHom
    continuous_toFun := continuous_snd.comp (FiniteAdelicGL.splitAtPlaces K n (· ∈ s)).continuous }

@[simp]
theorem finiteAway_apply (g : FiniteAdelicGL K n)
    (v : {v : Langlands.Global.FinitePlace K // v ∉ s}) :
    finiteAway K n s g v = FiniteAdelicGL.localProjection K n v g := rfl

private theorem isLocallyConstant_prod {X : Type*} [TopologicalSpace X] {ι : Type*}
    (t : Finset ι) (f : ι → X → ℂ) (hf : ∀ i ∈ t, IsLocallyConstant (f i)) :
    IsLocallyConstant (fun x => ∏ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact IsLocallyConstant.const 1
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a t)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

set_option maxHeartbeats 1000000 in
/-- The finite adelic tensor of local tests at the places of `s` with the characteristic
function of the integral away subgroup. -/
def finiteSchwartzTest (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) :
    SchwartzBruhat (FiniteAdelicGL K n) := by
  let E := (FiniteAdelicGL.splitAtPlaces K n (· ∈ s)).toHomeomorph
  let h := awayCharacteristic K n s
  let F := fun z : (∀ v : s, FiniteLocalGL K n v) ×
      FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s) =>
    (∏ v : s, f v (z.1 v)) * h z.2
  have hlc : IsLocallyConstant F :=
    (isLocallyConstant_prod Finset.univ
      (fun (v : s) (z : (∀ v : s, FiniteLocalGL K n v) ×
        FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s)) => f v (z.1 v)) fun v _ =>
      ((f v).locallyConstant.comp_continuous ((continuous_apply v).comp continuous_fst))).mul
      (h.locallyConstant.comp_continuous continuous_snd)
  have hlocals : IsCompact (Set.univ.pi (fun v : s => tsupport (f v))) :=
    isCompact_univ_pi fun v => (f v).hasCompactSupport
  have hsupport := hlocals.prod h.hasCompactSupport
  have hF : HasCompactSupport F := by
    refine HasCompactSupport.intro' hsupport
      ((isClosed_set_pi fun _ _ => isClosed_closure).prod isClosed_closure) ?_
    intro z hz
    by_contra hn
    simp only [F, mul_eq_zero, not_or] at hn
    refine hz ⟨?_, subset_tsupport _ hn.2⟩
    exact Set.mem_univ_pi.mpr fun v => subset_tsupport _
      (fun he => hn.1 (Finset.prod_eq_zero (Finset.mem_univ v) he))
  exact ⟨F ∘ E, hlc.comp_continuous E.continuous, hF.comp_homeomorph E⟩

@[simp]
theorem finiteSchwartzTest_apply (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v))
    (g : FiniteAdelicGL K n) :
    finiteSchwartzTest K n s f g = (∏ v : s, f v (FiniteAdelicGL.localProjection K n v g)) *
      awayCharacteristic K n s (finiteAway K n s g) :=
  rfl

/-- All factors of a finite tensor other than the selected place's local test. -/
def finiteComplement (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) (v : s)
    (g : FiniteAdelicGL K n) : ℂ :=
  (∏ w ∈ (Finset.univ.erase v), f w (FiniteAdelicGL.localProjection K n w g)) *
    awayCharacteristic K n s (finiteAway K n s g)

theorem finiteTest_eq_complement_mul (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v))
    (v : s) (g : FiniteAdelicGL K n) :
    finiteSchwartzTest K n s f g =
      finiteComplement K n s f v g * f v (FiniteAdelicGL.localProjection K n v g) := by
  rw [finiteSchwartzTest_apply, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ v)]
  unfold finiteComplement
  ring

/-- Inserting a local matrix at the selected place does not change the complement. -/
theorem finiteComplement_insert (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) (v : s)
    (k : FiniteLocalGL K n v) (x y : FiniteAdelicGL K n) :
    finiteComplement K n s f v (x * FiniteAdelicGL.localInclusion K n v k * y) =
      finiteComplement K n s f v (x * y) := by
  have haway : finiteAway K n s (FiniteAdelicGL.localInclusion K n v k) = 1 := by
    apply RestrictedProduct.ext
    intro w
    have hw : w.val ≠ v.val := fun he => w.property (he.symm ▸ v.property)
    rw [finiteAway_apply, FiniteAdelicGL.localProjection_localInclusion_of_ne K n _ _ hw]
    rfl
  unfold finiteComplement
  simp only [map_mul, haway, mul_one]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [FiniteAdelicGL.localProjection_localInclusion_of_ne K n _ _
    (fun h => (Finset.mem_erase.mp hw).1 (Subtype.ext h)), mul_one]

/-- The open level subgroup with prescribed local subgroups at the places of `s` and
integral components elsewhere. It is compact when the prescribed local subgroups are compact. -/
def finiteLevel (U : ∀ v : s, OpenSubgroup (FiniteLocalGL K n v)) :
    OpenSubgroup (FiniteAdelicGL K n) where
  carrier := {g | (∀ v : s, FiniteAdelicGL.localProjection K n v g ∈ U v) ∧
    finiteAway K n s g ∈ FiniteAdelicGL.awayIntegral K n (· ∈ s)}
  one_mem' := ⟨fun v => by simp, by simp⟩
  mul_mem' {a b} ha hb := ⟨fun v => by simpa using (U v).mul_mem (ha.1 v) (hb.1 v), by
    simpa using (FiniteAdelicGL.awayIntegral K n (· ∈ s)).mul_mem ha.2 hb.2⟩
  inv_mem' {a} ha := ⟨fun v => by simpa using (U v).inv_mem (ha.1 v), by
    simpa using (FiniteAdelicGL.awayIntegral K n (· ∈ s)).inv_mem ha.2⟩
  isOpen' := by
    have h1 : IsOpen {g : FiniteAdelicGL K n |
        ∀ v : s, FiniteAdelicGL.localProjection K n v g ∈ U v} := by
      have he : {g : FiniteAdelicGL K n |
          ∀ v : s, FiniteAdelicGL.localProjection K n v g ∈ U v} =
          ⋂ v : s, FiniteAdelicGL.localProjection K n v ⁻¹' (U v : Set _) := by
        ext g
        simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
        rfl
      rw [he]
      exact isOpen_iInter_of_finite fun v =>
        (U v).isOpen.preimage (FiniteAdelicGL.localProjection K n v).continuous
    exact h1.inter ((FiniteAdelicGL.awayIntegral K n (· ∈ s)).isOpen.preimage
      (finiteAway K n s).continuous)

theorem mem_finiteLevel (U : ∀ v : s, OpenSubgroup (FiniteLocalGL K n v))
    (g : FiniteAdelicGL K n) :
    g ∈ finiteLevel K n s U ↔ (∀ v : s, FiniteAdelicGL.localProjection K n v g ∈ U v) ∧
      finiteAway K n s g ∈ FiniteAdelicGL.awayIntegral K n (· ∈ s) :=
  Iff.rfl

/-- The level subgroup is compact when every prescribed local subgroup is. -/
theorem isCompact_finiteLevel (U : ∀ v : s, OpenSubgroup (FiniteLocalGL K n v))
    (hU : ∀ v : s, IsCompact (U v : Set (FiniteLocalGL K n v))) :
    IsCompact (finiteLevel K n s U : Set (FiniteAdelicGL K n)) := by
  let E := (FiniteAdelicGL.splitAtPlaces K n (· ∈ s)).toHomeomorph
  have hJ : IsCompact ((FiniteAdelicGL.awayIntegral K n (· ∈ s)).toSubgroup :
      Set (FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s))) :=
    RankinSelbergGlobal.UnipotentClass.isCompact_awayIntegral K n s
  have hc := (isCompact_univ_pi hU).prod hJ
  convert E.isCompact_preimage.mpr hc using 1
  ext g
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ_pi]
  rfl

/-- A finite tensor of right-invariant local tests is right invariant under the level
subgroup. -/
theorem finiteTest_mul_of_mem (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v))
    (U : ∀ v : s, OpenSubgroup (FiniteLocalGL K n v))
    (hf : ∀ (v : s) (x k : FiniteLocalGL K n v), k ∈ U v → f v (x * k) = f v x)
    (g k : FiniteAdelicGL K n) (hk : k ∈ finiteLevel K n s U) :
    finiteSchwartzTest K n s f (g * k) = finiteSchwartzTest K n s f g := by
  rw [finiteSchwartzTest_apply, finiteSchwartzTest_apply]
  congr 1
  · apply Finset.prod_congr rfl
    intro v _
    rw [map_mul]
    exact hf v _ _ (hk.1 v)
  · rw [map_mul]
    have h := awayCharacteristic_mul_of_mem K n s
    have hJ := hk.2
    have hmem : ∀ (x y : FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s)),
        y ∈ FiniteAdelicGL.awayIntegral K n (· ∈ s) →
        awayCharacteristic K n s (x * y) = awayCharacteristic K n s x := by
      intro x y hy
      classical
      have hiff : x * y ∈ ((FiniteAdelicGL.awayIntegral K n (· ∈ s)) : Set _) ↔
          x ∈ ((FiniteAdelicGL.awayIntegral K n (· ∈ s)) : Set _) := by
        change x * y ∈ (FiniteAdelicGL.awayIntegral K n (· ∈ s)).toSubgroup ↔
          x ∈ (FiniteAdelicGL.awayIntegral K n (· ∈ s)).toSubgroup
        exact ⟨fun hxy => by
            simpa only [mul_inv_cancel_right] using
              (FiniteAdelicGL.awayIntegral K n (· ∈ s)).mul_mem hxy
                ((FiniteAdelicGL.awayIntegral K n (· ∈ s)).inv_mem hy),
          fun hx => (FiniteAdelicGL.awayIntegral K n (· ∈ s)).mul_mem hx hy⟩
      change Set.indicator (↑(FiniteAdelicGL.awayIntegral K n (· ∈ s))) (fun _ => (1 : ℂ))
          (x * y) =
        Set.indicator (↑(FiniteAdelicGL.awayIntegral K n (· ∈ s))) (fun _ => (1 : ℂ)) x
      simp only [Set.indicator, hiff]
    exact hmem _ _ hJ

/-- A finite adelic tensor of local tests that are right invariant under compact open local
subgroups is right invariant under the corresponding compact open level subgroup. At each
prescribed place it is the local test times a complement unchanged by inserting a local
matrix at that place. -/
def FiniteTensorFactorizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ) (s : Finset (Langlands.Global.FinitePlace K))
    (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v))
    (U : ∀ v : s, OpenSubgroup (FiniteLocalGL K n v)),
    (∀ v : s, IsCompact (U v : Set (FiniteLocalGL K n v))) →
    (∀ (v : s) (x k : FiniteLocalGL K n v), k ∈ U v → f v (x * k) = f v x) →
    IsCompact (finiteLevel K n s U : Set (FiniteAdelicGL K n)) ∧
    (∀ g k : FiniteAdelicGL K n, k ∈ finiteLevel K n s U →
      finiteSchwartzTest K n s f (g * k) = finiteSchwartzTest K n s f g) ∧
    ∀ v : s, (∀ g : FiniteAdelicGL K n, finiteSchwartzTest K n s f g =
        finiteComplement K n s f v g * f v (FiniteAdelicGL.localProjection K n v g)) ∧
      ∀ (k : FiniteLocalGL K n v) (x y : FiniteAdelicGL K n),
        finiteComplement K n s f v (x * FiniteAdelicGL.localInclusion K n v k * y) =
          finiteComplement K n s f v (x * y)

theorem finiteTensorFactorization : FiniteTensorFactorizationStatement.{u} := by
  intro K _ _ n s f U hU hf
  exact ⟨isCompact_finiteLevel K n s U hU, finiteTest_mul_of_mem K n s f U hf,
    fun v => ⟨finiteTest_eq_complement_mul K n s f v, finiteComplement_insert K n s f v⟩⟩

end Langlands.TraceFormula.GlobalizationTensor
