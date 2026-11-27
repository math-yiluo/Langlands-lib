import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.RankinSelberg.UnipotentClassDecomposition
import Langlands.Representation.Hecke.TestFunction

/-! # Compact adelic tensors with prescribed finite factors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField Set Topology
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula.GlobalizationTensor

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

local instance : DecidableEq (Langlands.Global.FinitePlace K) := Classical.decEq _

/-- The matrix coordinate of an adelic point at a finite place. -/
def finiteComponent (v : Langlands.Global.FinitePlace K) :
    AdelicGL K n →ₜ* FiniteLocalGL K n v :=
  (FiniteAdelicGL.localProjection K n v).comp (AdelicGL.finite K n)

/-- The inclusion of a single finite matrix factor into the full adelic matrix group. -/
def includeFinite (v : Langlands.Global.FinitePlace K) :
    FiniteLocalGL K n v →ₜ* AdelicGL K n :=
  (AdelicGL.ofFinite K n).comp (FiniteAdelicGL.localInclusion K n v)

@[simp]
theorem finiteComponent_includeFinite (v : Langlands.Global.FinitePlace K)
    (k : FiniteLocalGL K n v) : finiteComponent K n v (includeFinite K n v k) = k := by
  simp [finiteComponent, includeFinite]

theorem finiteComponent_includeFinite_of_ne {v w : Langlands.Global.FinitePlace K}
    (h : w ≠ v) (k : FiniteLocalGL K n v) :
    finiteComponent K n w (includeFinite K n v k) = 1 := by
  simp [finiteComponent, includeFinite, FiniteAdelicGL.localProjection_localInclusion_of_ne, h]

@[simp]
theorem infinite_includeFinite (v : Langlands.Global.FinitePlace K) (k : FiniteLocalGL K n v) :
    AdelicGL.infinite K n (includeFinite K n v k) = 1 := by
  simp [includeFinite]

section Comparison

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

local instance : IsAffine (GLG).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

/-- The finite matrix coordinate agrees with the localization of actual points. -/
theorem finiteComponent_adelicHomeomorph (v : Langlands.Global.FinitePlace K)
    (x : AdelicGroupPoints K GLG) :
    finiteComponent K n v (GeneralLinearGroupPoints.adelicHomeomorph K n x) =
      GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
        (placeCompletion K (.inr v)) (AdelicGroupPoints.atPlace K GLG (.inr v) x) := by
  symm
  exact GroupScheme.GeneralLinear.affinePointsEquiv_naturality (n := Fin n)
    (R := CommRingCat.of K) (CommAlgCat.ofHom (adeleProjection K (.inr v))) x

/-- The actual local point insertion identifies with insertion of a matrix factor. -/
theorem adelicHomeomorph_ofPlace (v : Langlands.Global.FinitePlace K)
    (x : PlaceGroupPoints K GLG (.inr v)) :
    GeneralLinearGroupPoints.adelicHomeomorph K n (AdelicGroupPoints.ofPlace K GLG (.inr v) x) =
      includeFinite K n v (GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n)
        (CommRingCat.of K) (placeCompletion K (.inr v)) x) := by
  apply Units.ext
  apply Matrix.ext
  intro j k
  apply Prod.ext
  · funext w
    have h := GroupScheme.GeneralLinear.affinePointsEquiv_naturality (n := Fin n)
      (R := CommRingCat.of K) (CommAlgCat.ofHom (adeleProjection K (.inl w)))
        (AdelicGroupPoints.ofPlace K GLG (.inr v) x)
    change GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) (CommRingCat.of K)
      (placeCompletion K (.inl w)) (AdelicGroupPoints.atPlace K GLG (.inl w)
        (AdelicGroupPoints.ofPlace K GLG (.inr v) x)) = _ at h
    rw [AdelicGroupPoints.atPlace_ofPlace_of_ne K GLG _ _ (by simp), map_one] at h
    have hleft := congrArg (fun g => g.val j k) h.symm
    have hright := congrArg (fun g : InfiniteAdelicGL K n => g.val j k w)
      (infinite_includeFinite K n v
        (GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
          (placeCompletion K (.inr v)) x))
    have h1 : (1 : InfiniteAdelicGL K n).val j k w =
        (1 : GeneralLinear n w.Completion).val j k := by
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> rfl
    exact hleft.trans (h1.symm.trans hright.symm)
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    have h : finiteComponent K n w (GeneralLinearGroupPoints.adelicHomeomorph K n
        (AdelicGroupPoints.ofPlace K GLG (.inr v) x)) =
        finiteComponent K n w (includeFinite K n v
          (GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
            (placeCompletion K (.inr v)) x)) := by
      rw [finiteComponent_adelicHomeomorph]
      by_cases hw : w = v
      · subst w
        rw [AdelicGroupPoints.atPlace_ofPlace_same, finiteComponent_includeFinite]
      · rw [AdelicGroupPoints.atPlace_ofPlace_of_ne K GLG _ _ (by simpa using hw), map_one,
          finiteComponent_includeFinite_of_ne K n hw]
    exact congrArg (fun a => a.val j k) h

/-- Insert a local matrix through the actual group-scheme adelic point inclusion. -/
def matrixPlaceInclusion (v : Langlands.Global.FinitePlace K) :
    FiniteLocalGL K n v →* AdelicGroupPoints K GLG :=
  (AdelicGroupPoints.ofPlace K GLG (.inr v)).comp
    (GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
      (placeCompletion K (.inr v))).symm.toMonoidHom

@[simp]
theorem adelicHomeomorph_matrixPlaceInclusion (v : Langlands.Global.FinitePlace K)
    (k : FiniteLocalGL K n v) :
    GeneralLinearGroupPoints.adelicHomeomorph K n (matrixPlaceInclusion K n v k) =
      includeFinite K n v k := by
  let E := GroupScheme.GeneralLinear.affinePointsHomeomorph (Fin n) (CommRingCat.of K)
    (placeCompletion K (.inr v))
  change GeneralLinearGroupPoints.adelicHomeomorph K n
    (AdelicGroupPoints.ofPlace K GLG (.inr v) (E.symm k)) = _
  rw [adelicHomeomorph_ofPlace]
  exact congrArg (includeFinite K n v) (E.apply_symm_apply k)

end Comparison

section Test

variable (s : Finset (Langlands.Global.FinitePlace K))

/-- The away restricted-product component of a full adelic matrix. -/
def awayComponent : AdelicGL K n →ₜ* FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s) :=
  { toMonoidHom := (MonoidHom.snd _ _).comp
      ((FiniteAdelicGL.splitAtPlaces K n (· ∈ s)).toMonoidHom.comp
        (AdelicGL.finite K n).toMonoidHom)
    continuous_toFun := continuous_snd.comp
      ((FiniteAdelicGL.splitAtPlaces K n (· ∈ s)).continuous.comp (AdelicGL.finite K n).continuous) }

@[simp]
theorem awayComponent_apply (g : AdelicGL K n)
    (v : {v : Langlands.Global.FinitePlace K // v ∉ s}) :
    awayComponent K n s g v = finiteComponent K n v g := rfl

local notation "J" => FiniteAdelicGL.awayIntegral K n (· ∈ s)

/-- The characteristic function of the everywhere-integral away subgroup. -/
def awayCharacteristic : SchwartzBruhat (FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s)) := by
  have hc := RankinSelbergGlobal.UnipotentClass.isCompact_awayIntegral K n s
  exact Hecke.TestFunction.characteristic ⟨hc.isClosed, (J).isOpen⟩ hc

theorem awayCharacteristic_of_mem {g : FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s)}
    (h : g ∈ J) : awayCharacteristic K n s g = 1 := by
  exact Set.indicator_of_mem h _

theorem awayCharacteristic_mul_of_mem (g k : FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s))
    (hk : k ∈ J) : awayCharacteristic K n s (k * g) = awayCharacteristic K n s g := by
  have h : k * g ∈ ((J) : Set _) ↔ g ∈ ((J) : Set _) := by
    change k * g ∈ (J).toSubgroup ↔ g ∈ (J).toSubgroup
    exact ⟨fun h => by simpa only [inv_mul_cancel_left] using (J).mul_mem ((J).inv_mem hk) h,
      (J).mul_mem hk⟩
  classical
  change Set.indicator (↑(J)) (fun _ => (1 : ℂ)) (k * g) =
    Set.indicator (↑(J)) (fun _ => (1 : ℂ)) g
  simp only [Set.indicator, h]

set_option maxHeartbeats 950000 in
/-- The archimedean factor times the product of the specified local tests and the
characteristic function of the integral away subgroup. -/
def test (b : C_c(InfiniteAdelicGL K n, ℂ)) (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) :
    C_c(AdelicGL K n, ℂ) := by
  let E := (AdelicGL.split K n).toHomeomorph.trans
    ((Homeomorph.refl (InfiniteAdelicGL K n)).prodCongr
      (FiniteAdelicGL.splitAtPlaces K n (· ∈ s)).toHomeomorph)
  let h := awayCharacteristic K n s
  let F := fun z : InfiniteAdelicGL K n × ((∀ v : s, FiniteLocalGL K n v) ×
      FiniteAdelicGL.AwayRestrictedProduct K n (· ∈ s)) =>
    b z.1 * (∏ v : s, f v (z.2.1 v)) * h z.2.2
  have hc : Continuous F :=
    ((b.continuous.comp continuous_fst).mul (continuous_finsetProd _ fun v _ =>
      (f v).continuous.comp ((continuous_apply v).comp (continuous_fst.comp continuous_snd)))).mul
      (h.continuous.comp (continuous_snd.comp continuous_snd))
  have hlocals : IsCompact (Set.univ.pi (fun v : s => tsupport (f v))) :=
    isCompact_univ_pi fun v => (f v).hasCompactSupport
  have hsupport := b.hasCompactSupport.prod (hlocals.prod h.hasCompactSupport)
  have hF : HasCompactSupport F := by
    refine HasCompactSupport.intro' hsupport
      (isClosed_closure.prod ((isClosed_set_pi fun _ _ => isClosed_closure).prod isClosed_closure)) ?_
    intro z hz
    by_contra hn
    simp only [F, mul_eq_zero, not_or] at hn
    refine hz ⟨subset_tsupport _ hn.1.1, ?_, subset_tsupport _ hn.2⟩
    exact Set.mem_univ_pi.mpr fun v => subset_tsupport _
      (fun he => hn.1.2 (Finset.prod_eq_zero (Finset.mem_univ v) he))
  exact ⟨⟨F ∘ E, hc.comp E.continuous⟩, hF.comp_homeomorph E⟩

@[simp]
theorem test_apply (b : C_c(InfiniteAdelicGL K n, ℂ))
    (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) (g : AdelicGL K n) :
    test K n s b f g = b (AdelicGL.infinite K n g) *
      (∏ v : s, f v (finiteComponent K n v g)) * awayCharacteristic K n s (awayComponent K n s g) :=
  rfl

/-- All factors other than the selected place's local test. -/
def complement (b : C_c(InfiniteAdelicGL K n, ℂ))
    (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) (v : s) (g : AdelicGL K n) : ℂ :=
  b (AdelicGL.infinite K n g) *
    (∏ w ∈ (Finset.univ.erase v), f w (finiteComponent K n w g)) *
    awayCharacteristic K n s (awayComponent K n s g)

theorem test_eq_complement_mul (b : C_c(InfiniteAdelicGL K n, ℂ))
    (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) (v : s) (g : AdelicGL K n) :
    test K n s b f g = complement K n s b f v g * f v (finiteComponent K n v g) := by
  rw [test_apply, ← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ v)]
  unfold complement
  ring

/-- All finite coordinates other than the selected place are unchanged in the
complement of a factored test. -/
theorem complement_insert (b : C_c(InfiniteAdelicGL K n, ℂ))
    (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v)) (v : s) (k : FiniteLocalGL K n v)
    (x y : AdelicGL K n) :
    complement K n s b f v (x * includeFinite K n v k * y) = complement K n s b f v (x * y) := by
  have haway : awayComponent K n s (includeFinite K n v k) = 1 := by
    apply RestrictedProduct.ext
    intro w
    have hw : w.val ≠ v.val := fun he => w.property (he.symm ▸ v.property)
    rw [awayComponent_apply, finiteComponent_includeFinite_of_ne K n hw]
    rfl
  unfold complement
  simp only [map_mul, infinite_includeFinite, mul_one, haway]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [finiteComponent_includeFinite_of_ne K n
    (fun h => (Finset.mem_erase.mp hw).1 (Subtype.ext h)), mul_one]

/-- Insertion of an integral matrix outside the prescribed places fixes the tensor. -/
theorem test_awayIntegral_mul (b : C_c(InfiniteAdelicGL K n, ℂ))
    (f : ∀ v : s, SchwartzBruhat (FiniteLocalGL K n v))
    (v : Langlands.Global.FinitePlace K) (hv : v ∉ s) (k : FiniteLocalGL K n v)
    (hk : k ∈ FiniteAdelicGL.localIntegral K n v) (g : AdelicGL K n) :
    test K n s b f (includeFinite K n v k * g) = test K n s b f g := by
  have haway : awayComponent K n s (includeFinite K n v k) ∈ J := by
    rw [FiniteAdelicGL.mem_awayIntegral]
    intro w
    rw [awayComponent_apply]
    by_cases h : w.val = v
    · obtain ⟨w, hw⟩ := w
      change w = v at h
      subst w
      simpa only [finiteComponent_includeFinite] using hk
    · rw [finiteComponent_includeFinite_of_ne K n h]
      exact (FiniteAdelicGL.localIntegral K n w).one_mem
  simp only [test_apply, map_mul, infinite_includeFinite, one_mul,
    awayCharacteristic_mul_of_mem K n s _ _ haway]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  have hw : w.val ≠ v := fun h => hv (h ▸ w.property)
  rw [finiteComponent_includeFinite_of_ne K n hw, one_mul]

end Test

end Langlands.TraceFormula.GlobalizationTensor
