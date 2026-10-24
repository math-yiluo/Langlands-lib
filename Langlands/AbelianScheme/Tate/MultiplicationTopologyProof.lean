import Langlands.AbelianScheme.Tate.MultiplicationTopologyStatement
import Langlands.AbelianScheme.Tate.PrimeComparisonProof

/-! # Positive multiplication on the actual Tate limits -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Tate

universe u
variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

private abbrev fullIndex (n : ℕ) (hn : 0 < n) : Index (fun _ => True) :=
  ⟨n, hn, trivial⟩

private lemma section_transition {a b : ℕ} (h : a ∣ b) (x : Level G T b) :
    toSection G T a (transition G T h x) = (b / a) • toSection G T b x := rfl

private lemma full_section (x : Full G T) (a b : Index (fun _ => True))
    (h : a.val ∣ b.val) :
    (b.val / a.val) • toSection G T b.val (x.val b) =
      toSection G T a.val (x.val a) := by
  rw [← section_transition G T h]
  exact congrArg (toSection G T a.val) (x.property a b h)

private def lowerLevel (a b : ℕ) (x : Level G T a) : Level G T b := by
  classical
  exact if h : b • toSection G T a x = 0 then
    Additive.ofMul ⟨Additive.toMul (toSection G T a x),
      (mem_levelGroup G T b _).mpr h⟩
  else 0

private lemma lowerLevel_section (a b : ℕ) (x : Level G T a)
    (h : b • toSection G T a x = 0) :
    toSection G T b (lowerLevel G T a b x) = toSection G T a x := by
  simp only [lowerLevel, dite_eq_left h]
  rfl

private def evalKernel (n : ℕ) (hn : 0 < n) : AddSubgroup (Full G T) :=
  (evaluation G T (fun _ => True) (fullIndex n hn)).ker

private lemma kernel_coordinate (n : ℕ) (hn : 0 < n)
    (x : evalKernel G T n hn) (k : Index (fun _ => True)) :
    k.val • toSection G T (n * k.val)
      (x.val.val (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))) = 0 := by
  have h := full_section G T x.val (fullIndex n hn)
    (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))
    (dvd_mul_right n k.val)
  change ((n * k.val) / n) • _ = _ at h
  rw [Nat.mul_div_cancel_left _ hn] at h
  rw [h]
  have hx : x.val.val (fullIndex n hn) = 0 := x.property
  rw [hx, map_zero]

private def divideFull (n : ℕ) (hn : 0 < n) (x : evalKernel G T n hn) : Full G T :=
  ⟨fun k => lowerLevel G T (n * k.val) k.val
    (x.val.val (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))), by
    intro a b hab
    apply toSection_injective G T a.val
    rw [section_transition, lowerLevel_section G T _ _ _ (kernel_coordinate G T n hn x b),
      lowerLevel_section G T _ _ _ (kernel_coordinate G T n hn x a)]
    have h := full_section G T x.val
      (fullIndex (n * a.val) (Nat.mul_pos hn a.property.1))
      (fullIndex (n * b.val) (Nat.mul_pos hn b.property.1)) (Nat.mul_dvd_mul_left n hab)
    change ((n * b.val) / (n * a.val)) • _ = _ at h
    simpa only [Nat.mul_div_mul_left _ _ hn] using h⟩

private lemma divideFull_section (n : ℕ) (hn : 0 < n)
    (x : evalKernel G T n hn) (k : Index (fun _ => True)) :
    toSection G T k.val ((divideFull G T n hn x).val k) =
      toSection G T (n * k.val)
        (x.val.val (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))) :=
  lowerLevel_section G T _ _ _ (kernel_coordinate G T n hn x k)

private lemma continuous_divideFull (n : ℕ) (hn : 0 < n) :
    Continuous (divideFull G T n hn) := by
  apply (continuous_iff_evaluation G T _ _).mpr
  intro k
  exact (continuous_of_discreteTopology
    (f := lowerLevel G T (n * k.val) k.val)).comp
      ((continuous_evaluation G T (fun _ => True)
        (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))).comp
          (continuous_subtype_val : Continuous (Subtype.val : evalKernel G T n hn → Full G T)))

private def multiplyToKernel (n : ℕ) (hn : 0 < n) (x : Full G T) :
    evalKernel G T n hn :=
  ⟨n • x, by
    change evaluation G T _ (fullIndex n hn) (n • x) = 0
    rw [map_nsmul]
    exact level_nsmul_eq_zero G T n _⟩

private lemma divideFull_multiplyToKernel (n : ℕ) (hn : 0 < n) (x : Full G T) :
    divideFull G T n hn (multiplyToKernel G T n hn x) = x := by
  apply Subtype.ext
  funext k
  apply toSection_injective G T k.val
  rw [divideFull_section]
  change toSection G T (n * k.val)
    (n • x.val (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))) = _
  rw [map_nsmul]
  have h := full_section G T x k (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))
    (dvd_mul_left k.val n)
  change ((n * k.val) / k.val) • _ = _ at h
  simpa only [Nat.mul_div_cancel _ k.property.1] using h

private lemma multiplyToKernel_divideFull (n : ℕ) (hn : 0 < n)
    (x : evalKernel G T n hn) :
    multiplyToKernel G T n hn (divideFull G T n hn x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  apply toSection_injective G T k.val
  change toSection G T k.val (n • (divideFull G T n hn x).val k) = _
  rw [map_nsmul, divideFull_section]
  have h := full_section G T x.val k (fullIndex (n * k.val) (Nat.mul_pos hn k.property.1))
    (dvd_mul_left k.val n)
  change ((n * k.val) / k.val) • _ = _ at h
  simpa only [Nat.mul_div_cancel _ k.property.1] using h

private def fullKernelHomeomorph (n : ℕ) (hn : 0 < n) :
    Full G T ≃ₜ evalKernel G T n hn where
  toFun := multiplyToKernel G T n hn
  invFun := divideFull G T n hn
  left_inv := divideFull_multiplyToKernel G T n hn
  right_inv := multiplyToKernel_divideFull G T n hn
  continuous_toFun := (continuous_id.nsmul n).subtype_mk _
  continuous_invFun := continuous_divideFull G T n hn

/-- On the full limit, multiplication identifies the limit with the open kernel
of evaluation at its positive multiplier. -/
theorem fullMultiplicationOpenEmbeddings : FullMultiplicationOpenEmbeddings G T := by
  intro n hn
  have hopen : IsOpen (evalKernel G T n hn : Set (Full G T)) :=
    (isOpen_discrete ({0} : Set (Level G T n))).preimage
      (continuous_evaluation G T _ (fullIndex n hn))
  exact hopen.isOpenEmbedding_subtypeVal.comp (fullKernelHomeomorph G T n hn).isOpenEmbedding

private lemma nsmul_openEmbedding_retract
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
    (r : A →+ B) (s : B →+ A) (hr : Continuous r) (hs : Continuous s)
    (hrs : Function.LeftInverse r s) (n : ℕ)
    (hn : Topology.IsOpenEmbedding (fun x : A => n • x)) :
    Topology.IsOpenEmbedding (fun x : B => n • x) := by
  have he : Topology.IsEmbedding s := hrs.isEmbedding hr hs
  have hcomp : (s : B → A) ∘ (fun x : B => n • x) =
      (fun x : A => n • x) ∘ (s : B → A) := by
    funext x
    exact map_nsmul s n x
  have hi : Topology.IsEmbedding (fun x : B => n • x) :=
    Topology.IsEmbedding.of_comp (continuous_id.nsmul n) hs
      (hcomp.symm ▸ hn.isEmbedding.comp he)
  refine ⟨hi, ?_⟩
  have hrange : Set.range (fun x : B => n • x) =
      s ⁻¹' Set.range (fun x : A => n • x) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨s x, (map_nsmul s n x).symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨r x, ?_⟩
      exact (map_nsmul r n x).symm.trans ((congrArg r hx).trans (hrs y))
  rw [hrange]
  exact hn.isOpen_range.preimage hs

open PrimeComparison
open Langlands.TateTwist.Divisibility (AwayPrime)

local instance multiplicationPrimeFact (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.property⟩

private def extendPrimeProduct (m : ℕ) :
    AwayPrimeProduct G T m →+ PrimeProduct G T := by
  classical
  exact {
    toFun := fun x p => if h : Nat.Coprime (p : ℕ) m then x ⟨p, h⟩ else 0
    map_zero' := by
      funext p
      by_cases h : Nat.Coprime (p : ℕ) m <;> simp [h]
    map_add' := by
      intro x y
      funext p
      change (if h : Nat.Coprime (p : ℕ) m then (x + y) ⟨p, h⟩
        else (0 : PrimeAdic.Integral G T (p : ℕ))) =
        (if h : Nat.Coprime (p : ℕ) m then x ⟨p, h⟩
          else (0 : PrimeAdic.Integral G T (p : ℕ))) +
        (if h : Nat.Coprime (p : ℕ) m then y ⟨p, h⟩
          else (0 : PrimeAdic.Integral G T (p : ℕ)))
      by_cases h : Nat.Coprime (p : ℕ) m
      · simp only [dite_eq_left h]
        rfl
      · simp only [dite_eq_right h, add_zero] }

private lemma continuous_extendPrimeProduct (m : ℕ) :
    Continuous (extendPrimeProduct G T m) := by
  classical
  apply continuous_pi
  intro p
  by_cases h : Nat.Coprime (p : ℕ) m
  · simpa only [extendPrimeProduct, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      dite_eq_left h] using (continuous_apply (⟨p, h⟩ : AwayPrime m))
  · simpa only [extendPrimeProduct, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      dite_eq_right h] using (continuous_const : Continuous
        (fun _ : AwayPrimeProduct G T m => (0 : PrimeAdic.Integral G T (p : ℕ))))

private lemma restrict_extendPrimeProduct (m : ℕ) (x : AwayPrimeProduct G T m) :
    primeProductRestrict G T m (extendPrimeProduct G T m x) = x := by
  classical
  funext p
  exact dite_eq_left p.property

private lemma exists_awayRetract (m : ℕ) :
    ∃ (r : Full G T →+ Away G T m) (s : Away G T m →+ Full G T),
      Continuous r ∧ Continuous s ∧ Function.LeftInverse r s := by
  obtain ⟨ef, _, hf, hfi⟩ := fullPrimeProductComparison G T
  obtain ⟨ea, _, ha, hai⟩ := awayPrimeProductComparison G T m
  let r := ea.symm.toAddMonoidHom.comp ((primeProductRestrict G T m).comp ef.toAddMonoidHom)
  let s := ef.symm.toAddMonoidHom.comp ((extendPrimeProduct G T m).comp ea.toAddMonoidHom)
  refine ⟨r, s, hai.comp ((continuous_primeProductRestrict G T m).comp hf),
    hfi.comp ((continuous_extendPrimeProduct G T m).comp ha), ?_⟩
  intro x
  change ea.symm (primeProductRestrict G T m
    (ef (ef.symm (extendPrimeProduct G T m (ea x))))) = x
  rw [ef.apply_symm_apply, restrict_extendPrimeProduct, ea.symm_apply_apply]

/-- Every away limit is an additive continuous retract of the full limit, so
positive multiplication is an open embedding for every excluded modulus. -/
theorem awayMultiplicationOpenEmbeddings (m : ℕ) : AwayMultiplicationOpenEmbeddings G T m := by
  obtain ⟨r, s, hr, hs, hrs⟩ := exists_awayRetract G T m
  intro n hn
  exact nsmul_openEmbedding_retract r s hr hs hrs n (fullMultiplicationOpenEmbeddings G T n hn)

/-- Positive multiplication is an open embedding on the actual full and all
away Tate limits, for their original product-subspace topologies. -/
theorem multiplicationOpenEmbeddings : MultiplicationOpenEmbeddings G T :=
  ⟨fullMultiplicationOpenEmbeddings G T, awayMultiplicationOpenEmbeddings G T⟩

end Langlands.GroupScheme.Tate
