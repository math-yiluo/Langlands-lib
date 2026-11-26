import Langlands.GroupScheme.Dilatation.CoordinateAlgebra
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree

/-! # The affine blow-up algebra on flat tests -/

noncomputable section

namespace Langlands.GroupScheme.Dilatation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The affine blow-up algebra for a denominator from the base. -/
abbrev blowupAlgebra (r : R) (I : Ideal A) := coordinateAlgebra (algebraMap R A r) I

/-- The structural map from the original coordinate ring. -/
abbrev blowupMap (r : R) (I : Ideal A) : A →ₐ[R] blowupAlgebra r I :=
  IsScalarTower.toAlgHom R A _

section Flat

variable [IsDomain R]

/-- Localization at a nonzero base element is injective on a flat algebra. -/
theorem away_injective [Module.Flat R A] {r : R} (hr : r ≠ 0) :
    Function.Injective (algebraMap A (Localization.Away (algebraMap R A r))) := by
  apply IsLocalization.injective (M := Submonoid.powers (algebraMap R A r))
  rintro _ ⟨n, rfl⟩
  change (algebraMap R A r) ^ n ∈ nonZeroDivisors A
  rw [← map_pow, mem_nonZeroDivisors_iff_left]
  intro x hx
  exact smul_right_injective A (pow_ne_zero n hr) <| by
    simpa only [Algebra.smul_def, mul_zero] using hx

instance blowupAlgebra_torsionFree [Module.Flat R A] (r : R) (I : Ideal A) :
    Module.IsTorsionFree R (blowupAlgebra r I) :=
  Subtype.val_injective.moduleIsTorsionFree _ fun _ _ => rfl

omit [IsDomain R] in
/-- Clearing a power of the denominator puts any blow-up element in the image of `A`. -/
theorem exists_mul_pow_eq (r : R) (I : Ideal A) (s : blowupAlgebra r I) :
    ∃ (n : ℕ) (a : A), s * algebraMap R (blowupAlgebra r I) r ^ n = blowupMap r I a := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (algebraMap R A r) s.val
  exact ⟨n, a, Subtype.ext h⟩

variable {B : Type*} [CommRing B] [Algebra R B] [Module.Flat R B]
  {r : R} (hr : r ≠ 0) (I : Ideal A)

include hr in
/-- Maps to a flat test algebra are determined by their restriction to the original algebra. -/
theorem blowupMap_ext {f g : blowupAlgebra r I →ₐ[R] B}
    (h : f.comp (blowupMap r I) = g.comp (blowupMap r I)) : f = g := by
  ext s
  obtain ⟨n, a, ha⟩ := exists_mul_pow_eq r I s
  apply smul_right_injective B (pow_ne_zero n hr)
  change r ^ n • f s = r ^ n • g s
  have h' : r ^ n • s = blowupMap r I a := by
    simpa only [Algebra.smul_def, map_pow, mul_comm] using ha
  rw [← map_smul, ← map_smul, h']
  exact DFunLike.congr_fun h a

omit [IsDomain R] [Module.Flat R B] in
/-- Every divided generator maps to a multiple of the denominator before localization. -/
theorem maps_centre_to_span (f : blowupAlgebra r I →ₐ[R] B) :
    ∀ a ∈ I, f (blowupMap r I a) ∈ Ideal.span {algebraMap R B r} := by
  intro a ha
  apply Ideal.mem_span_singleton.mpr
  refine ⟨f (dividedElement (algebraMap R A r) I ⟨a, ha⟩), ?_⟩
  change f (algebraMap A (blowupAlgebra r I) a) = _
  have h := congrArg f (mul_dividedElement (algebraMap R A r) I ⟨a, ha⟩)
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] using h.symm

private def localizedMap (r : R) (f : A →ₐ[R] B) :
    Localization.Away (algebraMap R A r) →ₐ[R] Localization.Away (algebraMap R B r) :=
  IsLocalization.Away.liftAlgHom (algebraMap R A r)
    (f := (IsScalarTower.toAlgHom R B _).comp f) (by
      change IsUnit (algebraMap B _ (f (algebraMap R A r)))
      rw [f.commutes]
      exact IsLocalization.Away.algebraMap_isUnit _)

omit [IsDomain R] [Module.Flat R B] in
@[simp] private theorem localizedMap_algebraMap (f : A →ₐ[R] B) (a : A) :
    localizedMap r f (algebraMap A _ a) = algebraMap B _ (f a) :=
  by simp [localizedMap, IsLocalization.Away.liftAlgHom_apply]

omit [IsDomain R] [Module.Flat R B] in
private theorem localizedMap_mem_range (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a ∈ Ideal.span {algebraMap R B r}) (s : blowupAlgebra r I) :
    localizedMap r f s.val ∈ (IsScalarTower.toAlgHom R B _).range := by
  obtain ⟨s, hs⟩ := s
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hf a ha)
    refine ⟨b, ?_⟩
    apply (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap R B r))
      (algebraMap R B r)).mul_left_cancel
    change algebraMap B (Localization.Away (algebraMap R B r)) (algebraMap R B r) *
        algebraMap B _ b = _ * localizedMap r f (divided (algebraMap R A r) a)
    have he : localizedMap r f (algebraMap A _ (algebraMap R A r)) =
        algebraMap B (Localization.Away (algebraMap R B r)) (algebraMap R B r) :=
      (localizedMap_algebraMap f _).trans (congrArg _ (f.commutes r))
    calc
      _ = algebraMap B _ (f a) := by rw [hb, map_mul]
      _ = localizedMap r f (algebraMap A _ (algebraMap R A r) *
          divided (algebraMap R A r) a) := by rw [mul_divided, localizedMap_algebraMap]
      _ = _ := by rw [map_mul, he]
  | algebraMap a =>
    exact ⟨f a, (localizedMap_algebraMap f a).symm⟩
  | add x y hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy => rw [map_mul]; exact mul_mem ihx ihy

/-- A point of the original scheme lifts when every element of the centre ideal is divisible
by the denominator in the test algebra. -/
def liftBlowup (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a ∈ Ideal.span {algebraMap R B r}) : blowupAlgebra r I →ₐ[R] B :=
  (AlgEquiv.ofInjective (IsScalarTower.toAlgHom R B _) (away_injective hr)).symm.toAlgHom.comp
    (((localizedMap r f).comp ((inclusion _ I).restrictScalars R)).codRestrict _
      (localizedMap_mem_range I f hf))

@[simp] theorem liftBlowup_comp (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a ∈ Ideal.span {algebraMap R B r}) :
    (liftBlowup hr I f hf).comp (blowupMap r I) = f := by
  ext a
  let e := AlgEquiv.ofInjective (IsScalarTower.toAlgHom R B _) (away_injective hr)
  apply e.injective
  change e (e.symm _) = e (f a)
  rw [AlgEquiv.apply_symm_apply]
  exact Subtype.ext (localizedMap_algebraMap f a)

include hr in
/-- Universal property of the affine blow-up algebra on flat affine tests. -/
theorem existsUnique_liftBlowup_iff (f : A →ₐ[R] B) :
    (∃! g : blowupAlgebra r I →ₐ[R] B, g.comp (blowupMap r I) = f) ↔
      ∀ a ∈ I, f a ∈ Ideal.span {algebraMap R B r} := by
  constructor
  · rintro ⟨g, rfl, -⟩
    exact maps_centre_to_span I g
  · intro hf
    exact ⟨liftBlowup hr I f hf, liftBlowup_comp hr I f hf,
      fun _ h => blowupMap_ext hr I (h.trans (liftBlowup_comp hr I f hf).symm)⟩

end Flat

instance blowupAlgebra_flat [IsDedekindDomain R] [Module.Flat R A] (r : R) (I : Ideal A) :
    Module.Flat R (blowupAlgebra r I) := inferInstance

/-- Finitely many ideal generators suffice to generate the affine blow-up algebra over `A`. -/
theorem blowupAlgebra_finiteType_over (r : R) (I : Ideal A) (hI : I.FG) :
    Algebra.FiniteType A (blowupAlgebra r I) := by
  obtain ⟨s, hs⟩ := hI
  let π := algebraMap R A r
  let L : A →ₗ[A] Localization.Away π :=
    (Algebra.linearMap A A).smulRight (IsLocalization.Away.invSelf π :
      Localization.Away π)
  have hL (a : A) : L a = divided π a := by
    simp [L, divided, Algebra.smul_def, mul_comm]
  have hgen : coordinateAlgebra π I = Algebra.adjoin A (L '' (s : Set A)) := by
    apply le_antisymm
    · rw [coordinateAlgebra_le_iff]
      intro a ha
      rw [← hL]
      change L a ∈ (Algebra.adjoin A (L '' (s : Set A))).toSubmodule
      have hle : Submodule.span A (s : Set A) ≤
          (Algebra.adjoin A (L '' (s : Set A))).toSubmodule.comap L := by
        rw [Submodule.span_le]
        intro x hx
        exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have ha' : a ∈ Ideal.span (s : Set A) := hs.symm ▸ ha
      exact hle ha'
    · apply Algebra.adjoin_le
      rintro _ ⟨a, ha, rfl⟩
      rw [hL]
      exact divided_mem π I (hs ▸ Submodule.subset_span ha)
  change Algebra.FiniteType A (coordinateAlgebra π I)
  rw [hgen]
  exact Algebra.FiniteType.adjoin_of_finite (s.finite_toSet.image L)

instance blowupAlgebra_finiteType [IsNoetherianRing R] [Algebra.FiniteType R A]
    (r : R) (I : Ideal A) : Algebra.FiniteType R (blowupAlgebra r I) := by
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
    (blowupAlgebra_finiteType_over r I (IsNoetherian.noetherian I))

end Langlands.GroupScheme.Dilatation
