import Langlands.AlgebraicGeometry.AffineRationalDetection
import Langlands.AlgebraicGeometry.ClosedEqualizerFamily
import Langlands.GroupScheme.RepresentabilityTransfer
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The subgroup of translations preserving a morphism -/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry

section Functor

variable {S : Scheme.{u}} {G : GroupScheme S} {Y : Over S} (f : G.X ⟶ Y)

/-- The subgroup functor of right-translation parameters preserving `f`. A parameter on
`T` must preserve `f` on every test scheme `V` equipped with a map to `T`. -/
def translationStabilizer : SubgroupFunctor G where
  carrier T :=
    { carrier := {a | ∀ (V : Over S) (x : V ⟶ G.X) (t : V ⟶ T),
        (x * (t ≫ a)) ≫ f = x ≫ f}
      one_mem' := by
        intro V x t
        rw [MonObj.comp_one, mul_one]
      mul_mem' := fun {a b} ha hb ↦ by
        intro V x t
        change (x * (t ≫ (a * b))) ≫ f = x ≫ f
        rw [MonObj.comp_mul, ← mul_assoc, hb V (x * (t ≫ a)) t, ha V x t]
      inv_mem' := fun {a} ha ↦ by
        intro V x t
        have he := ha V (x * (t ≫ a⁻¹)) t
        rw [mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, mul_one] at he
        exact he.symm }
  comp_mem {T T'} q {a} ha := by
    intro V x t
    rw [← Category.assoc t q a]
    exact ha V x (t ≫ q)

lemma mem_translationStabilizer {T : Over S} (a : T ⟶ G.X) :
    a ∈ (translationStabilizer f).carrier T ↔
      ∀ (V : Over S) (x : V ⟶ G.X) (t : V ⟶ T), (x * (t ≫ a)) ≫ f = x ≫ f :=
  Iff.rfl

/-- Membership in the translation stabilizer is the equality of two morphisms on `G × T`. -/
lemma mem_translationStabilizer_iff_morphism {T : Over S} (a : T ⟶ G.X) :
    a ∈ (translationStabilizer f).carrier T ↔
      (fst G.X T * (snd G.X T ≫ a)) ≫ f = fst G.X T ≫ f := by
  rw [mem_translationStabilizer]
  refine ⟨fun h ↦ h _ _ _, fun h V x t ↦ ?_⟩
  simpa only [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd] using
    congrArg (lift x t ≫ ·) h

end Functor

section Field

local notation "Specᵣ " K:arg => Spec (CommRingCat.of K)

variable {K : Type u} [Field K] [IsAlgClosed K]
  {G : GroupScheme (Specᵣ K)} {Y : Over (Specᵣ K)} [IsSeparated Y.hom]
  [IsReduced G.X.left] [LocallyOfFiniteType G.X.hom] (f : G.X ⟶ Y)

/-- Preservation of `f` by a translation parameter can be tested by translating the
rational points of any dense open. The parameter scheme may be nonreduced. -/
lemma mem_translationStabilizer_iff_rational {T : Over (Specᵣ K)}
    (a : T ⟶ G.X) (U : G.X.left.Opens) (hU : Dense (U : Set G.X.left)) :
    a ∈ (translationStabilizer f).carrier T ↔
      ∀ x : 𝟙_ (Over (Specᵣ K)) ⟶ G.X, x.left (IsLocalRing.closedPoint K) ∈ U →
        ((toUnit T ≫ x) * a) ≫ f = toUnit T ≫ x ≫ f := by
  constructor
  · intro h x hx
    simpa only [Category.id_comp, Category.assoc] using
      (mem_translationStabilizer f a).mp h T (toUnit T ≫ x) (𝟙 T)
  · intro h
    rw [mem_translationStabilizer_iff_morphism]
    apply hom_ext_of_rational_slices U hU
    intro x hx
    rw [← Category.assoc (rationalSlice x T) _ f, MonObj.comp_mul, rationalSlice_fst,
      ← Category.assoc (rationalSlice x T) (snd G.X T) a, rationalSlice_snd, Category.id_comp,
      rationalSlice_fst_assoc]
    exact h x hx

/-- A reduced group scheme locally of finite type over an algebraically closed field has a
closed translation stabilizer for each morphism to a separated target. -/
theorem translationStabilizer_isClosedRepresentable :
    (translationStabilizer f).IsClosedRepresentable := by
  let L (x : 𝟙_ (Over (Specᵣ K)) ⟶ G.X) : G.X ⟶ Y :=
    ((toUnit G.X ≫ x) * 𝟙 G.X) ≫ f
  let R (x : 𝟙_ (Over (Specᵣ K)) ⟶ G.X) : G.X ⟶ Y := toUnit G.X ≫ x ≫ f
  let i := simultaneousEqualizerι L R
  have : Mono i := Over.mono_of_mono_left _
  apply (translationStabilizer f).isClosedRepresentable_of_scheme i
  intro T a
  rw [mem_translationStabilizer_iff_rational f a (⊤ : G.X.left.Opens) (by simp)]
  have he (x : 𝟙_ (Over (Specᵣ K)) ⟶ G.X) : a ≫ L x = a ≫ R x ↔
      ((toUnit T ≫ x) * a) ≫ f = toUnit T ≫ x ≫ f := by
    simp only [L, R, ← Category.assoc, MonObj.comp_mul, comp_toUnit, Category.comp_id]
  constructor
  · intro h
    have hh (x) : a ≫ L x = a ≫ R x := (he x).mpr (h x (by trivial))
    exact ⟨simultaneousEqualizerLift L R a hh, simultaneousEqualizerLift_ι L R a hh⟩
  · rintro ⟨b, rfl⟩ x hx
    exact (he x).mp (by rw [Category.assoc, simultaneousEqualizer_condition L R x,
      ← Category.assoc])

/-- For a finite morphism to a separated target, the translation stabilizer is a finite
closed subgroup scheme; its inclusion represents the stabilizer on all tests. -/
theorem exists_finite_translationStabilizer [IsFinite f.left] :
    ∃ (H : GroupScheme (Specᵣ K)) (i : H ⟶ G), IsClosedSubgroup i ∧ IsFinite H.X.hom ∧
      (translationStabilizer f).IsRepresentedBy i := by
  obtain ⟨H, i, hi, hclosed⟩ := translationStabilizer_isClosedRepresentable f
  refine ⟨H, i, hclosed, ?_, hi⟩
  have hmem : i.hom.hom ∈ (translationStabilizer f).carrier H.X := by
    rw [← hi.2, SubgroupFunctor.mem_range]
    exact ⟨𝟙 H.X, Category.id_comp _⟩
  let z : 𝟙_ (Over (Specᵣ K)) ⟶ Y := (1 : 𝟙_ (Over (Specᵣ K)) ⟶ G.X) ≫ f
  have hz : i.hom.hom ≫ f = toUnit H.X ≫ z := by
    have h := (mem_translationStabilizer f i.hom.hom).mp hmem H.X 1 (𝟙 H.X)
    simpa only [Category.id_comp, one_mul, z, ← Category.assoc, MonObj.comp_one] using h
  have hz' : i.hom.hom.left ≫ f.left = H.X.hom ≫ z.left := congrArg Over.Hom.left hz
  let b := pullback.lift i.hom.hom.left H.X.hom hz'
  have : IsClosedImmersion (z.left ≫ Y.hom) := by
    rw [Over.w z]
    change IsClosedImmersion (𝟙 (Specᵣ K))
    infer_instance
  have : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left Y.hom
  have : IsClosedImmersion (i.hom.hom.left) := hclosed
  have : IsClosedImmersion (b ≫ pullback.fst f.left z.left) := by
    rw [show b ≫ pullback.fst f.left z.left = i.hom.hom.left from pullback.lift_fst ..]
    infer_instance
  have : IsClosedImmersion b := IsClosedImmersion.of_comp b (pullback.fst f.left z.left)
  rw [← show b ≫ pullback.snd f.left z.left = H.X.hom from pullback.lift_snd ..]
  infer_instance

end Field
end Langlands.GroupScheme
