import Langlands.Cohomology.Tate.ZeroDefinitions
import Langlands.ClassFieldTheory.Local.CyclicClass
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

noncomputable section

open CategoryTheory CategoryTheory.Limits groupCohomology
open scoped BigOperators

namespace Langlands.ClassFieldTheory.Local

universe u

variable (G : Type u) [Group G]

/-- The trivial rational coefficient representation in the cohomology universe. -/
abbrev trivialRationalCoefficients := Rep.trivial IntegerScalars.{u} G (ULift.{u} ℚ)

/-- The trivial rational-mod-integers representation in the cohomology universe. -/
abbrev trivialRationalQuotientCoefficients :=
  Rep.trivial IntegerScalars.{u} G (ULift.{u} RationalModIntegers)

private def liftAdditiveMap {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    ULift.{u} A →ₗ[IntegerScalars.{u}] ULift.{u} B where
  toFun x := ULift.up (f x.down)
  map_add' x y := ULift.ext (map_add f x.down y.down)
  map_smul' z x := ULift.ext (map_zsmul f z.down x.down)

private def integerToRational : Langlands.Tate.integralTrivial G ⟶ trivialRationalCoefficients G :=
  Rep.ofHom ⟨liftAdditiveMap (Int.castAddHom ℚ), fun _ => rfl⟩

private def rationalToQuotient : trivialRationalCoefficients G ⟶ trivialRationalQuotientCoefficients G :=
  Rep.ofHom ⟨liftAdditiveMap rationalClass, fun _ => rfl⟩

/-- The actual short complex of trivial coefficients `ℤ → ℚ → ℚ/ℤ`. -/
def rationalCoefficientSequence : ShortComplex (Rep.{u} IntegerScalars.{u} G) :=
  ShortComplex.mk (integerToRational G) (rationalToQuotient G) (by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    apply ULift.ext
    change rationalClass (z.down : ℚ) = 0
    exact (Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff _).2 ⟨z.down, rfl⟩)

@[simp]
theorem rationalCoefficientSequence_f_down (z : IntegerScalars.{u}) :
    ((rationalCoefficientSequence G).f.hom z).down = (z.down : ℚ) := rfl

@[simp]
theorem rationalCoefficientSequence_g_down (q : ULift.{u} ℚ) :
    ((rationalCoefficientSequence G).g.hom q).down = rationalClass q.down := rfl

private theorem representationExact {R : Type u} [CommRing R]
    (S : ShortComplex (Rep.{u} R G))
    (h : ∀ x : S.X₂, S.g.hom x = 0 → ∃ y : S.X₁, S.f.hom y = x) : S.Exact :=
  (S.exact_map_iff_of_faithful (forget₂ (Rep R G) (ModuleCat R))).1
    ((ShortComplex.moduleCat_exact_iff _).2 h)

theorem rationalCoefficientSequence_shortExact : (rationalCoefficientSequence G).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ((Rep.mono_iff_injective _).2 ?_)
    ((Rep.epi_iff_surjective _).2 ?_)
  · apply representationExact G
    intro q hq
    change (ULift.up (rationalClass q.down) : ULift.{u} RationalModIntegers) = 0 at hq
    obtain ⟨z, hz⟩ := (Langlands.ClassFieldTheory.Global.FundamentalClass.rationalClass_eq_zero_iff _).1 (congrArg ULift.down hq)
    exact ⟨ULift.up z, ULift.ext hz⟩
  · intro z w h
    apply ULift.ext
    exact Int.cast_injective (congrArg ULift.down h)
  · intro q
    obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℚ)) q.down
    exact ⟨ULift.up a, ULift.ext ha⟩

section Finite

variable [Finite G]

private theorem isZero_H1_trivialRational : IsZero (H1 (trivialRationalCoefficients G)) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have hzero (f : Additive G →+ trivialRationalCoefficients G) : f = 0 := by
    apply AddMonoidHom.ext
    intro x
    have hz : Nat.card G • f x = 0 := by
      rw [← map_nsmul]
      have hx : Nat.card G • x = 0 := by
        change Additive.ofMul (x.toMul ^ Nat.card G) = 0
        rw [pow_card_eq_one', ofMul_one]
      rw [hx, map_zero]
    apply ULift.ext
    have hq : Nat.card G • (f x).down = 0 := congrArg ULift.down hz
    rw [nsmul_eq_mul] at hq
    exact (mul_eq_zero.mp hq).resolve_left (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine ⟨fun x y => (H1IsoOfIsTrivial (trivialRationalCoefficients G)).toLinearEquiv.injective ?_⟩
  exact (hzero _).trans (hzero _).symm

private theorem isZero_H2_trivialRational : IsZero (H2 (trivialRationalCoefficients G)) := by
  classical
  let := Fintype.ofFinite G
  rw [ModuleCat.isZero_iff_subsingleton]
  apply subsingleton_of_forall_eq 0
  intro x
  induction x using H2_induction_on with
  | h c =>
    apply (H2π_eq_zero_iff c).2
    let s (g : G) : ℚ := ∑ j : G, (c (g, j)).down
    let d : ℚ := Fintype.card G
    have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    refine ⟨fun g => ULift.up (s g / d), ?_⟩
    funext gh
    obtain ⟨g, h⟩ := gh
    have hsum : (∑ j : G, ((c (g * h, j)).down + (c (g, h)).down)) =
        ∑ j : G, ((c (h, j)).down + (c (g, h * j)).down) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg ULift.down ((mem_cocycles₂_iff _).1 c.property g h j)
    have hreindex : (∑ j : G, (c (g, h * j)).down) = s g :=
      Equiv.sum_comp (Equiv.mulLeft h) (fun j => (c (g, j)).down)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hreindex] at hsum
    have hs : s (g * h) + d * (c (g, h)).down = s h + s g := hsum
    apply ULift.ext
    rw [groupCohomology.d₁₂_hom_apply]
    change s h / d - s (g * h) / d + s g / d = (c (g, h)).down
    rw [← sub_div, ← add_div, div_eq_iff hd]
    linear_combination -hs

/-- The connecting isomorphism `H¹(G, ℚ/ℤ) ≅ H²(G, ℤ)` for a finite group. -/
def rationalConnectingIso : H1 (trivialRationalQuotientCoefficients G) ≅
    H2 (Langlands.Tate.integralTrivial G) := by
  let h := rationalCoefficientSequence_shortExact G
  have hiso : IsIso (groupCohomology.δ h 1 2 rfl) :=
    isIso_δ_of_isZero h 1 (isZero_H1_trivialRational G) (isZero_H2_trivialRational G)
  exact @asIso _ _ _ _ (groupCohomology.δ h 1 2 rfl) hiso

theorem rationalConnectingIso_hom :
    (rationalConnectingIso G).hom =
      groupCohomology.δ (rationalCoefficientSequence_shortExact G) 1 2 rfl := rfl

end Finite

end Langlands.ClassFieldTheory.Local
