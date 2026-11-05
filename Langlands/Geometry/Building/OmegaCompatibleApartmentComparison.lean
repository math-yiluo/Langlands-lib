import Langlands.Geometry.Building.KPCentralizerCompatibility
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness

/-! # Equivariant comparison of full omega-compatible apartments -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace FiniteQuotientAffineComparison

variable {N W V : Type*} [Group N] [Group W] [Fintype W]
    [AddCommGroup V] [Module ℝ V]
    (q : N →* W) (hq : Function.Surjective q)
    (L : N →* (V ≃ₗ[ℝ] V)) (c : N → V)

/-- The average of a cocycle over chosen lifts of a finite quotient. -/
def average : V :=
  (Fintype.card W : ℝ)⁻¹ • ∑ w : W, c (Classical.choose (hq w))

/-- A cocycle constant on the fibers of a finite quotient is a coboundary. -/
theorem average_spec
    (hc : ∀ n m, c (n * m) = c n + L n (c m))
    (hfiber : ∀ n m, q n = q m → c n = c m) (n : N) :
    c n + L n (average q hq c) = average q hq c := by
  classical
  let s : W → N := fun w => Classical.choose (hq w)
  have hs (w : W) : q (s w) = w := Classical.choose_spec (hq w)
  have hsum : (∑ w : W, c (n * s w)) = ∑ w : W, c (s w) := by
    calc
      _ = ∑ w : W, c (s (q n * w)) := by
        apply Finset.sum_congr rfl
        intro w _
        apply hfiber
        rw [map_mul, hs, hs]
      _ = _ := Equiv.sum_comp (Equiv.mulLeft (q n)) (fun w => c (s w))
  have hsum' : (Fintype.card W : ℝ) • c n +
      L n (∑ w : W, c (s w)) = ∑ w : W, c (s w) := by
    simpa only [hc, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Nat.cast_smul_eq_nsmul, map_sum] using hsum
  have hcard : (Fintype.card W : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change c n + L n ((Fintype.card W : ℝ)⁻¹ • ∑ w : W, c (s w)) =
    (Fintype.card W : ℝ)⁻¹ • ∑ w : W, c (s w)
  calc
    _ = (Fintype.card W : ℝ)⁻¹ •
        ((Fintype.card W : ℝ) • c n + L n (∑ w : W, c (s w))) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ hcard, one_smul, map_smul]
    _ = _ := congrArg ((Fintype.card W : ℝ)⁻¹ • ·) hsum'

end FiniteQuotientAffineComparison

namespace KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (D E : KPApartmentData i (localFieldOrder F))

/-- The difference of the two displacement cocycles at chosen apartment points. -/
def comparisonDefect (x : D.Apartment) (y : E.Apartment)
    (n : normalizerPoints i) : TranslationSpace i :=
  (n • y -ᵥ y) - (n • x -ᵥ x)

theorem displacement_mul (x : D.Apartment) (n m : normalizerPoints i) :
    (n * m) • x -ᵥ x =
      translationAction i n (m • x -ᵥ x) + (n • x -ᵥ x) := by
  rw [mul_smul]
  have h := ((D.normalizerAffineEquiv n).toAffineMap.linearMap_vsub (m • x) x).symm
  change n • (m • x) -ᵥ n • x = translationAction i n (m • x -ᵥ x) at h
  rw [← h, vsub_add_vsub_cancel]

theorem comparisonDefect_mul (x : D.Apartment) (y : E.Apartment)
    (n m : normalizerPoints i) :
    comparisonDefect D E x y (n * m) =
      comparisonDefect D E x y n +
        translationAction i n (comparisonDefect D E x y m) := by
  simp only [comparisonDefect, displacement_mul, map_sub]
  abel

variable (C : CentralizerDatum i)
    (hD : D.IsOmegaCompatible C) (hE : E.IsOmegaCompatible C)

include C hD hE in
theorem comparisonDefect_eq_zero_of_mem_centralizerPoints
    (x : D.Apartment) (y : E.Apartment) (n : normalizerPoints i)
    (hn : (n : rationalPoints G) ∈ centralizerPoints i) :
    comparisonDefect D E x y n = 0 := by
  rw [← torusCentralizer_carrier_base, ← C.isRepresentedBy.2] at hn
  change ∃ z : rationalPoints C.Z, rationalPoints.map C.j z = (n : rationalPoints G) at hn
  obtain ⟨z, hz⟩ := hn
  have hnz : C.toNormalizer z = n := Subtype.ext hz
  rw [comparisonDefect, ← hnz, hD.smul_eq_vadd, hE.smul_eq_vadd,
    vadd_vsub, vadd_vsub, sub_self]

include C hD hE in
theorem comparisonDefect_eq_of_weylClass_eq
    (x : D.Apartment) (y : E.Apartment) (n m : normalizerPoints i)
    (hnm : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk m) :
    comparisonDefect D E x y n = comparisonDefect D E x y m := by
  have hz : (m⁻¹ * n : normalizerPoints i) ∈
      (centralizerPoints i).subgroupOf (normalizerPoints i) :=
    QuotientGroup.eq.mp hnm.symm
  have hc := comparisonDefect_eq_zero_of_mem_centralizerPoints D E C hD hE x y
    (m⁻¹ * n) hz
  have hn : n = m * (m⁻¹ * n) := by group
  conv_lhs => rw [hn]
  rw [comparisonDefect_mul, hc, map_zero, add_zero]

/-- The averaging correction for two full omega-compatible apartment actions. -/
def comparisonCorrection [Fintype (relativeWeylGroup i)]
    (x : D.Apartment) (y : E.Apartment) : TranslationSpace i :=
  FiniteQuotientAffineComparison.average
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
    (QuotientGroup.mk'_surjective _) (comparisonDefect D E x y)

include C hD hE in
theorem comparisonCorrection_spec [Fintype (relativeWeylGroup i)]
    (x : D.Apartment) (y : E.Apartment) (n : normalizerPoints i) :
    comparisonDefect D E x y n +
        translationAction i n (comparisonCorrection D E x y) =
      comparisonCorrection D E x y :=
  FiniteQuotientAffineComparison.average_spec _ _ _ _
    (comparisonDefect_mul D E x y)
    (comparisonDefect_eq_of_weylClass_eq D E C hD hE x y) n

/-- An affine comparison with identity derivative, obtained by averaging over the
actual finite relative Weyl quotient. -/
def omegaCompatibleApartmentAffineEquiv
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    D.Apartment ≃ᵃ[ℝ] E.Apartment := by
  let _ := hD
  let _ := hE
  let := hG.finite_relativeWeylGroup i hi
  let := Fintype.ofFinite (relativeWeylGroup i)
  let x : D.Apartment := Classical.arbitrary _
  let y : E.Apartment := Classical.arbitrary _
  exact (AffineEquiv.vaddConst ℝ x).symm.trans
    (AffineEquiv.vaddConst ℝ (comparisonCorrection D E x y +ᵥ y))

@[simp]
theorem omegaCompatibleApartmentAffineEquiv_linear
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) :
    (omegaCompatibleApartmentAffineEquiv D E C hD hE hG hi).linear =
      LinearEquiv.refl ℝ (TranslationSpace i) := by
  rfl

theorem omegaCompatibleApartmentAffineEquiv_smul
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (n : normalizerPoints i) (z : D.Apartment) :
    omegaCompatibleApartmentAffineEquiv D E C hD hE hG hi (n • z) =
      n • omegaCompatibleApartmentAffineEquiv D E C hD hE hG hi z := by
  let := hG.finite_relativeWeylGroup i hi
  let := Fintype.ofFinite (relativeWeylGroup i)
  let x : D.Apartment := Classical.arbitrary _
  let y : E.Apartment := Classical.arbitrary _
  let b := comparisonCorrection D E x y
  change (n • z -ᵥ x) +ᵥ (b +ᵥ y) =
    n • ((z -ᵥ x) +ᵥ (b +ᵥ y))
  have h := comparisonCorrection_spec D E C hD hE x y n
  change (n • y -ᵥ y) - (n • x -ᵥ x) + translationAction i n b = b at h
  have h' : (n • x -ᵥ x) + b =
      translationAction i n b + (n • y -ᵥ y) := by
    calc
      _ = (n • x -ᵥ x) +
          ((n • y -ᵥ y) - (n • x -ᵥ x) + translationAction i n b) :=
        congrArg ((n • x -ᵥ x) + ·) h.symm
      _ = _ := by abel
  have hz := ((D.normalizerAffineEquiv n).toAffineMap.linearMap_vsub z x).symm
  change n • z -ᵥ n • x = translationAction i n (z -ᵥ x) at hz
  rw [smul_vadd, smul_vadd, vadd_vadd, vadd_vadd,
    ← vsub_add_vsub_cancel (n • z) (n • x) x, hz, add_assoc, h',
    ← add_assoc, ← vadd_vadd, vsub_vadd]

end KPApartmentData

end Langlands.Geometry.Building
