import Langlands.Global.AdelicIntertwiningOperator

/-! # Twisted right translation on functions in the adelic induced model

Conjugate ordinary right translation by the parameter twist of the normalized inducing
functions. This gives the pointwise formulas for the defining Eisenstein sum and
intertwining integral; no continuation or density assertion is made. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
  {K : Subgroup (AdelicGroupPoints F G)}

/-- The parameter-dependent right translate of `φ`, obtained by translating `φ_λ` and
untwisting. Here `φ` is in Lapid's normalization, with the half-modulus factor already
in `φ`; the twist therefore uses `λ` alone. -/
def IsIwasawaCompact.inducedRightTranslate (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (y : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) : ℂ :=
  hK.heightPower (-lam) g * hK.parameterTwist φ lam (g * y)

/-- The height powers for opposite parameters multiply to one. -/
theorem IsIwasawaCompact.heightPower_neg_mul (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.heightPower (-lam) g * hK.heightPower lam g = 1 := by
  simp [IsIwasawaCompact.heightPower, ← Complex.exp_add]

/-- Twisting the translated coefficient gives the right translate of the twisted function. -/
theorem IsIwasawaCompact.parameterTwist_inducedRightTranslate (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (y : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.parameterTwist (hK.inducedRightTranslate lam y φ) lam g =
      hK.parameterTwist φ lam (g * y) := by
  rw [IsIwasawaCompact.parameterTwist, IsIwasawaCompact.inducedRightTranslate,
    mul_right_comm (hK.heightPower (-lam) g), IsIwasawaCompact.heightPower_neg_mul, one_mul]

@[simp] theorem IsIwasawaCompact.inducedRightTranslate_one (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (φ : AdelicGroupPoints F G → ℂ) :
    hK.inducedRightTranslate lam 1 φ = φ := by
  funext g
  rw [IsIwasawaCompact.inducedRightTranslate, mul_one, IsIwasawaCompact.parameterTwist,
    mul_left_comm, IsIwasawaCompact.heightPower_neg_mul, mul_one]

/-- Apply right translation by `z` first to the function, then by `y`. -/
theorem IsIwasawaCompact.inducedRightTranslate_mul (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (y z : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) :
    hK.inducedRightTranslate lam y (hK.inducedRightTranslate lam z φ) =
      hK.inducedRightTranslate lam (y * z) φ := by
  funext g
  rw [IsIwasawaCompact.inducedRightTranslate, hK.parameterTwist_inducedRightTranslate, mul_assoc]
  rfl

/-- The twist disappears for right translation by `K`. -/
theorem IsIwasawaCompact.inducedRightTranslate_of_mem
    [IsAffine G.X.left] [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
    (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) {y : AdelicGroupPoints F G} (hy : y ∈ K)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.inducedRightTranslate lam y φ g = φ (g * y) := by
  have hpow : hK.heightPower lam (g * y) = hK.heightPower lam g := by
    rw [IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, hK.height_mul_right g hy]
  rw [IsIwasawaCompact.inducedRightTranslate, IsIwasawaCompact.parameterTwist, hpow,
    mul_left_comm, IsIwasawaCompact.heightPower_neg_mul, mul_one]

/-- Right equivariance of the defining Eisenstein sum, by equality of each summand. -/
theorem IsIwasawaCompact.eisensteinSeries_inducedRightTranslate (hK : IsIwasawaCompact p K)
    (lam : ComplexCharacterParameter F P) (y : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries (hK.inducedRightTranslate lam y φ) lam g =
      hK.eisensteinSeries φ lam (g * y) := by
  unfold IsIwasawaCompact.eisensteinSeries
  refine tsum_congr fun c => ?_
  simp only [IsIwasawaCompact.eisensteinTerm, hK.parameterTwist_inducedRightTranslate, mul_assoc]

section Intertwining

variable [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  {U M Q V M' : GroupScheme (Spec (CommRingCat.of F))} [IsAffine V.X.left]

/-- Right equivariance of the defining intertwining integral, by equality of integrands. -/
theorem IsIwasawaCompact.intertwiningIntegral_inducedRightTranslate (hK : IsIwasawaCompact p K)
    (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (lam : ComplexCharacterParameter F P) (y : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.intertwiningIntegral iU j w (hK.inducedRightTranslate lam y φ) lam g =
      hK.intertwiningIntegral iU j w φ lam (g * y) := by
  unfold IsIwasawaCompact.intertwiningIntegral
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [IsIwasawaCompact.intertwiningIntegrand, hK.parameterTwist_inducedRightTranslate,
    mul_assoc]

/-- Equivariance of the defining intertwining operator with `λ` twisted translation on the
source and `wλ` twisted translation on the target. -/
theorem IsIwasawaCompact.intertwiningOperator_inducedRightTranslate
    [IsAffine Q.X.left] {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
    (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
    (iU : U ⟶ P) (l : M ⟶ P) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (c : M' ⟶ M) (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (lam : ComplexCharacterParameter F P) (y : AdelicGroupPoints F G)
    (φ : AdelicGroupPoints F G → ℂ) (g : AdelicGroupPoints F G) :
    hK.intertwiningOperator hK' iU l iV c π' w (hK.inducedRightTranslate lam y φ) lam g =
      hK'.inducedRightTranslate (weylParameter l c π' lam) y
        (hK.intertwiningOperator hK' iU l iV c π' w φ lam) g := by
  simp only [IsIwasawaCompact.intertwiningOperator, hK.intertwiningIntegral_inducedRightTranslate,
    IsIwasawaCompact.inducedRightTranslate, IsIwasawaCompact.parameterTwist]
  rw [mul_right_comm (hK'.heightPower (-weylParameter l c π' lam) (g * y)),
    IsIwasawaCompact.heightPower_neg_mul, one_mul]

end Intertwining

end Langlands.Global.AdelicGroupPoints
