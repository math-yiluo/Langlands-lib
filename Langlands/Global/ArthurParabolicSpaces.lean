import Langlands.Global.AdelicIwasawaHeight
import Langlands.Global.AdelicComplexParameters
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.LanglandsDecompositionCones
import Langlands.Geometry.Building.RealTorusDuality

/-! # The spaces `𝔞_P` and `𝔞_P^*` of standard parabolic subgroups and `𝔞_0`

Arthur 2005, §4 and (5.1). For a standard parabolic subgroup `P = P_S` of a group `G` over a
number field `F` (the published closed representative `Standard.parabolicScheme i ν S`), with the
maximal split torus `i : T → G`:

* `torusToParabolic F i ν S : T ⟶ P` is the factorization of `i` through `P`;
* `restrictToTorus F i ν S : 𝔞_P^* = X(P) ⊗ ℝ → X(T) ⊗ ℝ = 𝔞_0^*` is restriction of characters
  (Arthur's embedding `𝔞_P^* ↪ 𝔞_0^*`, through (5.1));
* `toCharacterDual F i ν S : 𝔞_0 = V T → Hom(X(P), ℝ) = 𝔞_P` is its transpose, the projection
  `𝔞_0 → 𝔞_P`.

`realParameterPairing_toCharacterDual` shows that the two maps are transposes. Their comparison
with Arthur's spaces is stated in `ArthurParabolicSpacesStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Global.ArthurParabolicSpaces

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints

variable (F : Type u) [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T) (S : Set (characterLattice T))

/-- The maximal split torus `A_0 = T` as a subgroup of the standard parabolic subgroup `P_S`. -/
def torusToParabolic : T.toGrp ⟶ Standard.parabolicScheme i ν S :=
  (Standard.isRepresentedBy_parabolicHom i ν S).factorHom i
    ((range_le_torusCentralizer i).trans
      ((torusCentralizer_le_standardLevi i ν S).trans (standardLevi_le_standardParabolic i ν S)))

theorem torusToParabolic_comp : torusToParabolic F i ν S ≫ Standard.parabolicHom i ν S = i :=
  (Standard.isRepresentedBy_parabolicHom i ν S).factorHom_comp i _

/-- Restriction of real rational characters `𝔞_P^* = X(P) ⊗ ℝ → X(T) ⊗ ℝ = 𝔞_0^*`. -/
def restrictToTorus : RealCharacterParameter F (Standard.parabolicScheme i ν S) →ₗ[ℝ] Vstar T :=
  rationalCharacterRestrictReal (torusToParabolic F i ν S)

/-- The map `𝔞_0 = V T → 𝔞_P = Hom(X(P), ℝ)`, `H ↦ (χ ↦ ⟨χ|_T, H⟩)`. -/
def toCharacterDual : V T →ₗ[ℝ] RealCharacterDual F (Standard.parabolicScheme i ν S) where
  toFun v :=
    { toFun := fun χ => pair T (restrictToTorus F i ν S ((1 : ℝ) ⊗ₜ[ℤ] χ)) v
      map_zero' := by simp
      map_add' := fun χ ψ => by simp [TensorProduct.tmul_add] }
  map_add' v w := by
    apply AddMonoidHom.ext
    intro χ
    simp only [map_add]
    rfl
  map_smul' r v := by
    apply AddMonoidHom.ext
    intro χ
    simp only [map_smul, RingHom.id_apply]
    rfl

@[simp] theorem toCharacterDual_apply (v : V T)
    (χ : GroupScheme.rationalCharacters (Standard.parabolicScheme i ν S)) :
    toCharacterDual F i ν S v χ = pair T (restrictToTorus F i ν S ((1 : ℝ) ⊗ₜ[ℤ] χ)) v :=
  rfl

/-- The two comparison maps are transposes: `⟨μ, H_P⟩ = ⟨μ|_T, H⟩` for `μ ∈ 𝔞_P^*`, `H ∈ 𝔞_0`. -/
theorem realParameterPairing_toCharacterDual
    (m : RealCharacterParameter F (Standard.parabolicScheme i ν S)) (v : V T) :
    realParameterPairing F (Standard.parabolicScheme i ν S) m (toCharacterDual F i ν S v) =
      pair T (restrictToTorus F i ν S m) v := by
  induction m using TensorProduct.inductionOn with
  | tmul t χ =>
    rw [realParameterPairing_tmul, toCharacterDual_apply]
    have h : (t ⊗ₜ[ℤ] χ : RealCharacterParameter F (Standard.parabolicScheme i ν S)) =
        t • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  | add x y hx hy => simp [map_add, hx, hy]

end Langlands.Global.ArthurParabolicSpaces
