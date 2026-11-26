import Langlands.Geometry.Manifold.SmoothGroupHomLie
import Langlands.Automorphic.GroupSchemeInfiniteTranslation
import Langlands.Global.AdelicGroupPointTopology

/-! # Enveloping maps, character shifts and unipotent right ideals at infinity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Algebra.ComplexLieExtension

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

/-- The complexification of a real functional vanishing on brackets vanishes on brackets. -/
theorem linear_lie_eq_zero (lam : L →ₗ[ℝ] ℂ) (hlam : ∀ X Y : L, lam ⁅X, Y⁆ = 0)
    (U V : ℂ ⊗[ℝ] L) : linear lam ⁅U, V⁆ = 0 := by
  induction U using TensorProduct.inductionOn with
  | tmul z X =>
    induction V using TensorProduct.inductionOn with
    | tmul w Y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, linear_tmul, hlam, smul_zero]
    | add V₁ V₂ h₁ h₂ => rw [lie_add, map_add, h₁, h₂, add_zero]
  | add U₁ U₂ h₁ h₂ => rw [add_lie, map_add, h₁, h₂, add_zero]

/-- The complex Lie map `Y ↦ ι Y + λ(Y)` into the enveloping algebra, for a real functional
`λ` vanishing on brackets. -/
def characterShiftLie (lam : L →ₗ[ℝ] ℂ) (hlam : ∀ X Y : L, lam ⁅X, Y⁆ = 0) :
    ℂ ⊗[ℝ] L →ₗ⁅ℂ⁆ UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) :=
  { (UniversalEnvelopingAlgebra.ι ℂ).toLinearMap +
      (Algebra.linearMap ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L))).comp (linear lam) with
    map_lie' := by
      intro U V
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.add_apply,
        LieHom.coe_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
        Algebra.linearMap_apply]
      rw [linear_lie_eq_zero lam hlam, map_zero, add_zero, LieHom.map_lie, Ring.lie_def,
        Ring.lie_def]
      set a := UniversalEnvelopingAlgebra.ι ℂ U
      set b := UniversalEnvelopingAlgebra.ι ℂ V
      set p := algebraMap ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) (linear lam U)
      set q := algebraMap ℂ (UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L)) (linear lam V)
      have h₁ : a * q = q * a := (Algebra.commutes _ a).symm
      have h₂ : p * b = b * p := Algebra.commutes _ b
      have h₃ : p * q = q * p := Algebra.commutes _ q
      simp only [add_mul, mul_add]
      rw [h₁, h₂, h₃]
      abel }

/-- The enveloping automorphism shifting each generator `Y` by the scalar `λ(Y)`. -/
def characterShift (lam : L →ₗ[ℝ] ℂ) (hlam : ∀ X Y : L, lam ⁅X, Y⁆ = 0) :
    UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) →ₐ[ℂ] UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] L) :=
  UniversalEnvelopingAlgebra.lift ℂ (characterShiftLie lam hlam)

@[simp]
theorem characterShift_ι (lam : L →ₗ[ℝ] ℂ) (hlam : ∀ X Y : L, lam ⁅X, Y⁆ = 0)
    (U : ℂ ⊗[ℝ] L) :
    characterShift lam hlam (UniversalEnvelopingAlgebra.ι ℂ U) =
      UniversalEnvelopingAlgebra.ι ℂ U + algebraMap ℂ _ (linear lam U) := by
  unfold characterShift
  rw [UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

end Langlands.Algebra.ComplexLieExtension

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]

section Maps

variable {H G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] [IsAffine G.X.left]
  {e d : ℕ} (hsmoothH : SmoothOfRelativeDimension e H.X.hom)
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The archimedean point map of a morphism of group schemes is smooth for the chosen atlases. -/
theorem contMDiff_affinePointsTarget (j : H ⟶ G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F H hsmoothH
    letI := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d) ∞
      (H.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F))) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F H hsmoothH
  let := smoothChartedSpace F G hsmooth
  apply (contMDiff_iff_coordinateSmooth F G 𝓘(ℝ, smoothModel F e) hsmooth _).mpr
  exact ((contMDiff_iff_coordinateSmooth F H 𝓘(ℝ, smoothModel F e) hsmoothH id).mp
    contMDiff_id).postcomp j.hom.hom

/-- The tangent map at the identity of the archimedean point map of a morphism of group
schemes. -/
def pointTangent (j : H ⟶ G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F H hsmoothH
    letI := smoothChartedSpace F G hsmooth
    GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H) →L[ℝ]
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F H hsmoothH
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F H hsmoothH
  letI := smoothLieGroup F G hsmooth
  exact groupHomTangent 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
    (H.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)))

/-- The tangent map of a morphism of group schemes is a homomorphism of the Lie algebras of
left-invariant vector fields. -/
def pointTangentLieHom (j : H ⟶ G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F H hsmoothH
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F H hsmoothH
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H) →ₗ⁅ℝ⁆
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F H hsmoothH
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F H hsmoothH
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact
    { (pointTangent F hsmoothH hsmooth j).toLinearMap with
      map_lie' := fun {X Y} =>
        groupHomTangent_lie_of_separating 𝓘(ℝ, smoothModel F e) 𝓘(ℝ, smoothModel F d)
          (H.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)))
          (contMDiff_affinePointsTarget F hsmoothH hsmooth j)
          (fun W hW => eq_zero_of_forall_mvfderiv_eq_zero 𝓘(ℝ, smoothModel F d) 1 W hW) X Y }

/-- The algebra map between the complex enveloping algebras induced by the tangent map of a
morphism of group schemes at infinity. -/
def pointEnvelopingMap (j : H ⟶ G) :
    AdelicEnvelopingAlgebra F H hsmoothH →ₐ[ℂ] AdelicEnvelopingAlgebra F G hsmooth := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F H hsmoothH
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F H hsmoothH
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp
    (Langlands.Algebra.ComplexLieExtension.extendLieHom
      (pointTangentLieHom F hsmoothH hsmooth j)))

/-- On pure generators the enveloping map is the tangent map. -/
theorem pointEnvelopingMap_ι_tmul (j : H ⟶ G) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F H hsmoothH
    let := smoothChartedSpace F G hsmooth
    let := smoothLieGroup F H hsmoothH
    let := smoothLieGroup F G hsmooth
    let : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
    let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    ∀ (z : ℂ) (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H)),
      pointEnvelopingMap F hsmoothH hsmooth j (UniversalEnvelopingAlgebra.ι ℂ (z ⊗ₜ[ℝ] X)) =
        UniversalEnvelopingAlgebra.ι ℂ
          (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
          (z ⊗ₜ[ℝ] pointTangent F hsmoothH hsmooth j X) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F H hsmoothH
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F H hsmoothH
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  dsimp only
  intro z X
  unfold pointEnvelopingMap
  rw [UniversalEnvelopingAlgebra.lift_ι_apply, LieHom.comp_apply,
    Langlands.Algebra.ComplexLieExtension.extendLieHom_tmul]
  rfl

end Maps

section Shift

variable {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
  {e : ℕ} (hsmoothH : SmoothOfRelativeDimension e H.X.hom)

/-- The derivative at the identity of a complex function on `H(F_∞)`, as a real functional on
the identity tangent space. -/
def identityDerivative (χ : InfiniteAdelicGroupPoints F H → ℂ) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F H hsmoothH
    GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H) →ₗ[ℝ] ℂ := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F H hsmoothH
  exact (mvfderiv 𝓘(ℝ, smoothModel F e) χ 1).toLinearMap

/-- The enveloping automorphism `Y ↦ Y + dχ(Y)` of the derivative at the identity of a
function `χ` on `H(F_∞)`, for a proof that this derivative vanishes on brackets. -/
def envelopingCharacterShift (χ : InfiniteAdelicGroupPoints F H → ℂ)
    (hχ : letI := fun v : NumberField.InfinitePlace F =>
        InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F H hsmoothH
      letI := smoothLieGroup F H hsmoothH
      letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
        (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
      ∀ X Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F e) (InfiniteAdelicGroupPoints F H),
        identityDerivative F hsmoothH χ ⁅X, Y⁆ = 0) :
    AdelicEnvelopingAlgebra F H hsmoothH →ₐ[ℂ] AdelicEnvelopingAlgebra F H hsmoothH := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F H hsmoothH
  letI := smoothLieGroup F H hsmoothH
  letI : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F H) := LieGroup.of_le (n := ∞) (by simp)
  exact Langlands.Algebra.ComplexLieExtension.characterShift (identityDerivative F hsmoothH χ) hχ

end Shift

section Ideal

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The velocities at time `0` of the smooth curves through the identity of `G(F_∞)` that stay in
a given subset. -/
def curveTangents (S : Set (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    Set (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  exact {X | ∃ c : ℝ → InfiniteAdelicGroupPoints F G,
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ c ∧ c 0 = 1 ∧ (∀ t, c t ∈ S) ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 (1 : ℝ) = X}

/-- The complex span of the products `ι(X) · a` with `X` a curve tangent of a subset `S` and `a`
in the enveloping algebra: the right ideal generated by these directions. -/
def curveRightIdeal (S : Set (InfiniteAdelicGroupPoints F G)) :
    Submodule ℂ (AdelicEnvelopingAlgebra F G hsmooth) := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact Submodule.span ℂ {a | ∃ X ∈ curveTangents F hsmooth S,
    ∃ b : AdelicEnvelopingAlgebra F G hsmooth,
      a = UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) * b}

end Ideal

end Langlands.Global.InfiniteAdelicGroupPoints
