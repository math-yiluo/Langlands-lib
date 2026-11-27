import Langlands.Automorphic.GroupSchemeParabolicTangentStatement
import Langlands.Global.InfiniteAdelicTangentComplexification
import Langlands.GroupScheme.Lie.FieldAlgebraLie

/-! # The complexified archimedean tangent Lie algebra as a scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
open scoped Langlands.GroupScheme.Lie.FieldLie

section Realization

variable (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : ℕ}
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The tangent Lie algebra of `G` over `F`, as a Lie algebra over the rationals. -/
abbrev RationalTangentLie := RestrictScalars ℚ F (Additive (lieKernel G F))

/-- The realization of rational tangent vectors as tangent vectors at the identity of the
infinite adelic points, as an additive map. -/
def tangentAddHom :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    RationalTangentLie F G →+
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) :=
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  AddMonoidHom.mk' (fun x => tangentVector F G hsmooth (RestrictScalars.addEquiv ℚ F _ x))
    fun _ _ => tangentVector_add F G hsmooth _ _

/-- The complexified realization as an additive map. -/
def complexTangentAddHom :
    ℂ ⊗[ℚ] RationalTangentLie F G →+ AdelicComplexLieAlgebra F G hsmooth :=
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun z : ℂ =>
        ((TensorProduct.mk ℝ ℂ
          (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) z).toAddMonoidHom.comp
          (tangentAddHom F G hsmooth)))
      fun z w => by
        ext x
        simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
          TensorProduct.mk_apply, TensorProduct.add_tmul])
    fun q z x => by
      have h1 : RestrictScalars.addEquiv ℚ F _ (q • x) =
          (q : F) • RestrictScalars.addEquiv ℚ F (Additive (lieKernel G F)) x := by
        rw [RestrictScalars.addEquiv_map_smul, eq_ratCast]
      have h2 : (q • z : ℂ) = (q : ℝ) • z := by
        rw [Rat.smul_def, Complex.real_smul, Complex.ofReal_ratCast]
      change (q • z) ⊗ₜ[ℝ] tangentAddHom F G hsmooth x =
        z ⊗ₜ[ℝ] tangentAddHom F G hsmooth (q • x)
      rw [h2, TensorProduct.smul_tmul]
      congr 1
      change (q : ℝ) • tangentVector F G hsmooth (RestrictScalars.addEquiv ℚ F _ x) =
        tangentVector F G hsmooth (RestrictScalars.addEquiv ℚ F _ (q • x))
      rw [h1, tangentVector_ratCast_smul]

theorem complexTangentAddHom_tmul (z : ℂ) (x : RationalTangentLie F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    complexTangentAddHom F G hsmooth (z ⊗ₜ x) =
      (z ⊗ₜ[ℝ] (show GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) from
        tangentVector F G hsmooth (RestrictScalars.addEquiv ℚ F _ x)) :
        AdelicComplexLieAlgebra F G hsmooth) :=
  rfl

/-- The complexified realization `ℂ ⊗_ℚ Lie(G) → ℂ ⊗_ℝ Lie(G(F_∞))`, `z ⊗ x ↦ z ⊗ τ(x)`. -/
def complexTangentMap :
    ℂ ⊗[ℚ] RationalTangentLie F G →ₗ[ℂ] AdelicComplexLieAlgebra F G hsmooth where
  toFun := complexTangentAddHom F G hsmooth
  map_add' := map_add _
  map_smul' c t := by
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F G hsmooth
    induction t with
    | tmul z x =>
      rw [TensorProduct.smul_tmul', complexTangentAddHom_tmul, complexTangentAddHom_tmul,
        RingHom.id_apply, TensorProduct.smul_tmul', smul_eq_mul]
    | add a b ha hb =>
      rw [smul_add, map_add, map_add, ha, hb, smul_add]

theorem complexTangentMap_tmul (z : ℂ) (x : RationalTangentLie F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    complexTangentMap F G hsmooth (z ⊗ₜ x) =
      (z ⊗ₜ[ℝ] (show GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) from
        tangentVector F G hsmooth (RestrictScalars.addEquiv ℚ F _ x)) :
        AdelicComplexLieAlgebra F G hsmooth) :=
  rfl

set_option maxHeartbeats 1000000 in
theorem complexTangentMap_lie (a b : ℂ ⊗[ℚ] RationalTangentLie F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    complexTangentMap F G hsmooth ⁅a, b⁆ =
      ⁅complexTangentMap F G hsmooth a, complexTangentMap F G hsmooth b⁆ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  induction a with
  | add a₁ a₂ h₁ h₂ =>
    have e : ⁅a₁ + a₂, b⁆ = ⁅a₁, b⁆ + ⁅a₂, b⁆ := add_lie a₁ a₂ b
    rw [e, map_add, h₁, h₂, map_add]
    exact (add_lie (complexTangentMap F G hsmooth a₁) (complexTangentMap F G hsmooth a₂)
      (complexTangentMap F G hsmooth b)).symm
  | tmul z x =>
    induction b with
    | add b₁ b₂ h₁ h₂ =>
      have e : ⁅z ⊗ₜ[ℚ] x, b₁ + b₂⁆ = ⁅z ⊗ₜ[ℚ] x, b₁⁆ + ⁅z ⊗ₜ[ℚ] x, b₂⁆ :=
        lie_add (z ⊗ₜ[ℚ] x : ℂ ⊗[ℚ] RationalTangentLie F G) b₁ b₂
      rw [e, map_add, h₁, h₂, map_add]
      exact (lie_add (complexTangentMap F G hsmooth (z ⊗ₜ x)) (complexTangentMap F G hsmooth b₁)
        (complexTangentMap F G hsmooth b₂)).symm
    | tmul w y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, complexTangentMap_tmul, complexTangentMap_tmul,
        complexTangentMap_tmul]
      exact congrArg (fun Y => (z * w) ⊗ₜ[ℝ] Y) (tangentVector_lie F G hsmooth
        (RestrictScalars.addEquiv ℚ F _ x) (RestrictScalars.addEquiv ℚ F _ y))

/-- The complexified realization is surjective: the realizations of rational tangent vectors span
the real tangent space. -/
theorem complexTangentMap_surjective :
    Function.Surjective (complexTangentMap F G hsmooth) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  rw [← LinearMap.range_eq_top]
  set R := LinearMap.range (complexTangentMap F G hsmooth)
  have hz : ∀ (z : ℂ) (Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)),
      (z ⊗ₜ[ℝ] Y : AdelicComplexLieAlgebra F G hsmooth) ∈ R := by
    intro z Y
    have hspan : Submodule.span ℝ (Set.range fun x : Additive (lieKernel G F) =>
        (show GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) from
          tangentVector F G hsmooth x)) = ⊤ :=
      span_range_tangentVector F G hsmooth
    have hle : Submodule.span ℝ (Set.range fun x : Additive (lieKernel G F) =>
        (show GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) from
          tangentVector F G hsmooth x)) ≤
        (R.restrictScalars ℝ).comap (TensorProduct.mk ℝ ℂ
          (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) z) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact ⟨z ⊗ₜ (RestrictScalars.addEquiv ℚ F _).symm x, rfl⟩
    have hY := hle (hspan ▸ Submodule.mem_top : Y ∈ _)
    exact hY
  rw [eq_top_iff]
  rintro t -
  induction t using TensorProduct.inductionOn with
  | tmul z Y => exact hz z Y
  | add a b ha hb => exact R.add_mem ha hb

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem finite_rationalTangentLie [LocallyOfFiniteType G.X.hom] :
    Module.Finite ℚ (RationalTangentLie F G) := by
  let := RestrictScalars.moduleOrig ℚ F (Additive (lieKernel G F))
  have : Module.Finite F (RationalTangentLie F G) :=
    inferInstanceAs (Module.Finite F (Additive (lieKernel G F)))
  exact Module.Finite.trans F _

omit [IsAffine G.X.left] in
include hsmooth in
theorem finrank_rationalTangentLie :
    Module.finrank ℚ (RationalTangentLie F G) = Module.finrank ℚ F * d := by
  let := RestrictScalars.moduleOrig ℚ F (Additive (lieKernel G F))
  rw [← Module.finrank_mul_finrank ℚ F (RationalTangentLie F G)]
  congr 1
  exact finrank_lieKernel_of_smooth F G hsmooth F

theorem finrank_complexTangent :
    Module.finrank ℂ (ℂ ⊗[ℚ] RationalTangentLie F G) =
      Module.finrank ℂ (AdelicComplexLieAlgebra F G hsmooth) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have h : Module.finrank ℂ (AdelicComplexLieAlgebra F G hsmooth) =
      Module.finrank ℝ (smoothModel F d) := Module.finrank_baseChange
  rw [h, finrank_smoothModel, Module.finrank_baseChange, finrank_rationalTangentLie F G hsmooth,
    mul_comm]

/-- The complexified realization is injective. -/
theorem complexTangentMap_injective :
    Function.Injective (complexTangentMap F G hsmooth) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have := finite_rationalTangentLie F G
  have : FiniteDimensional ℝ
      (GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :=
    inferInstanceAs (FiniteDimensional ℝ (smoothModel F d))
  have : FiniteDimensional ℂ (AdelicComplexLieAlgebra F G hsmooth) := inferInstance
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_complexTangent F G hsmooth)).mpr (complexTangentMap_surjective F G hsmooth)

/-- **The complexified archimedean tangent Lie algebra is a scalar extension of the rational
Lie algebra.** The map `z ⊗ x ↦ z ⊗ τ(x)` is an isomorphism of complex Lie algebras
`ℂ ⊗_ℚ Lie(G) ≅ ℂ ⊗_ℝ Lie(G(F ⊗ ℝ))`. -/
def complexTangentEquiv :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    ℂ ⊗[ℚ] RationalTangentLie F G ≃ₗ⁅ℂ⁆ AdelicComplexLieAlgebra F G hsmooth :=
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  { LinearEquiv.ofBijective (complexTangentMap F G hsmooth)
      ⟨complexTangentMap_injective F G hsmooth, complexTangentMap_surjective F G hsmooth⟩ with
    map_lie' := fun {a b} => complexTangentMap_lie F G hsmooth a b }

theorem complexTangentEquiv_apply (t : ℂ ⊗[ℚ] RationalTangentLie F G) :
    complexTangentEquiv F G hsmooth t = complexTangentMap F G hsmooth t :=
  rfl

end Realization

section Naturality

variable (F : Type u) [Field F] [NumberField F] {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] {d e : ℕ}

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] in
/-- The tangent map of a homomorphism of groups over `F`, over the rationals. -/
def rationalTargetMap (f : H ⟶ G) : RationalTangentLie F H →ₗ[ℚ] RationalTangentLie F G where
  toFun x := (RestrictScalars.addEquiv ℚ F _).symm
    (Lie.targetMapLinear f F (RestrictScalars.addEquiv ℚ F _ x))
  map_add' _ _ := (Lie.targetMapLinear f F).map_add _ _
  map_smul' q _ := (Lie.targetMapLinear f F).map_smul (algebraMap ℚ F q) _

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom] in
theorem rationalTargetMap_apply (f : H ⟶ G) (x : RationalTangentLie F H) :
    RestrictScalars.addEquiv ℚ F _ (rationalTargetMap F f x) =
      Lie.targetMapLinear f F (RestrictScalars.addEquiv ℚ F _ x) :=
  rfl

/-- **Naturality of the complexified realization.** The complexified derivative of the map of
infinite adelic points induced by a homomorphism corresponds to the scalar extension of its
algebraic tangent map. -/
theorem complexPointDifferential_complexTangentMap (hH : SmoothOfRelativeDimension e H.X.hom)
    (hG : SmoothOfRelativeDimension d G.X.hom) (f : H ⟶ G)
    (t : ℂ ⊗[ℚ] RationalTangentLie F H) :
    complexPointDifferential F hH hG f (complexTangentMap F H hH t) =
      complexTangentMap F G hG ((rationalTargetMap F f).baseChange ℂ t) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothChartedSpace F H hH
  induction t using TensorProduct.inductionOn with
  | tmul z x =>
    rw [LinearMap.baseChange_tmul, complexTangentMap_tmul, complexTangentMap_tmul]
    exact congrArg (fun Y : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) =>
      (z ⊗ₜ[ℝ] Y : AdelicComplexLieAlgebra F G hG))
      (tangentVector_naturality F hH hG f (RestrictScalars.addEquiv ℚ F _ x))
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

end Naturality

end Langlands.Automorphic.GroupSchemeFunctions
