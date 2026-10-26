import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeTransport
import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineBaseChangeStatement
import Langlands.AlgebraicGeometry.RelativeDifferentialsSpecMapIsIso
import Langlands.AlgebraicGeometry.RelativeDifferentialsOpenImmersionProof
import Langlands.AlgebraicGeometry.Modules.TildePullback
import Mathlib.RingTheory.Kaehler.TensorProduct

/-! # Canonical differential base change for spectra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open TensorProduct

namespace Langlands.Scheme

private lemma tilde_homEquiv_apply {A : CommRingCat.{u}} (M : ModuleCat.{u} A)
    (N : (Spec A).Modules) (α : tilde M ⟶ N) (m : M) :
    (tilde.adjunction.homEquiv M N α) m =
      α.app ⊤ (tilde.toOpen M ⊤ m) := rfl

private lemma tilde_map_toOpen {A : CommRingCat.{u}} {M N : ModuleCat.{u} A}
    (α : M ⟶ N) (V : (Spec A).Opens) (m : M) :
    (tilde.map α).app V (tilde.toOpen M V m) = tilde.toOpen N V (α m) := by
  exact congrArg (fun k => k m) (tilde.toOpen_map_app α V)

section AlgebraPushout

variable (R S A B : CommRingCat.{u})
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

local notation "f" => Spec.map (CommRingCat.ofHom (algebraMap R A))
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap A B))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap S B))
local notation "M" => ModuleCat.of A (KaehlerDifferential R A)
local notation "E" => ModuleCat.of B (B ⊗[A] KaehlerDifferential R A)

/-- Identify the affine square map through a compatible tilde-pullback comparison. -/
lemma relativeDifferentialsSquareMap_isIso_of_tilde_comparison
    [Algebra.IsPushout R S A B]
    (hspec : RelativeDifferentialsSpecMapIsIsoStatement.{u})
    (σ : (pullback g).obj (tilde M) ≅ tilde E)
    (hσ : ∀ (V : (Spec A).Opens) (m : M),
      ((pullbackPushforwardAdjunction g).homEquiv _ _ σ.hom).app V
        (tilde.toOpen M V m) =
      tilde.toOpen E (g ⁻¹ᵁ V) (1 ⊗ₜ[A] m))
    (w : g ≫ f = q ≫ b) :
    IsIso (relativeDifferentialsSquareMap g b w) := by
  let e := (KaehlerDifferential.tensorKaehlerEquiv R S A B).toModuleIso
  let α := (pullback g).map (relativeDifferentialsSpecMap R A) ≫
    relativeDifferentialsSquareMap g b w
  let β := σ.hom ≫ tilde.map e.hom ≫ relativeDifferentialsSpecMap S B
  have heq : α = β := by
    apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
    apply (tilde.adjunction.homEquiv _ _).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
    intro a
    rw [tilde_homEquiv_apply, tilde_homEquiv_apply]
    dsimp only [α, β]
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Hom.comp_app, pushforward_map_app]
    change
      ((pullbackPushforwardAdjunction g).homEquiv _ _
        (relativeDifferentialsSquareMap g b w)).app ⊤
          ((relativeDifferentialsSpecMap R A).app ⊤
            (tilde.toOpen M ⊤ (KaehlerDifferential.D R A a))) =
      (relativeDifferentialsSpecMap S B).app (g ⁻¹ᵁ ⊤)
        ((tilde.map e.hom).app (g ⁻¹ᵁ ⊤)
          (((pullbackPushforwardAdjunction g).homEquiv _ _ σ.hom).app ⊤
            (tilde.toOpen M ⊤ (KaehlerDifferential.D R A a))))
    rw [relativeDifferentialsSpecMap_app_toOpen_D,
      relativeDifferentialsSquareMap_adjoint_app, hσ, tilde_map_toOpen]
    change _ = (relativeDifferentialsSpecMap S B).app (g ⁻¹ᵁ ⊤)
      (tilde.toOpen (ModuleCat.of B (KaehlerDifferential S B)) (g ⁻¹ᵁ ⊤)
        (KaehlerDifferential.tensorKaehlerEquiv R S A B
          (1 ⊗ₜ[A] KaehlerDifferential.D R A a)))
    rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul,
      relativeDifferentialsSpecMap_app_toOpen_D]
    congr 1
    simp only [TopologicalSpace.Opens.map_top]
    exact congrArg (fun h => h a)
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (algebraMap A B))).symm
  have : IsIso (relativeDifferentialsSpecMap R A) := hspec R A
  have : IsIso (relativeDifferentialsSpecMap S B) := hspec S B
  have : IsIso (tilde.map e.hom) := (tilde.functor B).map_isIso e.hom
  have : IsIso α := by rw [heq]; dsimp [β]; infer_instance
  exact IsIso.of_isIso_comp_left ((pullback g).map (relativeDifferentialsSpecMap R A)) _

end AlgebraPushout

section TensorSpectrum

variable (R A S : CommRingCat.{u}) [Algebra R A] [Algebra R S]

local notation "C" => CommRingCat.of (A ⊗[R] S)
local notation "Ω" => ModuleCat.of A (KaehlerDifferential R A)
local notation "ΩE" => ModuleCat.of C ((A ⊗[R] S) ⊗[A] KaehlerDifferential R A)
local notation "p₀" => Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] S)))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The tensor-spectrum comparison implies the exact categorical affine base-change map is iso. -/
lemma relativeDifferentialsBaseChangeMap_spec_isIso_of_tilde_comparison
    (hopen : RelativeDifferentialsOpenImmersionIsIsoStatement.{u})
    (hspec : RelativeDifferentialsSpecMapIsIsoStatement.{u})
    (σ : (pullback p₀).obj (tilde Ω) ≅ tilde ΩE)
    (hσ : ∀ (V : (Spec A).Opens) (m : Ω),
      ((pullbackPushforwardAdjunction p₀).homEquiv _ _ σ.hom).app V
        (tilde.toOpen Ω V m) =
      tilde.toOpen ΩE (p₀ ⁻¹ᵁ V) (1 ⊗ₜ[A] m)) :
    IsIso (relativeDifferentialsBaseChangeMap
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let q₀ := Spec.map (CommRingCat.ofHom (algebraMap S (A ⊗[R] S)))
  have w : p₀ ≫ f = q₀ ≫ b := by
    simp only [f, b, q₀, ← Spec.map_comp]
    congr 1
    ext r
    exact (IsScalarTower.algebraMap_apply R A (A ⊗[R] S) r).symm.trans
      (IsScalarTower.algebraMap_apply R S (A ⊗[R] S) r)
  have : Algebra.IsPushout R S A (A ⊗[R] S) :=
    (inferInstance : Algebra.IsPushout R A S (A ⊗[R] S)).symm
  have : IsIso (relativeDifferentialsSquareMap p₀ b w) :=
    relativeDifferentialsSquareMap_isIso_of_tilde_comparison R S A C hspec σ hσ w
  exact relativeDifferentialsBaseChangeMap_isIso_of_square hopen f b p₀ q₀ w
    (pullbackSpecIso R A S).inv (pullbackSpecIso_inv_fst' R A S)
    (pullbackSpecIso_inv_snd R A S)

end TensorSpectrum

/-- Discharge the tilde comparison with the canonical scalar-extension isomorphism. -/
lemma relativeDifferentialsBaseChangeMap_spec_isIso_of_comparisons
    (hopen : RelativeDifferentialsOpenImmersionIsIsoStatement.{u})
    (hspec : RelativeDifferentialsSpecMapIsIsoStatement.{u})
    (R A B : CommRingCat.{u}) (f : R ⟶ A) (b : R ⟶ B) :
    IsIso (relativeDifferentialsBaseChangeMap (Spec.map f) (Spec.map b)) := by
  let : Algebra R A := f.hom.toAlgebra
  let : Algebra R B := b.hom.toAlgebra
  exact relativeDifferentialsBaseChangeMap_spec_isIso_of_tilde_comparison R A B hopen hspec
    (Modules.tildePullbackAlgebraIso A (CommRingCat.of (A ⊗[R] B))
      (ModuleCat.of A (KaehlerDifferential R A)))
    (Modules.tildePullbackAlgebraIso_adjoint_toOpen A (CommRingCat.of (A ⊗[R] B))
      (ModuleCat.of A (KaehlerDifferential R A)))

/-- The actual canonical differential comparison for base change of spectra is invertible. -/
theorem relativeDifferentialsAffineBaseChangeIsIso :
    RelativeDifferentialsAffineBaseChangeIsIsoStatement.{u} :=
  relativeDifferentialsBaseChangeMap_spec_isIso_of_comparisons
    relativeDifferentialsOpenImmersionIsIso relativeDifferentialsSpecMapIsIso

end Langlands.Scheme
