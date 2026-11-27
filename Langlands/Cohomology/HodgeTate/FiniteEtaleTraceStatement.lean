import Langlands.Cohomology.HodgeTate.ProperSmoothStatement
import Langlands.Shimura.Coefficients.Etale

/-! # Finite étale trace and proper smooth Hodge–Tate comparison -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.Geometry EtaleGaloisAction EtaleDerivedSections
open Langlands.GaloisRepresentation.HodgeTate
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.Shimura.Coefficients
open scoped TensorProduct BigOperators

universe wY wR

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.HodgeTate

variable {K : Type} [Field K] (p : ℕ) [Fact p.Prime]
variable [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

local notation "Base" => Spec (CommRingCat.of K)
local notation "C" => Completed p K

variable [geomDerived : ∀ X : Over (Spec (CommRingCat.of K)), HasDerivedCategory.{wY}
    (ModuleSheaf (baseChange K (AlgebraicClosure K) X.hom) ℤ_[p])]
variable [HasDerivedCategory.{wR} (ModuleCat ℤ_[p])]

private abbrev ProperSmoothScheme := {X : Over Base // Smooth X.hom ∧ IsProper X.hom}

private abbrev hodgeSummand (X : Over Base) (i j : ℕ) : ModuleCat K :=
  (relativeCohomology X.hom i).obj (differentialForms X.hom j)

private abbrev hodgeModule (X : Over Base) (q : ℕ) : Type :=
  (j : Fin (q + 1)) → C ⊗[K] hodgeSummand X (q - j.val) j.val

private abbrev etaleModule (X : Over Base) (q : ℕ) : Type :=
  C ⊗[ℚ_[p]] (ellAdicEtaleAction.{wY, wR} X.hom p q).V

private def hodgePullback {X Y : Over Base} (a : Y ⟶ X) (q : ℕ) :
    hodgeModule p X q →ₗ[C] hodgeModule p Y q :=
  LinearMap.pi fun j => (TensorProduct.AlgebraTensorModule.lTensor C C
    (hodgeCohomologyPullback a j.val (q - j.val)).hom).comp (LinearMap.proj j)

private def etalePullback {X Y : Over Base} (a : Y ⟶ X) (q : ℕ) :
    etaleModule.{wY, wR} p X q →ₗ[C] etaleModule.{wY, wR} p Y q :=
  TensorProduct.AlgebraTensorModule.lTensor C C (ellAdicEtalePullback.{wY, wR} p a q).hom

variable {Γ : Type} [Group Γ]
variable {X : ProperSmoothScheme (K := K)} (Y : Action X.val.left.Etale Γ)

private abbrev coverOver : Over Base := Over.mk (Y.V.hom ≫ X.val.hom)

private def properSmoothCover (h : IsFiniteGeometricTorsor X.val.left Y) :
    ProperSmoothScheme (K := K) := by
  letI : Etale Y.V.hom := Y.V.prop
  letI : IsFinite Y.V.hom := h.2.1
  letI : Smooth X.val.hom := X.property.1
  letI : IsProper X.val.hom := X.property.2
  refine ⟨coverOver Y, ?_, ?_⟩
  · change Smooth (Y.V.hom ≫ X.val.hom)
    infer_instance
  · change IsProper (Y.V.hom ≫ X.val.hom)
    infer_instance

private abbrev coverMap : coverOver Y ⟶ X.val := Over.homMk Y.V.hom rfl

private def deckMap (γ : Γ) : coverOver Y ⟶ coverOver Y :=
  Over.homMk (Y.ρ γ).asHom.left (by
    change (Y.ρ γ).asHom.left ≫ Y.V.hom ≫ X.val.hom = Y.V.hom ≫ X.val.hom
    rw [← Category.assoc, MorphismProperty.Over.w])

/-- Proper smooth Hodge–Tate comparison commutes with unnormalized trace
for finite étale Galois covers. Each trace is characterized by the sum
of deck pullbacks after pullback to the cover. -/
def ProperSmoothHodgeTateFiniteEtaleTraceStatement (q : ℕ) : Prop :=
  ∃ h : ProperSmoothHodgeTateNaturalStatement.{wY, wR} (K := K) p q,
    let Φ := Classical.choose h
    ∀ (X : ProperSmoothScheme (K := K)) (Γ : Type) [Group Γ] [Fintype Γ]
      (Y : Action X.val.left.Etale Γ) (hy : IsFiniteGeometricTorsor X.val.left Y),
      let W := properSmoothCover Y hy
      let b := coverMap Y
      let u := hodgePullback p b q
      let v := etalePullback.{wY, wR} p b q
      Function.Injective u ∧ Function.Injective v ∧
      ∃ (trH : hodgeModule p W.val q →ₗ[C] hodgeModule p X.val q)
        (trE : etaleModule.{wY, wR} p W.val q →ₗ[C] etaleModule.{wY, wR} p X.val q),
        u.comp trH = ∑ γ : Γ, hodgePullback p (deckMap Y γ) q ∧
        v.comp trE = ∑ γ : Γ, etalePullback.{wY, wR} p (deckMap Y γ) q ∧
        (Φ X).toLinearMap.comp trH = trE.comp (Φ W).toLinearMap

end Langlands.Cohomology.HodgeTate
