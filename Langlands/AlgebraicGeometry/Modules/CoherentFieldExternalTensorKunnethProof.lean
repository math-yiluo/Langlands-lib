import Langlands.AlgebraicGeometry.Modules.CoherentFieldExternalTensorKunnethStatement
import Langlands.AlgebraicGeometry.Modules.CechResolution.CechCohomologyIso
import Langlands.AlgebraicGeometry.Modules.BiCech.Kunneth
import Langlands.AlgebraicGeometry.Picard.LineBundleQuasicoherent
import Langlands.Cohomology.ModuleComplex.FieldKunneth

/-! # Coherent Künneth over a field for external tensor products of line bundles: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace Langlands.AlgebraicGeometry.Modules

open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules.CechResolution
  Langlands.Cohomology.ModuleComplex.FieldKunneth

/-- Componentwise isomorphisms induce an isomorphism of the direct sums of tensor products
indexed by `{ab : ℕ × ℕ // ab.1 + ab.2 = n}`. -/
def directSumTensorIso {K : Type u} [Field K] {A A' B B' : ℕ → ModuleCat.{u} K}
    (eA : ∀ a, A a ≅ A' a) (eB : ∀ b, B b ≅ B' b) (n : ℕ) :
    ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
        TensorProduct K (A ab.1.1) (B ab.1.2)) ≅
      ModuleCat.of K (DirectSum {ab : ℕ × ℕ // ab.1 + ab.2 = n} fun ab =>
        TensorProduct K (A' ab.1.1) (B' ab.1.2)) :=
  LinearEquiv.toModuleIso (DFinsupp.mapRange.linearEquiv fun ab =>
    TensorProduct.congr (eA ab.1.1).toLinearEquiv (eB ab.1.2).toLinearEquiv)

/-- Coherent Künneth over a field for external tensor products of line bundles, in every
degree: `Hⁿ(X ×_K Y, p₁^* L ⊗ p₂^* M) ≅ ⨁_{a + b = n} Hᵃ(X, L) ⊗_K Hᵇ(Y, M)`. -/
theorem coherentFieldExternalTensorKunneth :
    CoherentFieldExternalTensorKunnethStatement.{u} := by
  intro K _ X Y _ _ _ _ L M n P
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  obtain ⟨𝒰, 𝒱, ⟨e⟩⟩ := BiCech.exists_nonempty_relativeCohomology_overProd_iso X Y L M n
  have eX : ∀ a, (DerivedSections.relativeCohomology X.hom a).obj L.obj ≅
      (cechCochainComplex X.hom 𝒰 L.obj).homology a := fun a =>
    (nonempty_relativeCohomology_iso_cechCochainComplex_homology X.hom 𝒰 L.obj a).some
  have eY : ∀ b, (DerivedSections.relativeCohomology Y.hom b).obj M.obj ≅
      (cechCochainComplex Y.hom 𝒱 M.obj).homology b := fun b =>
    (nonempty_relativeCohomology_iso_cechCochainComplex_homology Y.hom 𝒱 M.obj b).some
  exact ⟨e ≪≫ kunnethIso (K := K) _ _ n ≪≫
    directSumTensorIso (fun a => (eX a).symm) (fun b => (eY b).symm) n⟩

end Langlands.AlgebraicGeometry.Modules
