import Langlands.AlgebraicGeometry.Picard.DeterminantBasisLocus
import Langlands.RingTheory.Grassmannian.ProjectiveEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Ampleness of an actual determinant classified by a Grassmannian -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant

open Module.Grassmannian.ProjectiveEmbedding

variable {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E] {k : ℕ}
  (D : Rep R E k) {X : Scheme.{u}} (f : X ⟶ D.Gr) (N : X.Modules)
  (q : E → Γ(N, ⊤))

/-- The classified quotient on every affine open is the actual section module,
with the prescribed global generators. -/
def HasAffinePointComparison : Prop :=
  ∀ (W : X.Opens) (hW : IsAffineOpen W),
    letI := algOfHom D (hW.fromSpec ≫ f)
    ∃ c : ((Γ(X, W) ⊗[R] E) ⧸ (ptOf D (hW.fromSpec ≫ f)).toSubmodule) ≃ₗ[Γ(X, W)]
        Γ(N, W),
      ∀ m : E,
        c ((ptOf D (hW.fromSpec ≫ f)).toSubmodule.mkQ ((1 : Γ(X, W)) ⊗ₜ[R] m)) =
          N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q m)

/-- Grassmannian chart membership is exactly the actual section basis test. -/
theorem basis_test_iff_preimage
    (hc : HasAffinePointComparison D f N q) (x : Fin k → E)
    (W : X.Opens) (hW : IsAffineOpen W) :
    (Function.Bijective (fun v : Fin k → Γ(X, W) ↦
      ∑ j, v j • N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q (x j)))) ↔
        W ≤ f ⁻¹ᵁ D.V x := by
  let := algOfHom D (hW.fromSpec ≫ f)
  obtain ⟨c, hc⟩ := hc W hW
  have hfamily :
      c ∘ (fun v : Fin k → Γ(X, W) ↦
        ∑ j, v j • (ptOf D (hW.fromSpec ≫ f)).toSubmodule.mkQ
          ((1 : Γ(X, W)) ⊗ₜ[R] x j)) =
      (fun v : Fin k → Γ(X, W) ↦
        ∑ j, v j • N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q (x j))) := by
    funext v
    simp only [Function.comp_apply, map_sum, map_smul, hc]
  rw [← hfamily, Function.Bijective.of_comp_iff' c.bijective]
  rw [← D.hVchart x Γ(X, W) (ptOf D (hW.fromSpec ≫ f)), pt_ptOf]
  change Set.range (f.base ∘ hW.fromSpec.base) ⊆ (D.V x : Set D.Gr) ↔
    (W : Set X) ⊆ f.base ⁻¹' (D.V x : Set D.Gr)
  rw [Set.range_comp, hW.range_fromSpec, Set.image_subset_iff]

/-- An affine Grassmannian classification makes the determinant of the actual
finite locally free module ample on a compact scheme. -/
theorem finiteLocallyFreeDeterminant_isAmple
    [CompactSpace X] [IsAffineHom f]
    (hN : Langlands.Scheme.Modules.HasFiniteLocalBasis N)
    {ι : Type u} {T : ι → X.Opens}
    (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
      (ULift.{u} (Fin k)) ≅ N.over (T i))
    (hT : (⨆ i, T i) = ⊤)
    (hc : HasAffinePointComparison D f N q) :
    (finiteLocallyFreeDeterminant hN).IsAmple := by
  apply finiteLocallyFreeDeterminant_isAmple_of_affine_basis_tests hN e hT
    (fun x ↦ f ⁻¹ᵁ D.V x) (f.iSup_preimage_eq_top D.hV)
    (fun x ↦ (D.hVaff x).preimage f) (fun x j ↦ q (x j))
  intro x W hW i hi
  exact basis_test_iff_preimage D f N q hc x W hW

end Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant
