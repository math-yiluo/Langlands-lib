import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentCohomologyVanishingStatement
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof

/-!
# Proof that higher cohomology of quasi-coherent modules on affine schemes vanishes

On an affine scheme `X`, global sections of a short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` of
`𝒪_X`-modules with Čech-acyclic `G` are exact on the right, by the Library's
`AffineVanishing.surjective_app_of_exactAt` applied to the affine open `⊤`. Dimension shifting
along the chosen injective embeddings, which preserve Čech-acyclicity by
`AffineVanishing.isCechAcyclic_X₃`, gives the vanishing of `Hⁿ⁺¹(X, G)`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

namespace AffineVanishing

open PushforwardInjectiveAcyclic

variable {X : Scheme.{u}}

/-- On an affine scheme, for a short exact sequence `0 ⟶ G ⟶ I ⟶ Q ⟶ 0` of `𝒪_X`-modules
with `G` Čech-acyclic, global sections `Γ(X, I) ⟶ Γ(X, Q)` form an epimorphism. -/
lemma epi_globalSections_map_of_isCechAcyclic [IsAffine X] {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hG : IsCechAcyclic S.X₁) :
    Epi ((DerivedSections.globalSections X).map S.g) := by
  have hS' : (S.map (toAbSheaf X)).ShortExact := hS.map_of_exact _
  rw [ModuleCat.epi_iff_surjective]
  exact surjective_app_of_exactAt hS' (isAffineOpen_top X)
    (fun κ _ g' hg' => hG _ (isAffineOpen_top X) κ g' hg' 0)

/-- Higher cohomology of Čech-acyclic modules on an affine scheme vanishes. -/
theorem isZero_cohomology_of_isCechAcyclic [IsAffine X] (n : ℕ) (G : X.Modules)
    (hG : IsCechAcyclic G) :
    IsZero ((DerivedSections.cohomology X (n + 1)).obj G) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, ⊤))
  let F := DerivedSections.globalSections X
  change IsZero ((F.rightDerived (n + 1)).obj G)
  induction n generalizing G with
  | zero =>
    have hS := injectiveSc_shortExact G
    have := Langlands.Cohomology.DerivedPlus.epi_rightDerivedδ_of_isZero F hS 0 1 rfl
      (F.isZero_rightDerived_obj_injective_succ 0 (Injective.under G))
    refine IsZero.of_epi_eq_zero (Langlands.Cohomology.DerivedPlus.rightDerivedδ F hS 0 1 rfl) ?_
    have h0 : Epi ((F.rightDerived 0).map (injectiveSc G).g) := by
      have e : (F.rightDerived 0).map (injectiveSc G).g =
          (F.rightDerivedZeroIsoSelf.hom.app _ ≫ F.map (injectiveSc G).g) ≫
            F.rightDerivedZeroIsoSelf.inv.app _ := by
        rw [← F.rightDerivedZeroIsoSelf.hom.naturality, Category.assoc,
          Iso.hom_inv_id_app, Category.comp_id]
      have := epi_globalSections_map_of_isCechAcyclic hS hG
      rw [e]
      infer_instance
    rw [← cancel_epi ((F.rightDerived 0).map (injectiveSc G).g),
      Langlands.Cohomology.DerivedPlus.rightDerived_map_comp_δ, comp_zero]
  | succ n ih =>
    have hS := injectiveSc_shortExact G
    have := Langlands.Cohomology.DerivedPlus.epi_rightDerivedδ_of_isZero F hS (n + 1) (n + 2) rfl
      (F.isZero_rightDerived_obj_injective_succ (n + 1) (Injective.under G))
    exact IsZero.of_epi (Langlands.Cohomology.DerivedPlus.rightDerivedδ F hS (n + 1) (n + 2) rfl)
      (ih (cokernel (Injective.ι G)) (isCechAcyclic_X₃ hS hG))

end AffineVanishing

open AffineVanishing in
/-- Higher cohomology of quasi-coherent modules on an affine scheme vanishes, both absolutely
and over every affine base `Spec R`. -/
theorem affineQuasicoherentCohomologyVanishing :
    AffineQuasicoherentCohomologyVanishingStatement.{u} := by
  intro X _ M _ n
  have h0 := isZero_cohomology_of_isCechAcyclic n M (isCechAcyclic_of_isQuasicoherent M)
  refine ⟨h0, fun R g => ?_⟩
  exact ((ModuleCat.restrictScalars (DerivedSections.structureRingHom g).hom).map_isZero h0).of_iso
    ((DerivedSections.relativeCohomologyRestrictScalarsIso g (n + 1)).app _).symm

end Langlands.AlgebraicGeometry.Modules
