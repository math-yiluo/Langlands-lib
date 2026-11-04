import Langlands.Geometry.Building.IwahoriWeylQuotientLemmas

/-! # Chamber complement lemmas for the Iwahori–Weyl quotient -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IwahoriWeylAlgebra

variable {A : Type u} {B : Type v} {X : Type w} [Group A] [Group B] [MulAction A X]

/-- A subgroup free modulo the quotient kernel and transitive on the ambient orbit
has complementary image to the image of the full stabilizer. -/
theorem image_isComplement_stabilizer
    (f : A →* B) (hf : Function.Surjective f) (H : Subgroup A) (x : X)
    (hker : f.ker ≤ MulAction.stabilizer A x)
    (hfree : ∀ h : H, (h : A) • x = x → f h = 1)
    (htrans : ∀ a : A, ∃ h : H, (h : A) • a • x = x) :
    (H.map f).IsComplement' ((MulAction.stabilizer A x).map f) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.2
    intro b hbH hbK
    obtain ⟨h, hh, rfl⟩ := hbH
    obtain ⟨k, hk, hkh⟩ := hbK
    have hdiff : k⁻¹ * h ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkh, inv_mul_cancel]
    have hfix : h • x = x := by
      have h := MulAction.mem_stabilizer_iff.1 (hker hdiff)
      rw [mul_smul, inv_smul_eq_iff] at h
      exact h.trans (MulAction.mem_stabilizer_iff.1 hk)
    exact hfree ⟨h, hh⟩ hfix
  · apply Set.eq_univ_iff_forall.2
    intro b
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨h, hh⟩ := htrans a
    refine ⟨f (h : A)⁻¹, ⟨(h : A)⁻¹, H.inv_mem h.property, rfl⟩,
      f ((h : A) * a), ⟨(h : A) * a, ?_, rfl⟩, ?_⟩
    · exact MulAction.mem_stabilizer_iff.2 (by rwa [mul_smul])
    · change f (h : A)⁻¹ * f ((h : A) * a) = f a
      rw [← map_mul, inv_mul_cancel_left]

end IwahoriWeylAlgebra

namespace AffineRootSystem

variable {V : Type v} {A : Type w} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} {e : A ≃ᵃ[ℝ] A}

/-- A root-preserving affine automorphism maps each facet onto the facet of
the image point. -/
theorem image_facet (he : e ∈ rootStabilizer Ψ) (x : A) :
    e '' facet Ψ x = facet Ψ (e x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (facetRel_apply_iff he x z).2 hz
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (facetRel_apply_iff he x (e.symm y)).1
    simpa only [e.apply_symm_apply] using (show facetRel Ψ (e x) y from hy)

/-- A root-preserving affine automorphism maps a chamber onto a chamber. -/
theorem IsChamber.image {C : Set A} (hC : IsChamber Ψ C)
    (he : e ∈ rootStabilizer Ψ) : IsChamber Ψ (e '' C) := by
  obtain ⟨x, hx, rfl⟩ := hC
  refine ⟨e x, fun ψ hψ => ?_, (image_facet he x).symm⟩
  exact hx _ ((comp_mem_iff he ψ).2 hψ)

end AffineRootSystem

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

theorem normalizerAffineEquiv_image (n : normalizerPoints P.i) (C : Set P.Apartment) :
    P.apartment.normalizerAffineEquiv n '' C = n • C :=
  rfl

theorem normalizer_smul_isChamber
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (n : normalizerPoints P.i) :
    AffineRootSystem.IsChamber P.affineRoots (n • C) := by
  rw [← P.normalizerAffineEquiv_image]
  apply hC.image
  exact (hP.range_le_extendedAffineWeylGroup ⟨n, rfl⟩).1

/-- An action-compatible affine-part comparison transfers chamber freeness
and orbit transitivity to the actual quotient complement. -/
theorem affinePart_isComplement_chamberStabilizer_of_action
    [P.normalizerZero.Normal]
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (he : ∀ n : P.normalizerZeroComponent,
      (e (P.affinePartMk n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) =
        P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i))
    (C : Set P.Apartment)
    (hfree : ∀ w : AffineRootSystem.affineWeylGroup P.affineRoots,
      (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C = C → w = 1)
    (htrans : ∀ n : normalizerPoints P.i,
      ∃ w : AffineRootSystem.affineWeylGroup P.affineRoots,
        (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' (n • C) = C) :
    P.affinePart.IsComplement' (P.chamberStabilizer C) := by
  apply IwahoriWeylAlgebra.image_isComplement_stabilizer
    (QuotientGroup.mk' P.normalizerZero) (QuotientGroup.mk'_surjective _)
    P.normalizerZeroComponent C
  · intro n hn
    have hn0 : n ∈ P.normalizerZero := QuotientGroup.eq_one_iff n |>.1 hn
    let n0 : P.normalizerZeroComponent :=
      ⟨n, P.normalizerZero_le_normalizerZeroComponent hn0⟩
    have hn1 : P.affinePartMk n0 = 1 := (P.affinePartMk_eq_one_iff n0).2 hn0
    have hact : P.apartment.normalizerAffineEquiv n = 1 := by
      rw [← he n0, hn1, map_one]
      rfl
    apply MulAction.mem_stabilizer_iff.2
    rw [← P.normalizerAffineEquiv_image, hact]
    exact Set.image_id _
  · intro n hn
    have hw : e (P.affinePartMk n) = 1 := hfree _ (by
      rw [he n, P.normalizerAffineEquiv_image]
      exact hn)
    have hn1 : P.affinePartMk n = 1 := e.injective (by simpa using hw)
    exact congrArg Subtype.val hn1
  · intro n
    obtain ⟨w, hw⟩ := htrans n
    obtain ⟨q, rfl⟩ := e.surjective w
    obtain ⟨m, rfl⟩ := P.affinePartMk_surjective q
    refine ⟨m, ?_⟩
    rw [he m, P.normalizerAffineEquiv_image] at hw
    exact hw

/-- For fixed actual data, the exact sequence and the unique affine-Weyl
transport of chambers imply the full chamber splitting. -/
theorem iwahoriWeylChamberSplitting_of_unique_chamber_transport
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hex : P.IwahoriWeylExactSequence)
    (htransport : ∀ C D : Set P.Apartment,
      AffineRootSystem.IsChamber P.affineRoots C →
      AffineRootSystem.IsChamber P.affineRoots D →
        ∃! w : AffineRootSystem.affineWeylGroup P.affineRoots,
          (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C = D)
    (C : Set P.Apartment) (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    P.IwahoriWeylChamberSplitting C := by
  obtain ⟨hN, hG, ⟨e, he⟩, _, hsurj⟩ := hex
  let := hN
  let := hG
  have hcomp : P.affinePart.IsComplement' (P.chamberStabilizer C) := by
    apply P.affinePart_isComplement_chamberStabilizer_of_action e he C
    · intro w hw
      obtain ⟨w0, _, huniq⟩ := htransport C C hC hC
      exact (huniq w hw).trans (huniq 1 (Set.image_id _)).symm
    · intro n
      obtain ⟨w, hw, _⟩ :=
        htransport (n • C) C (P.normalizer_smul_isChamber hP hC n) hC
      exact ⟨w, hw⟩
  exact ⟨hN, hG, P.affinePart_normal, hcomp,
    P.chamberStabilizer_toComponents_bijective hsurj C hcomp⟩

end ParahoricBuildingData

/-- The geometric and algebraic reduction used by the chamber-splitting
proof, retaining the original data and normalizer action. -/
def IwahoriWeylChamberReductionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      P.IwahoriWeylExactSequence →
        (∀ C D : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
          AffineRootSystem.IsChamber P.affineRoots D →
            ∃! w : AffineRootSystem.affineWeylGroup P.affineRoots,
              (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C = D) →
          ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
            P.IwahoriWeylChamberSplitting C

theorem iwahoriWeylChamberReduction : IwahoriWeylChamberReductionStatement.{u} := by
  intro F _ _ _ _ G _ P hP hex htransport C hC
  exact P.iwahoriWeylChamberSplitting_of_unique_chamber_transport hP hex htransport C hC

end Langlands.Geometry.Building
