import Langlands.AlgebraicGeometry.StandardEtaleLift
import Langlands.GroupScheme.Torus.MultiplicativeTypeFlatNilpotentReflectionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeQuasiIsotrivialProof
import Langlands.GroupScheme.Torus.NilpotentReductionAffine
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Flat nilpotent reflection of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open RelativeMultiplicativeType

/-- An étale morphism to an affine base has a standard étale affine chart at each point. -/
private theorem exists_standardEtale_chart {R : Type u} [CommRing R] {U : Scheme.{u}}
    (p : U ⟶ Spec (CommRingCat.of R)) [Etale p] (x : U) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C),
      Algebra.IsStandardEtale R C ∧
        ∃ (a : Spec (CommRingCat.of C) ⟶ U) (z : Spec (CommRingCat.of C)),
          a z = x ∧ a ≫ p = Spec.algebraMap R C := by
  let 𝒱 := U.affineOpenCover
  let i := 𝒱.idx x
  obtain ⟨y, hy⟩ := 𝒱.covers x
  let φ : CommRingCat.of R ⟶ 𝒱.X i := Spec.preimage (𝒱.f i ≫ p)
  have hφ : Spec.map φ = 𝒱.f i ≫ p := Spec.map_preimage _
  let : Algebra R (𝒱.X i) := φ.hom.toAlgebra
  have : Algebra.Etale R (𝒱.X i) := by
    have h : Etale (Spec.map φ) := by
      rw [hφ]
      infer_instance
    exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h)
  obtain ⟨f, hf, hC⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) y.asIdeal
  let C := Localization.Away f
  obtain ⟨z, hz⟩ := (PrimeSpectrum.localization_away_comap_range C f).ge hf
  refine ⟨C, inferInstance, inferInstance, hC, Spec.algebraMap (𝒱.X i) C ≫ 𝒱.f i, z, ?_, ?_⟩
  · rw [Scheme.Hom.comp_apply]
    exact (congrArg (𝒱.f i) hz).trans hy
  · rw [Category.assoc, ← hφ, Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq R (𝒱.X i) C).symm

/-- Split reflection can use any surjection with nilpotent kernel as the reduction map. -/
private theorem isDiagonalizable_of_nilpotent_surjection {B C : Type u} [CommRing B]
    [CommRing C] (q : B →+* C) (hq : Function.Surjective q)
    (hK : IsNilpotent (RingHom.ker q)) (G : GroupScheme (Spec (CommRingCat.of B)))
    [Flat G.X.hom]
    (hG : IsDiagonalizable ((baseChange (Spec.map (CommRingCat.ofHom q))).obj G)) :
    IsDiagonalizable G := by
  let e := q.quotientKerEquivOfSurjective hq
  let d := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hd : d ≫ Spec.map (CommRingCat.ofHom q) = Spec.algebraMap B (B ⧸ RingHom.ker q) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
      (RingHom.quotientKerEquivOfSurjective_symm_comp hq)
  exact NilpotentReduction.isDiagonalizable_of_baseChange (RingHom.ker q) hK G
    (IsDiagonalizable.of_iso (Descent.pullbackComparison _ d _ hd G).symm (hG.baseChange d))

/-- A flat group scheme with multiplicative-type nilpotent reduction is of
multiplicative type. -/
theorem multiplicativeTypeFlatNilpotentReflection :
    MultiplicativeTypeFlatNilpotentReflectionStatement.{u} := by
  intro A _ J hJ H hFlat hRed
  let r := Spec.algebraMap A (A ⧸ J)
  have hr : Surjective r :=
    Langlands.AlgebraicGeometry.Picard.InfinitesimalTensorNilpotence.spec_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using hJ)
  obtain ⟨𝒱, h𝒱⟩ := multiplicativeTypeQuasiIsotrivial.1 _ _ hRed
  suffices h : ∀ x : Spec (CommRingCat.of A),
      ∃ (U : Scheme.{u}) (p : U ⟶ Spec (CommRingCat.of A)),
        Etale p ∧ x ∈ Set.range p ∧ IsDiagonalizable ((baseChange p).obj H) by
    obtain ⟨𝒰, h𝒰⟩ := MultiplicativeTypeQuasiIsotrivial.exists_etale_cover_of_pointwise _ H h
    exact ⟨𝒰.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun i => by have := 𝒰.map_prop i; exact ⟨inferInstance, inferInstance⟩), h𝒰⟩
  intro x
  obtain ⟨x₀, hx₀⟩ := r.surjective x
  let i := 𝒱.idx x₀
  obtain ⟨y, hy⟩ := 𝒱.covers x₀
  have : Etale (𝒱.f i) := 𝒱.map_prop i
  obtain ⟨C, _, _, hC, a, z, hz, ha⟩ := exists_standardEtale_chart (𝒱.f i) y
  let : Algebra.IsStandardEtale (A ⧸ J) C := hC
  obtain ⟨B, _, _, hB, q, hqA, hq, hK⟩ :=
    Langlands.AlgebraicGeometry.StandardEtaleLift.exists_etale_nilpotent_lift A J hJ C
  let p := Spec.algebraMap A B
  let s := Spec.map (CommRingCat.ofHom q)
  let d := a ≫ 𝒱.f i
  have hp : Etale p := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hB)
  have hs : s ≫ p = d ≫ r := by
    change s ≫ p = (a ≫ 𝒱.f i) ≫ r
    rw [ha]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hqA]
    rfl
  refine ⟨Spec (CommRingCat.of B), p, hp, ⟨s z, ?_⟩, ?_⟩
  · calc
      p (s z) = r (𝒱.f i (a z)) := by
        simpa only [d, Scheme.Hom.comp_apply] using congrArg (fun m => m z) hs
      _ = x := by rw [hz, hy, hx₀]
  · let G := (baseChange p).obj H
    have : Flat G.X.hom := by
      change Flat (pullback.snd H.X.hom p)
      infer_instance
    have hd : IsDiagonalizable ((baseChange d).obj ((baseChange r).obj H)) :=
      IsDiagonalizable.of_iso (baseChangeCompIso (𝒱.f i) a _) ((h𝒱 i).baseChange a)
    have hG : IsDiagonalizable ((baseChange s).obj G) :=
      IsDiagonalizable.of_iso
        (Descent.pullbackComparison p s _ hs H ≪≫ baseChangeCompIso r d H) hd
    exact isDiagonalizable_of_nilpotent_surjection q hq hK G hG

end Langlands.GroupScheme
