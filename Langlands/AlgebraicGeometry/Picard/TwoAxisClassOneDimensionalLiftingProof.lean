import Langlands.AlgebraicGeometry.Picard.TwoAxisClassProductBaseChange
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassSquareGluing
import Langlands.AlgebraicGeometry.Picard.GenericThickeningPullback
import Langlands.AlgebraicGeometry.Picard.TwoAxisClassNilpotentInjectiveProof

/-! # Murre's condition (F7) for the two-axis class presheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AbelianScheme

namespace TwoAxisRigidifiedLineBundle

open UnramifiedFunctor

variable {S : Scheme.{u}} (A : Langlands.AbelianScheme S)

section Functoriality

/-- Class restriction along an identity is the identity. -/
lemma classesPullback_id (T : Over S) (x : Classes A T) :
    classesPullback A (𝟙 T) x = x :=
  (classPresheaf A).map_id_apply (op T) x

/-- Class restriction along an isomorphism of test objects is injective. -/
lemma classesPullback_injective_of_isIso {T U : Over S} (h : T ⟶ U) [IsIso h] :
    Function.Injective (classesPullback A h) :=
  ((isIso_iff_bijective ((classPresheaf A).map h.op)).mp inferInstance).1

variable {Λ : Type u} [CommRing Λ] (f : Spec (CommRingCat.of Λ) ⟶ S)

/-- `algHomOver` turns composition of algebra maps into composition of test morphisms. -/
lemma algHomOver_comp {B C D : Type u} [CommRing B] [Algebra Λ B] [CommRing C] [Algebra Λ C]
    [CommRing D] [Algebra Λ D] (φ : B →ₐ[Λ] C) (ψ : C →ₐ[Λ] D) :
    algHomOver f (ψ.comp φ) = algHomOver f ψ ≫ algHomOver f φ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((ψ.comp φ : B →ₐ[Λ] D) : B →+* D)) =
    Spec.map (CommRingCat.ofHom (ψ : C →+* D)) ≫ Spec.map (CommRingCat.ofHom (φ : B →+* C))
  rw [← Spec.map_comp]
  rfl

/-- `algHomOver` sends the identity algebra map to the identity. -/
lemma algHomOver_id (B : Type u) [CommRing B] [Algebra Λ B] :
    algHomOver f (AlgHom.id Λ B) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id B)) = 𝟙 _
  rw [CommRingCat.ofHom_id, Spec.map_id]

instance algHomOver_isIso {B C : Type u} [CommRing B] [Algebra Λ B] [CommRing C] [Algebra Λ C]
    (e : B ≃ₐ[Λ] C) : IsIso (algHomOver f (e : B →ₐ[Λ] C)) :=
  ⟨⟨algHomOver f (e.symm : C →ₐ[Λ] B), by
    rw [← algHomOver_comp, AlgEquiv.comp_symm, algHomOver_id], by
    rw [← algHomOver_comp, AlgEquiv.symm_comp, algHomOver_id]⟩⟩

end Functoriality

section Transfer

variable {Λ : Type u} [CommRing Λ] (f : Spec (CommRingCat.of Λ) ⟶ S)

/-- Restriction of classes along a surjective map `π : D → E` of `Λ`-algebras, with `D` local
and `E` nontrivial, is injective. This transfers the local injectivity
`classesPullback_injective_local` along `D ⧸ ker π ≃ E`. -/
theorem classesPullback_algHomOver_injective {D E : Type u} [CommRing D] [Algebra Λ D]
    [IsLocalRing D] [CommRing E] [Algebra Λ E] [Nontrivial E] (π : D →ₐ[Λ] E)
    (hπ : Function.Surjective π) :
    Function.Injective (classesPullback A (algHomOver f π)) := by
  have hKtop : RingHom.ker π ≠ ⊤ := by
    intro h
    have h1 : (1 : D) ∈ RingHom.ker π := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  let w : algebraOver f (D ⧸ RingHom.ker π) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ RingHom.ker π))) ≫
        (algebraOver f D).hom) :=
    Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ RingHom.ker π))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap Λ D)) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap Λ (D ⧸ RingHom.ker π))) ≫ f
      rw [Category.id_comp, ← Category.assoc, ← Spec.map_comp]
      rfl)
  have hfac : algHomOver f π =
      algHomOver f (Ideal.quotientKerAlgEquivOfSurjective hπ :
        D ⧸ RingHom.ker π →ₐ[Λ] E) ≫ w.hom ≫
        compTestHom (T := algebraOver f D)
          (Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ RingHom.ker π)))) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (π : D →+* E)) =
      Spec.map (CommRingCat.ofHom ((Ideal.quotientKerAlgEquivOfSurjective hπ :
        D ⧸ RingHom.ker π →ₐ[Λ] E) : D ⧸ RingHom.ker π →+* E)) ≫ 𝟙 _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap D (D ⧸ RingHom.ker π)))
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
  have h₀ := classesPullback_injective_local A D (RingHom.ker π) hKtop (algebraOver f D).hom
  rw [hfac]
  intro x y hxy
  rw [classesPullback_comp, classesPullback_comp, classesPullback_comp,
    classesPullback_comp] at hxy
  exact h₀ (classesPullback_injective_of_isIso A w.hom
    (classesPullback_injective_of_isIso A _ hxy))

end Transfer

section GenericLifting

open GenericThickening

/-- The gluing argument behind (F7). Let `Λ` be a local ring, `I` a proper ideal with
`I² = 0`, and `Λ → Λ'` an algebra injective on `I`. If a class `ξ'` over `Λ/I` and a class
`η` over `Λ'` agree over `Λ'/IΛ'`, then `ξ'` lifts to a class over `Λ`. -/
theorem exists_lift_of_generic {Λ : Type u} [CommRing Λ] [IsLocalRing Λ] (Λ' : Type u)
    [CommRing Λ'] [Algebra Λ Λ'] {I : Ideal Λ} (hItop : I ≠ ⊤) (hII : I * I = ⊥)
    (hinj : ∀ x ∈ I, algebraMap Λ Λ' x = 0 → x = 0) (f : Spec (CommRingCat.of Λ) ⟶ S)
    (ξ' : Classes A (algebraOver f (Λ ⧸ I))) (η : Classes A (algebraOver f Λ'))
    (hη : classesPullback A (algHomOver f (Ideal.Quotient.mkₐ Λ (I.map (algebraMap Λ Λ')))) η =
      classesPullback A (algHomOver f (quotMap Λ' I)) ξ') :
    ∃ ξ : Classes A (Over.mk f), classesPullback A (algebraOverBase f (Λ ⧸ I)) ξ = ξ' := by
  obtain ⟨z₁, hz₁⟩ := classes_squareGluing A f (fibreSnd Λ' I) (fibreFst Λ' I) (quotMap Λ' I)
    (Ideal.Quotient.mkₐ Λ (I.map (algebraMap Λ Λ'))) (fibre_isPullback Λ' I)
    (Ideal.Quotient.mkₐ_surjective Λ _) (isNilpotent_ker_mkₐ_map Λ' hII) ξ' η hη
  have := isLocalRing_quotient_thick Λ' hItop hII
  have : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hagree : classesPullback A (algHomOver f (thickMk Λ' I)) z₁ =
      classesPullback A (algHomOver f (secMap Λ' I)) ξ' := by
    apply classesPullback_algHomOver_injective A f (retraction Λ' I) (retraction_surjective Λ' I)
    rw [← classesPullback_comp, ← classesPullback_comp, ← algHomOver_comp, ← algHomOver_comp,
      retraction_comp_mkₐ, retraction_comp_secMap, algHomOver_id, classesPullback_id]
    exact hz₁
  obtain ⟨z, hz⟩ := classes_squareGluing A f (Ideal.Quotient.mkₐ Λ I)
    (Algebra.ofId Λ (fibre Λ' I)) (secMap Λ' I) (thickMk Λ' I) (thick_isPullback Λ' hII hinj)
    (Ideal.Quotient.mkₐ_surjective Λ _) (isNilpotent_ker_mkₐ_thick Λ' hII) ξ' z₁ hagree
  let u : Over.mk f ⟶ algebraOver f Λ := Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ Λ)) ≫ f = f
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp,
      Category.id_comp])
  refine ⟨classesPullback A u z, ?_⟩
  have hu : algebraOverBase f (Λ ⧸ I) ≫ u = algHomOver f (Ideal.Quotient.mkₐ Λ I) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (algebraMap Λ (Λ ⧸ I))) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ Λ I : Λ →+* Λ ⧸ I))
    rw [Category.comp_id]
    rfl
  rw [← classesPullback_comp, hu]
  exact hz

open GenericThickening in
/-- Murre's condition (F7) for the two-axis class presheaf of an abelian scheme. -/
theorem classPresheaf_oneDimensionalLifting : OneDimensionalLifting (classPresheaf A) := by
  intro Λ _ _ _ _ _ hAss t ht I hI hNI f ξ' hlift
  obtain ⟨η, hη⟩ := hlift
  have hItop : I ≠ ⊤ := by
    rintro rfl
    obtain ⟨n, hn⟩ := hI
    rw [Ideal.top_pow, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  exact exists_lift_of_generic A (Localization.AtPrime t.asIdeal) hItop (mul_self_eq_bot hI hNI)
    (fun x _ hx ↦ algebraMap_atPrime_injective hAss t ht (hx.trans (map_zero _).symm))
    f ξ' η hη

end GenericLifting

end TwoAxisRigidifiedLineBundle

/-- Murre's condition (F7) holds for the two-axis class presheaf of every abelian scheme over
the spectrum of a noetherian ring. -/
theorem noetherianTwoAxisClassOneDimensionalLifting :
    NoetherianTwoAxisClassOneDimensionalLiftingStatement.{u} :=
  fun _ _ _ A ↦ TwoAxisRigidifiedLineBundle.classPresheaf_oneDimensionalLifting A

end Langlands.AlgebraicGeometry.Picard
