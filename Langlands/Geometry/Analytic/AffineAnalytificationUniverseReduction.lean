import Langlands.Geometry.Analytic.AffineAnalytificationMonomorphismComparison
import Langlands.Geometry.Analytic.AnalyticImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Basic

/-! # Moving affine analytification problems to the field universe -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory SaturatedAtlasPresentation
open scoped TensorProduct

namespace UniverseReduction

section RingTheory

/-- Étale ring maps compose, for rings in arbitrary universes. -/
theorem etale_comp {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : f.Etale) (hg : g.Etale) : (g.comp f).Etale := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale R S := hf
  have : Algebra.Etale S T := hg
  exact Algebra.Etale.comp R S T

/-- Étaleness is invariant under conjugation by ring isomorphisms, across universes. -/
theorem etale_of_conj {R S : Type v} {R' S' : Type w} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] {φ : R →+* S} {φ' : R' →+* S'} (e₁ : R ≃+* R') (e₂ : S ≃+* S')
    (h : ∀ r, e₂ (φ r) = φ' (e₁ r)) (hφ : φ.Etale) : φ'.Etale := by
  have h₁ : (e₁.symm.toRingHom).Etale := RingHom.Etale.of_bijective e₁.symm.bijective
  have h₂ : (e₂.toRingHom).Etale := RingHom.Etale.of_bijective e₂.bijective
  have h₃ := etale_comp (etale_comp h₁ hφ) h₂
  have he : e₂.toRingHom.comp (φ.comp e₁.symm.toRingHom) = φ' := by
    ext r'
    simp [h]
  rwa [he] at h₃

/-- Ring epimorphisms are invariant under conjugation by ring isomorphisms, across
universes. -/
theorem epi_of_conj {R S : Type v} {R' S' : Type w} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] {φ : R →+* S} {φ' : R' →+* S'} (e₁ : R ≃+* R') (e₂ : S ≃+* S')
    (h : ∀ r, e₂ (φ r) = φ' (e₁ r)) [Epi (CommRingCat.ofHom φ)] :
    Epi (CommRingCat.ofHom φ') := by
  let : Algebra R S := φ.toAlgebra
  have hE : Algebra.IsEpi R S :=
    CommRingCat.epi_iff_epi.mp (inferInstanceAs (Epi (CommRingCat.ofHom φ)))
  refine ⟨fun {T} g k hgk => ?_⟩
  have hgk' (r' : R') : g (φ' r') = k (φ' r') :=
    congrArg (fun m : CommRingCat.of R' ⟶ T => m r') hgk
  let α : S →+* T := g.hom.comp (e₂.toRingHom)
  let β : S →+* T := k.hom.comp (e₂.toRingHom)
  let : Algebra R T := (α.comp φ).toAlgebra
  let α' : S →ₐ[R] T := { α with commutes' := fun _ => rfl }
  let β' : S →ₐ[R] T :=
    { β with
      commutes' := fun r => by
        change k (e₂ (φ r)) = g (e₂ (φ r))
        rw [h]
        exact (hgk' (e₁ r)).symm }
  let Θ := Algebra.TensorProduct.lift α' β' fun _ _ => Commute.all _ _
  ext s'
  have hs := (Algebra.isEpi_iff_forall_one_tmul_eq (R := R) (A := S)).mp hE (e₂.symm s')
  have hΘ := congrArg Θ hs
  simp only [Θ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one] at hΘ
  change k (e₂ (e₂.symm s')) = g (e₂ (e₂.symm s')) at hΘ
  simpa using hΘ.symm

/-- The spectrum of a ring map is an open immersion exactly when the map is an
étale epimorphism. -/
theorem isOpenImmersion_specMap_iff {R S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) :
    _root_.AlgebraicGeometry.IsOpenImmersion
        (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ↔
      φ.Etale ∧ Epi (CommRingCat.ofHom φ) := by
  constructor
  · intro hφ
    have hEt : _root_.AlgebraicGeometry.Etale
        (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) := inferInstance
    refine ⟨(_root_.AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @_root_.AlgebraicGeometry.Etale) (φ := CommRingCat.ofHom φ)).mp hEt, ?_⟩
    exact epi_of_mono_specMap _
  · rintro ⟨hEt, hEpi⟩
    have : Mono (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) :=
      mono_specMap_of_epi _
    have : _root_.AlgebraicGeometry.Etale
        (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) :=
      _root_.AlgebraicGeometry.HasRingHomProperty.Spec_iff.mpr hEt
    exact _root_.AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono _

/-- Open immersions of affine spectra are invariant under conjugation by ring
isomorphisms, across universes. -/
theorem isOpenImmersion_of_conj {R S : Type v} {R' S' : Type w} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] {φ : R →+* S} {φ' : R' →+* S'} (e₁ : R ≃+* R') (e₂ : S ≃+* S')
    (h : ∀ r, e₂ (φ r) = φ' (e₁ r))
    (hφ : _root_.AlgebraicGeometry.IsOpenImmersion
      (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ))) :
    _root_.AlgebraicGeometry.IsOpenImmersion
      (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ')) := by
  obtain ⟨hEt, hEpi⟩ := (isOpenImmersion_specMap_iff φ).mp hφ
  exact (isOpenImmersion_specMap_iff φ').mpr ⟨etale_of_conj e₁ e₂ h hEt, epi_of_conj e₁ e₂ h⟩

end RingTheory

section Models

variable {K : Type u} [CommRing K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- The quotient of the presenting polynomial ring by the kernel of the presentation,
a model of `A` in the universe of the coefficient ring. -/
abbrev Model : Type u := MvPolynomial (Fin P.arity) K ⧸ RingHom.ker P.map

/-- The model is isomorphic to the presented algebra. -/
def modelEquiv : Model P ≃ₐ[K] A := Ideal.quotientKerAlgEquivOfSurjective P.surjective

/-- The quotient presentation of the model. -/
def modelPresentation : FinitePolynomialPresentation K (Model P) :=
  ⟨P.arity, Ideal.Quotient.mkₐ K _, Ideal.Quotient.mkₐ_surjective K _⟩

variable {B : Type v} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- The map of models corresponding to `f`. -/
def modelMap : Model P →ₐ[K] Model Q :=
  (modelEquiv Q).symm.toAlgHom.comp (f.comp (modelEquiv P).toAlgHom)

theorem modelEquiv_modelMap (x : Model P) :
    modelEquiv Q (modelMap P Q f x) = f (modelEquiv P x) := by
  simp [modelMap]

theorem modelMap_conj :
    (modelEquiv Q).toAlgHom.comp ((modelMap P Q f).comp (modelEquiv P).symm.toAlgHom) = f := by
  ext a
  simp [modelMap]

theorem surjective_iff_model :
    Function.Surjective f ↔ Function.Surjective (modelMap P Q f) := by
  constructor
  · intro hf b
    obtain ⟨a, ha⟩ := hf (modelEquiv Q b)
    refine ⟨(modelEquiv P).symm a, (modelEquiv Q).injective ?_⟩
    rw [modelEquiv_modelMap, AlgEquiv.apply_symm_apply, ha]
  · intro hf b
    obtain ⟨a, ha⟩ := hf ((modelEquiv Q).symm b)
    refine ⟨modelEquiv P a, ?_⟩
    rw [← modelEquiv_modelMap, ha, AlgEquiv.apply_symm_apply]

theorem isOpenImmersion_iff_model :
    _root_.AlgebraicGeometry.IsOpenImmersion
        (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
      _root_.AlgebraicGeometry.IsOpenImmersion
        (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (modelMap P Q f).toRingHom)) := by
  constructor
  · exact isOpenImmersion_of_conj (modelEquiv P).symm.toRingEquiv (modelEquiv Q).symm.toRingEquiv
      fun a => (modelEquiv Q).injective (by
        change modelEquiv Q ((modelEquiv Q).symm (f a)) =
          modelEquiv Q (modelMap P Q f ((modelEquiv P).symm a))
        rw [modelEquiv_modelMap]
        simp)
  · exact isOpenImmersion_of_conj (modelEquiv P).toRingEquiv (modelEquiv Q).toRingEquiv
      fun x => modelEquiv_modelMap P Q f x

end Models

section Analytic

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Localized functoriality carries algebra isomorphisms to analytic isomorphisms,
for algebras in arbitrary universes. -/
theorem isIso_localizedHom_of_algEquiv {A : Type v} {B : Type w} [CommRing A] [Algebra K A]
    [CommRing B] [Algebra K B] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (e : A ≃ₐ[K] B) :
    IsIso (localizedHom K P Q e.toAlgHom) := by
  have hidA := (affineAnalytificationLocalizedFunctoriality K A A A P P P P (AlgHom.id K A)
    (AlgHom.id K A)).2.2.1
  have hidB := (affineAnalytificationLocalizedFunctoriality K B B B Q Q Q Q (AlgHom.id K B)
    (AlgHom.id K B)).2.2.1
  have hcompA := (affineAnalytificationLocalizedFunctoriality K A B A P P Q P e.toAlgHom
    e.symm.toAlgHom).2.2.2.1
  have hcompB := (affineAnalytificationLocalizedFunctoriality K B A B Q Q P Q e.symm.toAlgHom
    e.toAlgHom).2.2.2.1
  refine ⟨⟨localizedHom K Q P e.symm.toAlgHom, ?_, ?_⟩⟩
  · rw [← hcompB]
    simpa using hidB
  · rw [← hcompA]
    simpa using hidA

variable {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  {B : Type v} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (f : A →ₐ[K] B)

/-- The analytified map is conjugate to the analytified map of models. -/
theorem localizedHom_eq_conj :
    localizedHom K P Q f =
      localizedHom K (modelPresentation Q) Q (modelEquiv Q).toAlgHom ≫
        localizedHom K (modelPresentation P) (modelPresentation Q) (modelMap P Q f) ≫
          localizedHom K P (modelPresentation P) (modelEquiv P).symm.toAlgHom := by
  conv_lhs => rw [← modelMap_conj P Q f]
  rw [(affineAnalytificationLocalizedFunctoriality K A (Model Q) B P P (modelPresentation Q) Q
      ((modelMap P Q f).comp (modelEquiv P).symm.toAlgHom) (modelEquiv Q).toAlgHom).2.2.2.1,
    (affineAnalytificationLocalizedFunctoriality K A (Model P) (Model Q) P P
      (modelPresentation P) (modelPresentation Q)
      (modelEquiv P).symm.toAlgHom (modelMap P Q f)).2.2.2.1]

theorem closedImmersion_iff_model :
    closedImmersion (localizedHom K P Q f) ↔
      closedImmersion (localizedHom K (modelPresentation P) (modelPresentation Q)
        (modelMap P Q f)) := by
  have := isIso_localizedHom_of_algEquiv (modelPresentation Q) Q (modelEquiv Q)
  have := isIso_localizedHom_of_algEquiv P (modelPresentation P) (modelEquiv P).symm
  rw [localizedHom_eq_conj, MorphismProperty.cancel_left_of_respectsIso closedImmersion,
    MorphismProperty.cancel_right_of_respectsIso closedImmersion]

theorem openImmersion_iff_model :
    openImmersion (localizedHom K P Q f) ↔
      openImmersion (localizedHom K (modelPresentation P) (modelPresentation Q)
        (modelMap P Q f)) := by
  have := isIso_localizedHom_of_algEquiv (modelPresentation Q) Q (modelEquiv Q)
  have := isIso_localizedHom_of_algEquiv P (modelPresentation P) (modelEquiv P).symm
  rw [localizedHom_eq_conj, MorphismProperty.cancel_left_of_respectsIso openImmersion,
    MorphismProperty.cancel_right_of_respectsIso openImmersion]

end Analytic

end UniverseReduction

end Langlands.Analytic.AffineAnalytification
