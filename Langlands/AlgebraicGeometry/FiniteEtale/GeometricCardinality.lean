import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.Dimension.Constructions

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- The rational-point count of a finite étale algebra over a separably closed field. -/
theorem natCard_algHom_eq_finrank (K A : Type u) [Field K] [IsSepClosed K]
    [CommRing A] [Algebra K A] [Module.Finite K A] [Algebra.FormallyEtale K A] :
    Nat.card (A →ₐ[K] K) = Module.finrank K A := by
  classical
  have : IsArtinianRing A := isArtinian_of_tower K inferInstance
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  calc
    Nat.card (A →ₐ[K] K) = Nat.card (PrimeSpectrum A) :=
      Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K A)
    _ = Module.finrank K (PrimeSpectrum A → K) := by
      rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]
    _ = Module.finrank K A :=
      (Algebra.FormallyEtale.equivPiOfIsSepClosed K A).toLinearEquiv.finrank_eq.symm

/-- The scalar structure on global functions induced by the actual structure morphism. -/
abbrev coordinateAlgebra {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) : Algebra K Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra

/-- Sections of an affine scheme over a field are the corresponding algebra homomorphisms. -/
noncomputable def sectionsAlgHomEquiv {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [IsAffine X] :
    letI := coordinateAlgebra f
    {x : Spec (.of K) ⟶ X // x ≫ f = 𝟙 _} ≃ (Γ(X, ⊤) →ₐ[K] K) := by
  letI := coordinateAlgebra f
  let e := Scheme.ΓSpecIso (.of K)
  have hinv : X.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(X, ⊤)).hom = 𝟙 _ := by
    simpa only [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom,
      Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] using
      congrArg Scheme.Hom.appTop X.isoSpec.hom_inv_id
  have hback (φ : Γ(X, ⊤) ⟶ CommRingCat.of K) :
      (Spec.map φ ≫ X.isoSpec.inv).appTop ≫ e.hom = φ := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
      ← Category.assoc, hinv, Category.id_comp]
  let ev : {x : Spec (.of K) ⟶ X // x ≫ f = 𝟙 _} → (Γ(X, ⊤) →ₐ[K] K) := fun x =>
    { toRingHom := (x.1.appTop ≫ e.hom).hom
      commutes' := fun r => by
        have hx : f.appTop ≫ x.1.appTop = 𝟙 _ := by
          rw [← Scheme.Hom.comp_appTop, x.2, Scheme.Hom.id_appTop]
        have h : e.inv ≫ f.appTop ≫ x.1.appTop ≫ e.hom = 𝟙 _ := by
          rw [reassoc_of% hx, Iso.inv_hom_id]
        exact congrArg (fun g : CommRingCat.of K ⟶ CommRingCat.of K => g.hom r) h }
  refine Equiv.ofBijective ev ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    apply ext_of_isAffine
    apply (cancel_mono e.hom).1
    ext a
    exact DFunLike.congr_fun hxy a
  · intro φ
    let φ' : Γ(X, ⊤) ⟶ CommRingCat.of K := CommRingCat.ofHom φ.toRingHom
    have hsection : (Spec.map φ' ≫ X.isoSpec.inv) ≫ f = 𝟙 _ := by
      apply ext_of_isAffine
      apply (cancel_mono e.hom).1
      rw [Scheme.Hom.comp_appTop, Category.assoc, hback,
        Scheme.Hom.id_appTop, Category.id_comp]
      apply (cancel_epi e.inv).1
      rw [Iso.inv_hom_id]
      ext r
      exact φ.commutes r
    refine ⟨⟨Spec.map φ' ≫ X.isoSpec.inv, hsection⟩, ?_⟩
    apply AlgHom.ext
    intro a
    exact congrArg (fun g : Γ(X, ⊤) ⟶ CommRingCat.of K => g.hom a) (hback φ')

/-- The number of actual sections of a finite étale scheme over a separably closed field
is the dimension of its actual coordinate algebra. -/
theorem natCard_sections_eq_finrank {X : Scheme.{u}} {K : Type u} [Field K]
    [IsSepClosed K] (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f] :
    letI := coordinateAlgebra f
    Nat.card {x : Spec (.of K) ⟶ X // x ≫ f = 𝟙 _} = Module.finrank K Γ(X, ⊤) := by
  let := coordinateAlgebra f
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Module.Finite K Γ(X, ⊤) := by
    exact RingHom.Finite.comp f.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : Algebra.Etale K Γ(X, ⊤) := by
    exact RingHom.Etale.stableUnderComposition
      (Scheme.ΓSpecIso (.of K)).inv.hom f.appTop.hom
      (RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv))
      (HasRingHomProperty.appTop (P := @Etale) f inferInstance)
  exact (Nat.card_congr (sectionsAlgHomEquiv f)).trans (natCard_algHom_eq_finrank K Γ(X, ⊤))

end Langlands.AlgebraicGeometry.FiniteEtale
