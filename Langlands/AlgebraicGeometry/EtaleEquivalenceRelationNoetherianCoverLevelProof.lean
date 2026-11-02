import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianCoverLevelStatement
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianCoaction
import Langlands.AlgebraicGeometry.RingEtaleGroupoidFiniteCover
import Langlands.AlgebraicGeometry.RingEtaleGroupoidQuotientLevel
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationKernelPair
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationNoetherianPushout
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # A Noetherian level carrying the finite surjective cover

Proof of the statement NL (`EtaleEquivalenceRelationNoetherianCoverLevelStatement`), the middle
step of the proof of Stacks Project Lemma 70.15.1 (Tag 07VS) for presentations.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry

open EtaleEquivalenceRelation

/-- NL for a cover whose relation ring has a finite-type Čech presentation. -/
theorem noetherianCoverLevel_of_presentation (E E₀ E' : EtaleEquivalenceRelation.{u})
    (f : E.U ⟶ E₀.U) (g : E.R ⟶ E₀.R) (h : IsCartesianHom E E₀ f g) [IsAffine E.U]
    [IsAffine E₀.U] [IsAffine E₀.R] [IsNoetherianRing Γ(E₀.U, ⊤)]
    (f' : E'.U ⟶ E.U) (g' : E'.R ⟶ E.R) (h' : IsCartesianHom E' E f' g') [IsFinite f']
    [Surjective f'] {A₁ B₁ : Type u} [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁]
    [Algebra.FiniteType ℤ A₁] [Algebra.Etale A₁ B₁] [Module.FaithfullyFlat A₁ B₁]
    (φ : B₁ →+* Γ(E'.U, ⊤))
    (hF : letI : Algebra A₁ Γ(E'.U, ⊤) := (φ.comp (algebraMap A₁ B₁)).toAlgebra
      ∃ F : B₁ ⊗[A₁] Γ(E'.U, ⊤) →+* Γ(E'.R, ⊤),
        (∀ b d, F (b ⊗ₜ d) = E'.t.appTop (φ b) * E'.s.appTop d) ∧ Function.Bijective F) :
    ∃ (E₁ : EtaleEquivalenceRelation.{u}) (f₁ : E.U ⟶ E₁.U) (g₁ : E.R ⟶ E₁.R),
      IsCartesianHom E E₁ f₁ g₁ ∧ IsAffine E₁.U ∧ IsNoetherian E₁.U ∧
        E₁.HasFiniteSurjectiveCoverWithAffineQuotient := by
  have : IsAffine E.R := h.isAffine_R
  have : IsAffine E'.U := isAffine_of_isAffineHom f'
  have hc := h'.comp h
  have : IsAffine E'.R := hc.isAffine_R
  let _ : Algebra Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) := E₀.s.appTop.hom.toAlgebra
  let _ : Algebra Γ(E₀.U, ⊤) Γ(E.U, ⊤) := f.appTop.hom.toAlgebra
  let _ : Algebra Γ(E₀.U, ⊤) Γ(E'.U, ⊤) := (f' ≫ f).appTop.hom.toAlgebra
  let _ : Algebra A₁ Γ(E'.U, ⊤) := (φ.comp (algebraMap A₁ B₁)).toAlgebra
  have hE₀ := E₀.ringEtaleGroupoid
  have : Algebra.Etale Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) := RingHom.etale_algebraMap.mp hE₀.etale_algebraMap
  have : Algebra.FiniteType Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) := inferInstance
  have : Algebra.FiniteType ℤ B₁ :=
    Algebra.FiniteType.trans (S := A₁) inferInstance inferInstance
  let θ := h.coaction
  have hθ : θ.IsMultiplicative := h.coaction_isMultiplicative
  let θ' := hc.coaction
  have hθ' : θ'.IsMultiplicative := hc.coaction_isMultiplicative
  let ψ := appTopAlgHom f' f
  have hψ : ∀ b, θ'.coaction (ψ b) =
      Algebra.TensorProduct.map (AlgHom.id Γ(E₀.U, ⊤) Γ(E₀.R, ⊤)) ψ (θ.coaction b) :=
    fun b => h'.ringHom_comp_appTop h b
  have hfin : (ψ : Γ(E.U, ⊤) →+* Γ(E'.U, ⊤)).Finite :=
    IsFinite.finite_app f' ⊤ (isAffineOpen_top E.U)
  have hsurj : Function.Surjective (PrimeSpectrum.comap (ψ : Γ(E.U, ⊤) →+* Γ(E'.U, ⊤))) := by
    have : Surjective (Spec.map f'.appTop) :=
      (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f')).mp
        inferInstance
    exact (surjective_iff _).mp this
  have hker := RingEtaleGroupoid.ker_le_nilradical_of_comap_surjective _ hsurj
  obtain ⟨F, hF, hFbij⟩ := hF
  have hinv : ∀ x, hc.relationIso.inv (hc.relationIso.hom x) = x := fun x => by
    change (hc.relationIso.hom ≫ hc.relationIso.inv).hom x = x
    rw [Iso.hom_inv_id]
    rfl
  let L : B₁ ⊗[A₁] Γ(E'.U, ⊤) →+* Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E'.U, ⊤) :=
    hc.relationIso.inv.hom.comp F
  have hL : ∀ b d, L (b ⊗ₜ d) = θ'.coaction (φ b) * ((1 : Γ(E₀.R, ⊤)) ⊗ₜ d) := by
    intro b d
    change hc.relationIso.inv (F (b ⊗ₜ d)) = hc.ringHom (φ b) * ((1 : Γ(E₀.R, ⊤)) ⊗ₜ d)
    rw [hF, map_mul, ← hc.relationIso_hom_one_tmul d, hinv]
    rfl
  have hLbij : Function.Bijective L :=
    (ConcreteCategory.bijective_of_isIso hc.relationIso.inv).comp hFbij
  obtain ⟨s, hs⟩ := hE₀.exists_bijective_level θ' hθ' φ L hL hLbij
  obtain ⟨D, D', hD, hD', φD, hDfg, hsD', hφD, hφfin, hφsurj⟩ :=
    hE₀.exists_finite_level θ hθ θ' hθ' ψ hψ hfin hker s
  obtain ⟨φ', hφ', F', hF', hF'bij⟩ := hs D' hD' hsD'
  let θD := hE₀.subalgebraCoaction θ D hD
  have hθD : θD.IsMultiplicative := hE₀.subalgebraCoaction_isMultiplicative θ hθ D hD
  let θD' := hE₀.subalgebraCoaction θ' D' hD'
  have hθD' : θD'.IsMultiplicative := hE₀.subalgebraCoaction_isMultiplicative θ' hθ' D' hD'
  let _ : Algebra D' (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] D') := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra D (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] D) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  have GD := hE₀.level θD hθD
  have GD' := hE₀.level θD' hθD'
  have : IsNoetherianRing D :=
    Algebra.FiniteType.isNoetherianRing Γ(E₀.U, ⊤) D
      (h := (Subalgebra.fg_iff_finiteType D).mp hDfg)
  have hcart := h.isCartesianHom_toScheme.comp
    (RingEtaleGroupoid.isCartesianHom_of_equivariant GD h.ringEtaleGroupoid D.val
      (hE₀.subalgebraCoaction_val θ D hD))
  refine ⟨GD.toScheme, _, _, hcart, inferInstanceAs (IsAffine (Spec _)),
    inferInstanceAs (IsNoetherian (Spec (CommRingCat.of D))), ?_⟩
  refine ⟨GD'.toScheme, _, _,
    RingEtaleGroupoid.isCartesianHom_of_equivariant GD GD' φD
      (hE₀.subalgebraCoaction_map θ θ' ψ hψ hD hD' φD hφD), ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).mpr hφfin
  · exact (surjective_iff _).mpr hφsurj
  · let _ : Algebra A₁ D' := (φ'.comp (algebraMap A₁ B₁)).toAlgebra
    exact hasAffineQuotient_of_bijective (θD'.toRingHom hθD') GD'.toScheme (Iso.refl _)
      (Iso.refl _) (by simp) (by simp)
      { toRingHom := φ', commutes' := fun _ => rfl } F' hF' hF'bij

/-- Proof of the statement NL: over a Noetherian first level, a finite surjective cartesian
cover with an affine quotient descends to a Noetherian level. -/
theorem etaleEquivalenceRelationNoetherianCoverLevel :
    EtaleEquivalenceRelationNoetherianCoverLevelStatement.{u} := by
  intro E E₀ f g h _ _ _ _ hcov
  obtain ⟨E', f', g', h', _, _, hq⟩ := hcov
  have : IsNoetherianRing Γ(E₀.U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top E₀.U⟩
  have : IsAffine E.R := h.isAffine_R
  have : IsAffine E'.U := isAffine_of_isAffineHom f'
  have : IsAffine E'.R := h'.isAffine_R
  obtain ⟨A₁, B₁, _, _, _, _, -, _, _, φ, hF⟩ := exists_fg_pushout_of_hasAffineQuotient E' hq
  exact noetherianCoverLevel_of_presentation E E₀ E' f g h f' g' h' φ hF

end Langlands.AlgebraicGeometry
