import Langlands.Cohomology.PrimeMinimalPerfectProof
import Langlands.Cohomology.PrimeFreeHomotopyDescentProof
import Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpread.Core

/-!
# Finite free models along ring maps

For a ring map `α : R →+* A`, a finite free model of a complex `K` over `R` is a finite free
complex over `A` homotopy equivalent to the scalar extension of `K`, with prescribed term ranks.
Models pass to further scalar extensions, exist near every prime with term ranks the
residue-field homology dimensions, and transport homology and induced maps.
-/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.Cohomology.ModuleComplex.FibreH0Spread

variable {R : Type u} [CommRing R]

/-- Ordinary extension of scalars preserves finite free complexes. -/
lemma isFiniteFree_baseChange {A B : Type u} [CommRing A] [CommRing B] (β : A →+* B)
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (hP : IsFiniteFree P) :
    IsFiniteFree ((baseChange β).obj P) := by
  refine ⟨bounded_baseChange β hP.1, fun i ↦ ?_⟩
  have := (hP.2 i).1
  have := (hP.2 i).2
  exact ⟨finite_extendScalars β (P.X i), free_extendScalars β (P.X i)⟩

/-- A finite free model of `K` along `α` with term ranks `n`: a finite free complex over `A`
homotopy equivalent to the scalar extension of `K` along `α` whose term in degree `i` is free of
rank `n i`. -/
def HasModel {A : Type u} [CommRing A] (α : R →+* A) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n : ℤ → ℕ) : Prop :=
  ∃ P : CochainComplex (ModuleCat.{u} A) ℤ, IsFiniteFree P ∧
    Nonempty (HomotopyEquiv P ((baseChange α).obj K)) ∧
    ∀ i : ℤ, Nonempty (P.X i ≃ₗ[A] (Fin (n i) → A))

/-- A finite free model along `α` gives a finite free model along any further ring map. -/
lemma HasModel.comp {A B : Type u} [CommRing A] [CommRing B] {α : R →+* A}
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ → ℕ} (h : HasModel α K n) (β : A →+* B) :
    HasModel (β.comp α) K n := by
  obtain ⟨P, hP, ⟨e⟩, hn⟩ := h
  refine ⟨(baseChange β).obj P, isFiniteFree_baseChange β hP,
    ⟨(baseChangeHomotopyEquiv β e).trans
      (HomotopyEquiv.ofIso ((baseChangeCompIso α β).app K).symm)⟩, fun i ↦ ?_⟩
  obtain ⟨ei⟩ := hn i
  exact nonempty_extendScalars_equiv β ei

/-- A finite free model after inverting `r` gives one after inverting any multiple of `r`. -/
lemma HasModel.of_dvd {K : CochainComplex (ModuleCat.{u} R) ℤ} {n : ℤ → ℕ} {r s : R}
    (h : HasModel (algebraMap R (Localization.Away r)) K n) (hrs : r ∣ s) :
    HasModel (algebraMap R (Localization.Away s)) K n := by
  have hu : IsUnit (algebraMap R (Localization.Away s) r) :=
    isUnit_of_dvd_unit (map_dvd _ hrs) (IsLocalization.Away.algebraMap_isUnit s)
  have := h.comp (IsLocalization.Away.lift (S := Localization.Away r) r hu)
  rwa [IsLocalization.Away.lift_comp] at this

/-- Near a prime, a strictly perfect complex has a finite free model after inverting one element
outside the prime, with term ranks the residue-field homology dimensions. -/
lemma exists_hasModel {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (p : Ideal R) [p.IsPrime] :
    ∃ r : R, r ∉ p ∧ HasModel (algebraMap R (Localization.Away r)) K
      (fun i ↦ Module.finrank p.ResidueField
        (((baseChange (algebraMap R p.ResidueField)).obj K).homology i)) := by
  obtain ⟨_, L, hL, hE, hRank⟩ := primeMinimalPerfect R K hK p
  obtain ⟨r, hr, P, hP, hPe, hPRank⟩ := primeFreeHomotopyDescent R K hK p _ L hL hE hRank
  exact ⟨r, hr, P, hP, hPe, hPRank⟩

variable {A : Type u} [CommRing A] {α : R →+* A}

/-- The homology of a scalar extension of a model is the homology of the corresponding scalar
extension of the modelled complex. -/
def transportIso {T : Type u} [CommRing T] {K : CochainComplex (ModuleCat.{u} R) ℤ}
    {P : CochainComplex (ModuleCat.{u} A) ℤ} (e : HomotopyEquiv P ((baseChange α).obj K))
    (β : A →+* T) (i : ℤ) :
    ((baseChange β).obj P).homology i ≅ ((baseChange (β.comp α)).obj K).homology i :=
  (baseChangeHomotopyEquiv β e).toHomologyIso i ≪≫
    HomologicalComplex.homologyMapIso ((baseChangeCompIso α β).app K).symm i

/-- The transport isomorphisms intertwine the map induced on models with the map induced by the
original chain map. -/
lemma transportIso_comm {T : Type u} [CommRing T] {K K₁ : CochainComplex (ModuleCat.{u} R) ℤ}
    {P P₁ : CochainComplex (ModuleCat.{u} A) ℤ} (e : HomotopyEquiv P ((baseChange α).obj K))
    (e₁ : HomotopyEquiv P₁ ((baseChange α).obj K₁)) (ψ : K ⟶ K₁) (β : A →+* T) (i : ℤ) :
    HomologicalComplex.homologyMap ((baseChange β).map (e.hom ≫ (baseChange α).map ψ ≫ e₁.inv))
        i ≫ (transportIso e₁ β i).hom =
      (transportIso e β i).hom ≫
        HomologicalComplex.homologyMap ((baseChange (β.comp α)).map ψ) i := by
  have hh := ((ModuleCat.extendScalars β).mapHomotopy
    (e₁.homotopyInvHomId.compLeftId (e.hom ≫ (baseChange α).map ψ))).homologyMap_eq i
  have hnat := ((baseChangeCompIso α β).inv.naturality ψ)
  change HomologicalComplex.homologyMap ((baseChange β).map (e.hom ≫ (baseChange α).map ψ ≫
      e₁.inv)) i ≫ (HomologicalComplex.homologyMap ((baseChange β).map e₁.hom) i ≫
      HomologicalComplex.homologyMap ((baseChangeCompIso α β).inv.app K₁) i) =
    (HomologicalComplex.homologyMap ((baseChange β).map e.hom) i ≫
      HomologicalComplex.homologyMap ((baseChangeCompIso α β).inv.app K) i) ≫
      HomologicalComplex.homologyMap ((baseChange (β.comp α)).map ψ) i
  change HomologicalComplex.homologyMap ((baseChange β).map
      ((e.hom ≫ (baseChange α).map ψ) ≫ e₁.inv ≫ e₁.hom)) i =
    HomologicalComplex.homologyMap ((baseChange β).map (e.hom ≫ (baseChange α).map ψ)) i at hh
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, ← Functor.map_comp,
    Category.assoc, Category.assoc, ← Category.assoc e.hom, hh, Functor.map_comp,
    HomologicalComplex.homologyMap_comp, Category.assoc, Category.assoc,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    show (baseChange β).map ((baseChange α).map ψ) ≫ (baseChangeCompIso α β).inv.app K₁ = _
      from hnat, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]

/-- Along isomorphisms intertwining two maps of modules, one map is bijective exactly when the
other is. -/
lemma bijective_iff_of_comm {T : Type u} [CommRing T] {M N M' N' : ModuleCat.{u} T}
    (f : M ⟶ N) (g : M' ⟶ N') (E : M ≅ M') (E₁ : N ≅ N') (h : f ≫ E₁.hom = E.hom ≫ g) :
    Function.Bijective f.hom ↔ Function.Bijective g.hom := by
  have e₁ : Function.Bijective f.hom ↔ IsIso f := (ConcreteCategory.isIso_iff_bijective f).symm
  have e₂ : Function.Bijective g.hom ↔ IsIso g := (ConcreteCategory.isIso_iff_bijective g).symm
  rw [e₁, e₂, ← isIso_comp_right_iff f E₁.hom, h, isIso_comp_left_iff]

/-- Along isomorphisms intertwining two pairs of maps of modules, joint injectivity of the
second pair implies joint injectivity of the first. -/
lemma jointly_injective_of_comm {T : Type u} [CommRing T] {M N₁ N₂ M' N₁' N₂' : ModuleCat.{u} T}
    (f₁ : M ⟶ N₁) (f₂ : M ⟶ N₂) (g₁ : M' ⟶ N₁') (g₂ : M' ⟶ N₂') (E : M ≅ M') (E₁ : N₁ ≅ N₁')
    (E₂ : N₂ ≅ N₂') (h₁ : f₁ ≫ E₁.hom = E.hom ≫ g₁) (h₂ : f₂ ≫ E₂.hom = E.hom ≫ g₂)
    (hg : ∀ c : M', g₁.hom c = 0 → g₂.hom c = 0 → c = 0) :
    ∀ c : M, f₁.hom c = 0 → f₂.hom c = 0 → c = 0 := by
  intro c hc₁ hc₂
  have hE : E.hom.hom c = 0 := by
    refine hg _ ?_ ?_
    · rw [← ModuleCat.comp_apply, ← h₁, ModuleCat.comp_apply, hc₁, map_zero]
    · rw [← ModuleCat.comp_apply, ← h₂, ModuleCat.comp_apply, hc₂, map_zero]
  exact E.toLinearEquiv.injective (hE.trans (map_zero _).symm)

/-- Bijectivity of a map induced on scalar extensions of models is bijectivity of the map
induced on the corresponding scalar extensions of the original complexes. -/
lemma bijective_homologyMap_iff_of_model {T : Type u} [CommRing T]
    {K K₁ : CochainComplex (ModuleCat.{u} R) ℤ} {P P₁ : CochainComplex (ModuleCat.{u} A) ℤ}
    (e : HomotopyEquiv P ((baseChange α).obj K)) (e₁ : HomotopyEquiv P₁ ((baseChange α).obj K₁))
    (ψ : K ⟶ K₁) (β : A →+* T) (γ : R →+* T) (hγ : β.comp α = γ) (i : ℤ) :
    Function.Bijective (HomologicalComplex.homologyMap
        ((baseChange β).map (e.hom ≫ (baseChange α).map ψ ≫ e₁.inv)) i).hom ↔
      Function.Bijective (HomologicalComplex.homologyMap ((baseChange γ).map ψ) i).hom := by
  subst hγ
  exact bijective_iff_of_comm _ _ _ _ (transportIso_comm e e₁ ψ β i)

/-- Joint injectivity of maps induced on scalar extensions of the original complexes implies
joint injectivity of the maps induced on the corresponding scalar extensions of models. -/
lemma jointly_injective_homologyMap_of_model {T : Type u} [CommRing T]
    {K K₁ K₂ : CochainComplex (ModuleCat.{u} R) ℤ} {P P₁ P₂ : CochainComplex (ModuleCat.{u} A) ℤ}
    (e : HomotopyEquiv P ((baseChange α).obj K)) (e₁ : HomotopyEquiv P₁ ((baseChange α).obj K₁))
    (e₂ : HomotopyEquiv P₂ ((baseChange α).obj K₂)) (ψ₁ : K ⟶ K₁) (ψ₂ : K ⟶ K₂) (β : A →+* T)
    (γ : R →+* T) (hγ : β.comp α = γ) (i : ℤ)
    (h : ∀ c : ((baseChange γ).obj K).homology i,
      (HomologicalComplex.homologyMap ((baseChange γ).map ψ₁) i).hom c = 0 →
      (HomologicalComplex.homologyMap ((baseChange γ).map ψ₂) i).hom c = 0 → c = 0) :
    ∀ c : ((baseChange β).obj P).homology i,
      (HomologicalComplex.homologyMap
        ((baseChange β).map (e.hom ≫ (baseChange α).map ψ₁ ≫ e₁.inv)) i).hom c = 0 →
      (HomologicalComplex.homologyMap
        ((baseChange β).map (e.hom ≫ (baseChange α).map ψ₂ ≫ e₂.inv)) i).hom c = 0 → c = 0 := by
  subst hγ
  exact jointly_injective_of_comm _ _ _ _ _ _ _ (transportIso_comm e e₁ ψ₁ β i)
    (transportIso_comm e e₂ ψ₂ β i) h

/-- The homology of a scalar extension of a model is linearly equivalent to the homology of the
corresponding scalar extension of the original complex. -/
lemma nonempty_homology_equiv_of_model {T : Type u} [CommRing T]
    {K : CochainComplex (ModuleCat.{u} R) ℤ} {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (e : HomotopyEquiv P ((baseChange α).obj K)) (β : A →+* T) (γ : R →+* T)
    (hγ : β.comp α = γ) (i : ℤ) :
    Nonempty (((baseChange β).obj P).homology i ≃ₗ[T] ((baseChange γ).obj K).homology i) := by
  subst hγ
  exact ⟨(transportIso e β i).toLinearEquiv⟩

end Langlands.Cohomology.ModuleComplex.FibreH0Spread
