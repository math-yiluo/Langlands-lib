/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafModule
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine

/-!
# Endomorphisms of the Tate twists are finite

Let `Λ` be a finite commutative ring and `X` a scheme with finitely many connected components (for
instance a connected or a noetherian scheme). The endomorphisms of the constant complex `Λ_X` in
`D(X_ét, Λ)` are the global sections of the constant sheaf; these are locally constant functions
`X → Λ` (`AlgebraicGeometry.Scheme.isLocallyConstant_constantSheafToPointFunctionSheaf_app`), so
they are finite (`AlgebraicGeometry.Scheme.finite_sections_constantSheaf`,
`AlgebraicGeometry.Etale.finite_endomorphisms_constantComplex`). Tensoring with an object
having a tensor inverse is injective on morphisms
(`CategoryTheory.MonoidalCategory.whiskerRight_injective_of_tensorIsoUnit`), so every invertible
object, for instance every Tate twist `Λ_X(m)`, has finitely many endomorphisms
(`AlgebraicGeometry.Etale.finite_endomorphisms_tateObject`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C]

/-- Whiskering on the right with an object `M` which has a left tensor inverse `L`,
`M ⊗ L ≅ 𝟙`, is injective on morphisms. -/
lemma whiskerRight_injective_of_tensorIsoUnit {M L : C} (e : M ⊗ L ≅ 𝟙_ C) {A B : C} :
    Function.Injective (fun φ : A ⟶ B ↦ φ ▷ M) := by
  intro φ ψ h
  have h₁ : φ ▷ (M ⊗ L) = ψ ▷ (M ⊗ L) := by
    simp only at h
    rw [whiskerRight_tensor, whiskerRight_tensor, h]
  have h₂ (χ : A ⟶ B) : χ = (ρ_ A).inv ≫ A ◁ e.inv ≫ χ ▷ (M ⊗ L) ≫ B ◁ e.hom ≫ (ρ_ B).hom := by
    rw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, ← rightUnitor_inv_naturality_assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [h₂ φ, h₂ ψ, h₁]

end CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A global section of the constant étale sheaf `M` is a locally constant function on the points
of `X`: near every point it is constant on the image of an étale map, which is open. -/
lemma isLocallyConstant_constantSheafToPointFunctionSheaf_app (M : AddCommGrpCat.{u + 1})
    (σ : (sheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).obj
      (op (Etale.mk (𝟙 X)))) :
    IsLocallyConstant ((X.constantSheafToPointFunctionSheaf M).hom.app (op (Etale.mk (𝟙 X))) σ :
      X → M) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  obtain ⟨W, g, w, ⟨m, hm⟩, hgw⟩ := exists_of_mem_smallEtaleTopology
    (Presheaf.imageSieve_mem X.smallEtaleTopology
      (CategoryTheory.toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)) σ) x
  have hD (w' : W.left) :
      ((X.constantSheafToPointFunctionSheaf M).hom.app (op (Etale.mk (𝟙 X))) σ : X → M)
        (g.left w') = m := by
    have h₁ := congrArg (fun s ↦ (X.constantSheafToPointFunctionSheaf M).hom.app (op W) s w') hm
    have h₂ := NatTrans.naturality_apply (X.constantSheafToPointFunctionSheaf M).hom g.op σ
    simp only at h₁
    rw [constantSheafToPointFunctionSheaf_app_toSheafify] at h₁
    exact (congrFun h₂ w').symm.trans h₁.symm
  have hgW : g.left = W.hom := by
    have := CategoryTheory.Over.w ((Etale.forget X).map g)
    simp only at this
    exact (Category.comp_id _).symm.trans this
  refine ⟨Set.range g.left, ?_, ⟨w, hgw⟩, ?_⟩
  · rw [hgW]
    exact W.hom.isOpenMap.isOpen_range
  · rintro _ ⟨w', rfl⟩
    rw [hD, ← hgw, hD]

/-- **Global sections of a constant étale sheaf are finite** on a scheme with finitely many
connected components, for a finite group `M`: they are locally constant functions `X → M`
(`isLocallyConstant_constantSheafToPointFunctionSheaf_app`), hence determined by their values on
the connected components. -/
lemma finite_sections_constantSheaf [Finite (_root_.ConnectedComponents X)]
    (M : AddCommGrpCat.{u + 1}) [Finite M] :
    Finite ((sheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).obj
      (op (Etale.mk (𝟙 X)))) := by
  let ψ := (X.constantSheafToPointFunctionSheaf M).hom.app (op (Etale.mk (𝟙 X)))
  have hψ : Function.Injective ψ := by
    have : Mono ((sheafToPresheaf _ _).map (X.constantSheafToPointFunctionSheaf M)) :=
      Functor.map_mono _ _
    have : Mono ψ := (NatTrans.mono_iff_mono_app _).1 this _
    exact (AddCommGrpCat.mono_iff_injective _).1 this
  let r := Function.surjInv (_root_.ConnectedComponents.surjective_coe (α := X))
  refine Finite.of_injective (fun σ (c : _root_.ConnectedComponents X) ↦ (ψ σ : X → M) (r c))
    fun σ σ' h ↦ hψ ?_
  have hc (τ) (x : X) :
      (ψ τ : X → M) x = (ψ τ : X → M) (r (_root_.ConnectedComponents.mk x)) :=
    (isLocallyConstant_constantSheafToPointFunctionSheaf_app X M τ).apply_eq_of_isPreconnected
      isPreconnected_connectedComponent mem_connectedComponent
      (_root_.ConnectedComponents.coe_eq_coe'.1 (Function.surjInv_eq _ _))
  exact funext fun x ↦ (hc σ x).trans ((congrFun h _).trans (hc σ' x).symm)

/-- **Global sections of a constant étale sheaf of modules are finite** on a scheme with finitely
many connected components, for a finite module `M`: the forgetful functors to types preserve
sheafification, which reduces to the case of abelian groups (`finite_sections_constantSheaf`). -/
lemma finite_sections_constantSheaf_moduleCat [Finite (_root_.ConnectedComponents X)]
    {Λ : Type (u + 1)} [CommRing Λ] (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Finite ((sheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).obj
      (op (Etale.mk (𝟙 X)))) := by
  let M' := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj M
  have : Finite M' := ‹Finite M›
  have hfinite := finite_sections_constantSheaf X M'
  exact @Finite.of_equiv _ _ hfinite (((sheafifyComposeIso X.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat)
    ((Functor.const X.Etaleᵒᵖ).obj M')).app _).toEquiv.symm.trans
      ((sheafifyComposeIso X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ))
        ((Functor.const X.Etaleᵒᵖ).obj M)).app _).toEquiv)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})

/-- **The endomorphisms of the constant complex are finite** over a scheme with finitely many
connected components: they are the global sections of the constant sheaf `Λ_X`
(`AlgebraicGeometry.Scheme.finite_sections_constantSheaf_moduleCat`). -/
lemma finite_endomorphisms_constantComplex [Finite (_root_.ConnectedComponents X)] :
    Finite (constantComplex Λ X ⟶ constantComplex Λ X) := by
  let F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)
  let hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
  let adj := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT
  have hΓ := finite_sections_constantSheaf_moduleCat X (ModuleCat.of Λ Λ)
  have h₁ := @Finite.of_injective (ModuleCat.of Λ Λ ⟶ ((sheafSections X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)).obj (op (MorphismProperty.Over.mk ⊤ (𝟙 X) _))).obj F) _ hΓ
    (fun g ↦ g.hom (1 : Λ))
    fun g g' h ↦ ModuleCat.hom_ext (LinearMap.ext_ring h)
  have h₂ : Finite (F ⟶ F) := Finite.of_equiv _ (adj.homEquiv _ _).symm
  let e := constantComplexIsoSingleFunctorConstantSheaf Λ X
  exact Finite.of_equiv _ ((Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor _ 0))
    |>.homEquiv.trans (e.homCongr e).symm)

variable {Λ X} in
/-- **An invertible object of `D(X_ét, Λ)` has finitely many endomorphisms** over a scheme with
finitely many connected components: `φ ↦ φ ⊗ M` embeds them into the endomorphisms of
`Λ_X ≅ L ⊗ M`. -/
lemma finite_endomorphisms_of_isInvertible [Finite (_root_.ConnectedComponents X)]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.isInvertible Λ X L) : Finite (L ⟶ L) := by
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := hL
  have := finite_endomorphisms_constantComplex Λ X
  exact Finite.of_injective (fun φ : L ⟶ L ↦ e₁.inv ≫ φ ▷ M ≫ e₁.hom) fun φ ψ h ↦
    whiskerRight_injective_of_tensorIsoUnit (A := L) (B := L) e₂ (by simpa using h)

/-- **The Tate twists have finitely many endomorphisms** over a scheme with finitely many
connected components (for instance a connected or a noetherian scheme). -/
lemma finite_endomorphisms_tateObject [HasTateTwist Λ] [HasInvertibleExponent Λ X]
    [Finite (_root_.ConnectedComponents X)] (m : ℤ) :
    Finite (tateObject Λ X m ⟶ tateObject Λ X m) :=
  finite_endomorphisms_of_isInvertible (HasTateTwist.isInvertible_twistObject X m)

end AlgebraicGeometry.Etale
