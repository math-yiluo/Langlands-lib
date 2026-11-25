/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.AffineHom
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
public import Mathlib.Algebra.Module.Presentation.Finite
public import WeilConjectures.Mathlib.Algebra.Module.Presentation.Tensor

/-!
# Presentations of global sections of modules on affine schemes

On an affine scheme, quasi-coherent modules are determined by their global sections. We express
this in terms of presentations `Module.Relations.Solution.IsPresentation` of the global sections:

- if `s` presents `Γ(N, ⊤)` by relations `ρ` and `g : Y ⟶ Z` is a morphism of affine schemes,
  then the pullbacks `pullbackΓ g N (s.var i)` present `Γ(g^* N, ⊤)` by the relations `ρ` with
  coefficients pulled back along `g`
  (`AlgebraicGeometry.Scheme.Modules.exists_isPresentation_pullbackΓ`);
- morphisms out of a module whose global sections are presented by `s` are determined by the
  images of the generators, and any solution of the relations in the global sections of the
  target comes from a morphism
  (`AlgebraicGeometry.Scheme.Modules.hom_ext_of_isPresentation`,
  `AlgebraicGeometry.Scheme.Modules.exists_hom_of_isPresentation`);
- for finitely many generators and relations there is a module of finite presentation whose
  global sections are presented by them
  (`AlgebraicGeometry.Scheme.Modules.exists_isFinitePresentation_isPresentation`).
-/

@[expose] public section

universe w₀ w₁ u

open CategoryTheory Module

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The pullback of global sections is semilinear along `g.appTop`. -/
lemma pullbackΓ_smul_appTop (g : Y ⟶ X) (M : X.Modules) (r : Γ(X, ⊤)) (m : Γ(M, ⊤)) :
    pullbackΓ g M (r • m) = g.appTop r • pullbackΓ g M m := by
  rw [pullbackΓ_apply, pullbackΓ_apply]
  exact Hom.app_smul _ r m

/-- The pullback of a linear combination of global sections is the linear combination of the
pullbacks, with coefficients pulled back along `g.appTop`. -/
lemma pullbackΓ_linearCombination (g : Y ⟶ X) (M : X.Modules) {G : Type*} (v : G → Γ(M, ⊤))
    (a : G →₀ Γ(X, ⊤)) :
    pullbackΓ g M (Finsupp.linearCombination Γ(X, ⊤) v a) =
      Finsupp.linearCombination Γ(Y, ⊤) (fun i ↦ pullbackΓ g M (v i))
        (Finsupp.mapRange g.appTop.hom (map_zero _) a) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapRange_add (map_add _), map_add, map_add, map_add, ha, hb]
  | single i r => simp [pullbackΓ_smul_appTop]

/-- **Presentations of the global sections of a pullback, affine case.** If `s` presents the
global sections of a quasi-coherent module `N` on an affine scheme `Z` by relations `ρ`, and
`g : Y ⟶ Z` is a morphism from an affine scheme, then the pullbacks of the generators present the
global sections of `g^* N` by the relations `ρ` base changed along `g.appTop`. -/
theorem exists_isPresentation_pullbackΓ [IsAffine Y] [IsAffine Z] (g : Y ⟶ Z) (N : Z.Modules)
    [N.IsQuasicoherent] {ρ : Relations.{w₀, w₁} Γ(Z, ⊤)} {s : ρ.Solution Γ(N, ⊤)}
    (hs : s.IsPresentation) :
    ∃ t : (ρ.baseChange g.appTop.hom).Solution Γ((pullback g).obj N, ⊤),
      t.IsPresentation ∧ ∀ i, t.var i = pullbackΓ g N (s.var i) := by
  have hUV : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ ⊤ := le_of_eq g.preimage_top.symm
  obtain ⟨e, he⟩ := exists_linearEquiv_pullback_sections g N (isAffineOpen_top Z)
    (isAffineOpen_top Y) hUV
  let := (g.appLE ⊤ ⊤ hUV).hom.toAlgebra
  have hring : g.appLE ⊤ ⊤ hUV = g.appTop := by
    exact g.appLE_eq_app
  have h₁ := (hs.baseChange (B := Γ(Y, ⊤))).of_linearEquiv e
  have hc (r : ρ.R) : ((ρ.baseChange (algebraMap Γ(Z, ⊤) Γ(Y, ⊤)))).relation r =
      Finsupp.mapRange g.appTop.hom (map_zero _) (ρ.relation r) := by
    ext x
    change (g.appLE ⊤ ⊤ hUV).hom (ρ.relation r x) = g.appTop.hom (ρ.relation r x)
    rw [hring]
  refine ⟨_, h₁.ofRelationEq hc, fun i ↦ ?_⟩
  change e (1 ⊗ₜ s.var i) = _
  rw [he, pullbackΓ_eq]
  congr 2

variable [IsAffine Y] {M N : Y.Modules} [M.IsQuasicoherent]
  {ρ : Relations.{w₀, w₁} Γ(Y, ⊤)} {s : ρ.Solution Γ(M, ⊤)}

omit [IsAffine Y] [M.IsQuasicoherent] in
/-- A morphism `M ⟶ N`, on global sections, is a solution of the relations presenting
`Γ(M, ⊤)`. -/
lemma postcomp_appₗ_var (φ : M ⟶ N) (i : ρ.G) :
    (s.postcomp (Hom.appₗ φ ⊤)).var i = φ.app ⊤ (s.var i) :=
  rfl

/-- Morphisms out of a quasi-coherent module on an affine scheme whose global sections are
presented by `s` agree if they agree on the generators `s.var i`. -/
lemma hom_ext_of_isPresentation (hs : s.IsPresentation) {α β : M ⟶ N}
    (h : ∀ i, α.app ⊤ (s.var i) = β.app ⊤ (s.var i)) : α = β := by
  have : Hom.appₗ α ⊤ = Hom.appₗ β ⊤ := hs.postcomp_injective (Relations.Solution.ext
    (funext fun i ↦ h i))
  exact hom_ext_of_isAffine fun m ↦ LinearMap.congr_fun this m

/-- On an affine scheme, every solution in `Γ(N, ⊤)` of the relations presenting the global
sections of a quasi-coherent module `M` is the image of the generators under a morphism
`M ⟶ N`. -/
lemma exists_hom_of_isPresentation [N.IsQuasicoherent] (hs : s.IsPresentation)
    (t : ρ.Solution Γ(N, ⊤)) : ∃ φ : M ⟶ N, ∀ i, φ.app ⊤ (s.var i) = t.var i := by
  obtain ⟨φ, hφ⟩ := exists_hom_app_top_eq_of_isAffine (hs.desc t)
  exact ⟨φ, fun i ↦ (hφ _).trans (hs.desc_var t i)⟩

/-- On an affine scheme, two quasi-coherent modules whose global sections are presented by the
same relations are isomorphic, compatibly with the generators. -/
lemma exists_iso_of_isPresentation [N.IsQuasicoherent] (hs : s.IsPresentation)
    {t : ρ.Solution Γ(N, ⊤)} (ht : t.IsPresentation) :
    ∃ e : M ≅ N, ∀ i, e.hom.app ⊤ (s.var i) = t.var i := by
  obtain ⟨φ, hφ⟩ := exists_hom_of_isPresentation hs t
  obtain ⟨ψ, hψ⟩ := exists_hom_of_isPresentation ht s
  refine ⟨⟨φ, ψ, hom_ext_of_isPresentation hs fun i ↦ ?_,
    hom_ext_of_isPresentation ht fun i ↦ ?_⟩, hφ⟩
  · rw [Hom.comp_app, ConcreteCategory.comp_apply, hφ, hψ, Hom.id_app]
    rfl
  · rw [Hom.comp_app, ConcreteCategory.comp_apply, hψ, hφ, Hom.id_app]
    rfl

/-- **Modules with prescribed global sections, affine case.** For finitely many generators and
relations with coefficients in the global functions of an affine scheme `Z`, there is a module of
finite presentation on `Z` whose global sections are presented by them. -/
theorem exists_isFinitePresentation_isPresentation [IsAffine Z] (ρ : Relations.{u, u} Γ(Z, ⊤))
    [Finite ρ.G] [Finite ρ.R] :
    ∃ (N : Z.Modules) (s : ρ.Solution Γ(N, ⊤)), N.IsFinitePresentation ∧ s.IsPresentation := by
  let R : CommRingCat.{u} := Γ(Z, ⊤)
  let Q : ModuleCat.{u} R := ModuleCat.of R ρ.Quotient
  let T : (Spec R).Modules := tilde Q
  let eT : ρ.Quotient ≃ₗ[R] Γ(T, ⊤) := (tilde.isoTop Q).toLinearEquiv
  have h₀ := (Relations.Solution.ofQuotient_isPresentation ρ).of_linearEquiv eT
  have h₁ := h₀.ofSMulEq (f := (Scheme.ΓSpecIso R).inv.hom) (smul_top_eq T)
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.surjective
  have : Module.FinitePresentation R Γ(T, ⊤) :=
    have : Finite (Presentation.ofIsPresentation h₀).G := ‹Finite ρ.G›
    have : Finite (Presentation.ofIsPresentation h₀).R := ‹Finite ρ.R›
    (Presentation.ofIsPresentation h₀).finitePresentation
  obtain ⟨P, hP⟩ := exists_presentation_isFinite_of_finitePresentation T
  have : T.IsFinitePresentation := P.isFinitePresentation
  obtain ⟨t, ht, -⟩ := exists_isPresentation_pullbackΓ Z.toSpecΓ T h₁
  have hc (r : ρ.R) : (((ρ.baseChange (Scheme.ΓSpecIso R).inv.hom)).baseChange
      Z.toSpecΓ.appTop.hom).relation r = ρ.relation r := by
    ext g
    simp only [Finsupp.mapRange_apply, Scheme.toSpecΓ_appTop]
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
    rfl
  exact ⟨_, _, inferInstance, ht.ofRelationEq hc⟩

end AlgebraicGeometry.Scheme.Modules
