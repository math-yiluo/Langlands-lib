/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionFinitePull
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionDerivedPull
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImage
import WeilConjectures.AlgebraicGeometry.ConstantCompletionOrdinaryReducedPull

/-!
# Constant coefficient completion: CompletedFinitePull

The completed finite pullback comparison (`completedFinitePull_existsUnique`).

Part of the split of `Sheaf.Paper.ConstantCompletionEquivalence`.
Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local irreducible] completed
variable {J A I}
attribute [local irreducible] derivedExtension
attribute [local irreducible] SheafOfModules.monoidalCategory
variable (J A I)
variable {J A I}
attribute [local irreducible] strictLimit
variable (J A I)
attribute [local irreducible] ordinaryUnit
attribute [local irreducible] quotientPresentation
variable {J A I}
variable {C' : Type u} [SmallCategory C'] {J' : GrothendieckTopology C'}
variable {L : Sheaf J (Type u) ⥤ Sheaf J' (Type u)} (F : InverseImageData L)
attribute [local semireducible] completed
attribute [local irreducible] completed
variable (V : Sheaf J' (Type u) ⥤ Sheaf J (Type u)) (adj : L ⊣ V)
variable [hL : PreservesFiniteLimits L]
attribute [local irreducible] derivedPull pull change

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reduced_square_isIso
    {M₀ M₁ M₂ M₃ M₄ D₀ D₁ D₂ D₃ D₄ : Type*}
    [Category M₀] [Category M₁] [Category M₂] [Category M₃] [Category M₄]
    [Preadditive M₀] [Preadditive M₁] [Preadditive M₂] [Preadditive M₃]
    [Preadditive M₄]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    (q₀ : CochainComplex M₀ ℤ ⥤ D₀) (q₁ : CochainComplex M₁ ℤ ⥤ D₁)
    (q₂ : CochainComplex M₂ ℤ ⥤ D₂) (q₃ : CochainComplex M₃ ℤ ⥤ D₃)
    (q₄ : CochainComplex M₄ ℤ ⥤ D₄)
    (r : M₀ ⥤ M₁) (s : M₂ ⥤ M₃) (p : M₁ ⥤ M₃) (b : M₀ ⥤ M₂)
    (e : M₃ ⥤ M₄)
    [r.PreservesZeroMorphisms] [s.PreservesZeroMorphisms]
    [p.PreservesZeroMorphisms] [b.PreservesZeroMorphisms] [e.PreservesZeroMorphisms]
    {dr : D₀ ⥤ D₁} {ds : D₂ ⥤ D₃} {dp : D₁ ⥤ D₃} {db : D₀ ⥤ D₂}
    (de : D₃ ⥤ D₄)
    (α : r.mapHomologicalComplex (.up ℤ) ⋙ q₁ ≅ q₀ ⋙ dr)
    (βp : q₁ ⋙ dp ⟶ p.mapHomologicalComplex (.up ℤ) ⋙ q₃)
    (γ : r ⋙ p ⟶ b ⋙ s)
    (βb : q₀ ⋙ db ⟶ b.mapHomologicalComplex (.up ℤ) ⋙ q₂)
    (δ : s.mapHomologicalComplex (.up ℤ) ⋙ q₃ ≅ q₂ ⋙ ds)
    (ε : q₃ ⋙ de ⟶ e.mapHomologicalComplex (.up ℤ) ⋙ q₄)
    (η : dr ⋙ dp ⟶ db ⋙ ds) (P : CochainComplex M₀ ℤ)
    (h : DerivedPullComparisonFormula q₀ q₁ q₂ q₃ r s p b α βp γ βb δ η P)
    [IsIso (βp.app ((r.mapHomologicalComplex (.up ℤ)).obj P))]
    [IsIso (βb.app P)]
    [IsIso (ε.app (((r ⋙ p).mapHomologicalComplex (.up ℤ)).obj P))]
    [IsIso (ε.app (((b ⋙ s).mapHomologicalComplex (.up ℤ)).obj P))]
    (hγ : ∀ M, IsIso (e.map (γ.app M))) :
    IsIso (de.map (η.app (q₀.obj P))) := by
  let f := (NatTrans.mapHomologicalComplex γ (.up ℤ)).app P
  have hf (j : ℤ) : IsIso (((e.mapHomologicalComplex (.up ℤ)).map f).f j) :=
    hγ (P.X j)
  have : IsIso ((e.mapHomologicalComplex (.up ℤ)).map f) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hn := ε.naturality f
  dsimp only [Functor.comp_map] at hn
  have hr := congrArg de.map h
  simp only [Functor.map_comp] at hr
  have he : de.map (η.app (q₀.obj P)) ≫
      de.map (ds.map (βb.app P) ≫
        δ.inv.app ((b.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      ε.app (((b ⋙ s).mapHomologicalComplex (.up ℤ)).obj P) =
    de.map (dp.map (α.inv.app P) ≫
      βp.app ((r.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      ε.app (((r ⋙ p).mapHomologicalComplex (.up ℤ)).obj P) ≫
      q₄.map ((e.mapHomologicalComplex (.up ℤ)).map f) := by
    have hh := congrArg (fun k ↦ k ≫
      ε.app (((b ⋙ s).mapHomologicalComplex (.up ℤ)).obj P)) hr.symm
    have hh' := congrArg (fun k ↦ de.map (dp.map (α.inv.app P)) ≫
      de.map (βp.app ((r.mapHomologicalComplex (.up ℤ)).obj P)) ≫ k) hn
    simp only [Category.assoc] at hh
    simpa only [Functor.map_comp, Category.assoc] using hh.trans hh'
  have : IsIso (de.map (η.app (q₀.obj P)) ≫
      (de.map (ds.map (βb.app P) ≫
        δ.inv.app ((b.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      ε.app (((b ⋙ s).mapHomologicalComplex (.up ℤ)).obj P))) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right (de.map (η.app (q₀.obj P)))
    (de.map (ds.map (βb.app P) ≫
      δ.inv.app ((b.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        ε.app (((b ⋙ s).mapHomologicalComplex (.up ℤ)).obj P))

attribute [local irreducible] dres

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reduced_derivedPullComparison_isIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    IsIso (Functor.whiskerRight (derivedPullComparison F V adj A I)
      (extend (quotient J' A I n))) := by
  let := HasDerivedCategory.standard (Mod (completed J A I))
  let := HasDerivedCategory.standard (Mod (constant J A))
  let := HasDerivedCategory.standard (Mod (completed J' A I))
  let := HasDerivedCategory.standard (Mod (constant J' A))
  let := HasDerivedCategory.standard (Mod (finite J' A I n))
  let φ := coefficientMap J A I
  let ψ := coefficientMap J' A I
  let p := derivedPull F V adj (constantMap F A)
  let b := derivedPull F V adj (completedMap F A I)
  let q := quotient J' A I n
  let τ := Functor.whiskerRight (derivedPullComparison F V adj A I) (extend q)
  let P (X : Cx (completed J A I)) :=
    X.IsKFlatTensor ∧ ∀ j : ℤ, SheafOfModules.IsFlat (X.X j)
  have hrep (X : Cx (completed J A I)) (hX : P X) :
      IsIso (τ.app ((Q (completed J A I)).obj X)) := by
    have hr := restricted_kFlat φ (flat_and_quotients J A I).1 X hX.1
    have hrf := restricted_flat φ (flat_and_quotients J A I).1 X hX.1 hX.2
    have hs := pull_flat_kFlat F V adj (constantMap F A) _ hr hrf
    have ht := pull_flat_kFlat F V adj (completedMap F A I) X hX.1 hX.2
    have htr := restricted_kFlat ψ (flat_and_quotients J' A I).1 _ ht.1
    have := p.computation _ hr hrf
    have := b.computation X hX.1 hX.2
    have hεS : IsIso ((extendComparison q).app
        (((res φ ⋙ pull F (constantMap F A)).mapHomologicalComplex (.up ℤ)).obj X)) :=
      (derivedExtension q).computation _ hs.1
    have hεT : IsIso ((extendComparison q).app
        (((pull F (completedMap F A I) ⋙ res ψ).mapHomologicalComplex (.up ℤ)).obj X)) :=
      (derivedExtension q).computation _ htr
    have ho := ordinaryReducedPull_isIso F V adj A I n
    apply reduced_square_isIso
      (Q (completed J A I)) (Q (constant J A)) (Q (completed J' A I))
      (Q (constant J' A)) (Q (finite J' A I n))
      (res φ) (res ψ) (pull F (constantMap F A)) (pull F (completedMap F A I))
      (change q) (extend q) (resFactors φ) p.comparison (ordinaryPullComparison F A I)
      b.comparison (resFactors ψ) (extendComparison q) (derivedPullComparison F V adj A I) X
    · exact (derivedPullComparison_existsUnique F V adj A I).exists.choose_spec X hX.1 hX.2
    · intro M
      exact NatIso.isIso_app_of_isIso (Functor.whiskerRight
        (ordinaryPullComparison F A I) (change q)) M
  obtain ⟨e, he⟩ := resolving_iso _ _ P (module_flat_kFlat_resolution (J := J))
    (fun X hX ↦ @asIso _ _ _ _ (τ.app ((Q (completed J A I)).obj X)) (hrep X hX))
    (fun X Y _ _ f ↦ τ.naturality ((Q (completed J A I)).map f))
  have hτ : e.hom = τ := by
    apply resolving_nat_ext P (module_flat_kFlat_resolution (J := J))
    intro X hX
    exact he X hX
  change IsIso τ
  rw [← hτ]
  infer_instance

/-- Completed pullback has the asserted finite comparison in D(A/I^(n+1)) on the second
site. Its inverse is exactly the finite reduction of the unreduced scalar comparison,
after the canonical constant-pullback tensor reassociation. Source: Stacks 099L, 06YY
(auxiliary; not a blueprint node).
Proof: choose one flat-term K-flat completed-coefficient model P. Both sides reduce to
the same quotient u^(-1)P/I^(n+1)u^(-1)P, by finiteComparison and inverse image exactness.
The scalar comparison sends p to 1 tensor p; finite reduction sends its image to the
same quotient class, inverse to the displayed comparison. Every construction commutes
with maps of models and with quotient transitions before localization, and therefore
after descent. The inverse equation fixes the natural isomorphism uniquely. -/
theorem completedFinitePull_existsUnique (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! e : (derivedPull F V adj (completedMap F A I)).functor ⋙
          dres (coefficientMap J' A I) ⋙ extend (quotient J' A I n) ≅
        dres (coefficientMap J A I) ⋙ extend (quotient J A I n) ⋙
          (derivedPull F V adj (constantMap F (A ⧸ I ^ (n + 1)))).functor,
      ∀ M : D (completed J A I),
        (extend (quotient J' A I n)).map ((derivedPullComparison F V adj A I).app M) =
          (finitePull F V adj A I n).hom.app ((dres (coefficientMap J A I)).obj M) ≫
            e.inv.app M := by
  let a := Functor.isoWhiskerLeft (dres (coefficientMap J A I))
    (finitePull F V adj A I n)
  let τ := Functor.whiskerRight (derivedPullComparison F V adj A I)
    (extend (quotient J' A I n))
  have : IsIso τ := reduced_derivedPullComparison_isIso F V adj A I n
  let e := (asIso τ).symm ≪≫ a
  refine ⟨e, ?_, ?_⟩
  · intro M
    change τ.app M = a.hom.app M ≫ (a.inv.app M ≫ (asIso τ).hom.app M)
    simp only [Iso.hom_inv_id_app_assoc, asIso_hom]
  · intro e' he'
    apply Iso.ext_inv
    apply NatTrans.ext
    funext M
    apply (cancel_epi (a.hom.app M)).1
    exact (he' M).symm.trans (by
      change τ.app M = a.hom.app M ≫ (a.inv.app M ≫ τ.app M)
      simp only [Iso.hom_inv_id_app_assoc])

end CategoryTheory.ConstantCompletion
