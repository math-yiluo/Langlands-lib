/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData
import all WeilConjectures.AlgebraicGeometry.AdicFiniteReductionData

/-! # Ordinary insertion coherence for scalar and geometric comparison

Source: Stacks Project, Modules on Sites, `lemma-adjointness-tensor-restrict`
and `lemma-adjoint-pullback-pushforward-modules`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard derivedExtension derivedPull
  DerivedCategory.Q CategoryTheory.constantSheaf CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  CochainComplex.IsKFlatTensor CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 10000] change_additive pull_additive SheafOfModules.instAbelian
attribute [local irreducible] adicFiniteComparisonData adicFinitePullbackData
attribute [local instance 10000] adicFiniteSectionModule

/-- The ordinary balancing isomorphism for a specified composite sheaf ring map.
Source: Stacks Project, Modules on Sites, `lemma-adjointness-tensor-restrict`.
(auxiliary; not a blueprint node). -/
def adicOrdinaryChangeComp {D : Type w} [SmallCategory D]
    {T : GrothendieckTopology D} {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V) (e : h = f ≫ g) :
    change f ⋙ change g ≅ change h :=
by
  cases e
  exact adicFiniteChangeComp f g

attribute [local irreducible] change

private theorem insertion_naturality
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) {M N : Mod R} (k : M ⟶ N) :
    (underlying R).map k ≫ insertion f N =
      insertion f M ≫ (underlying S).map ((change f).map k) := by
  have h := congrArg ((underlying R).map) ((adicFiniteOrdinaryUnit f).naturality k)
  simp only [Functor.map_comp] at h
  have he (Z : Mod R) : (underlying R).map ((adicFiniteOrdinaryUnit f).app Z) =
      insertion f Z := (adicFiniteOrdinaryUnit_existsUnique f).exists.choose_spec Z
  rw [he, he] at h
  exact h

private theorem pullInsertion_naturality
    {D E : Type w} [SmallCategory D] [SmallCategory E]
    {T : GrothendieckTopology D} {TE : GrothendieckTopology E}
    {L : Sheaf T (Type w) ⥤ Sheaf TE (Type w)} (F : InverseImageData L)
    {R : Sheaf T CommRingCat.{w}} {S : Sheaf TE CommRingCat.{w}}
    (c : F.rings.obj R ⟶ S) {M N : Mod R} (k : M ⟶ N) :
    L.map ((underlying R).map k) ≫ pullInsertion F c N =
      pullInsertion F c M ≫ (underlying S).map ((pull F c).map k) := by
  have hn := (F.algebra R).moduleUnderlying.inv.naturality k
  change L.map ((underlying R).map k) ≫ (F.algebra R).moduleUnderlying.inv.app N =
    (F.algebra R).moduleUnderlying.inv.app M ≫
      (underlying (F.rings.obj R)).map ((F.algebra R).modules.map k) at hn
  calc
    _ = ((F.algebra R).moduleUnderlying.inv.app M ≫
        (underlying (F.rings.obj R)).map ((F.algebra R).modules.map k)) ≫
          insertion c ((F.algebra R).modules.obj N) := by
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hn)
    _ = _ := by
      rw [Category.assoc, insertion_naturality]
      rfl

attribute [local irreducible] pull

private theorem specified_change_insertion
    {D : Type w} [SmallCategory D] {T : GrothendieckTopology D}
    {R S V : Sheaf T CommRingCat.{w}}
    (f : R ⟶ S) (g : S ⟶ V) (h : R ⟶ V) (e : h = f ≫ g) (M : Mod R) :
    insertion f M ≫ insertion g ((change f).obj M) ≫
      (underlying V).map ((adicOrdinaryChangeComp f g h e).hom.app M) = insertion h M := by
  cases e
  exact adicFiniteChangeComp_insertion f g M

@[no_expose]
private def ordinaryCandidate (X : Scheme.{u})
    {A B C : Type (max v (u + 1))} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f) :
    adicFiniteOrdinaryPullback.{u, v} X A ⋙
        change (adicFiniteConstantMap h (coefficientProEtaleModelTopology.{u, v} X)) ≅
      change (adicFiniteConstantMap h (smallModelComparisonEtaleTopology.{u, v} X)) ⋙
        adicFiniteOrdinaryPullback.{u, v} X C :=
  (Functor.isoWhiskerLeft (adicFiniteOrdinaryPullback.{u, v} X A)
    (adicOrdinaryChangeComp
      (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
      (adicFiniteConstantMap g (coefficientProEtaleModelTopology.{u, v} X))
      (adicFiniteConstantMap h (coefficientProEtaleModelTopology.{u, v} X))
      (adicFiniteConstantComp _ f g h e)).symm) ≪≫
  Functor.isoWhiskerRight (adicFiniteOrdinaryComparison.{u, v} X f)
    (change (adicFiniteConstantMap g (coefficientProEtaleModelTopology.{u, v} X))) ≪≫
  Functor.isoWhiskerLeft
    (change (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)))
    (adicFiniteOrdinaryComparison.{u, v} X g) ≪≫
  Functor.isoWhiskerRight
    (adicOrdinaryChangeComp
      (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
      (adicFiniteConstantMap g (smallModelComparisonEtaleTopology.{u, v} X))
      (adicFiniteConstantMap h (smallModelComparisonEtaleTopology.{u, v} X))
      (adicFiniteConstantComp _ f g h e))
    (adicFiniteOrdinaryPullback.{u, v} X C)

private theorem paste_insertions {H : Type*} [Category H]
    {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ C₁ C₂ C₃ D₂ : H}
    (i₀ : A₀ ⟶ A₁) (i₁ : A₁ ⟶ A₂) (i₂ : A₀ ⟶ A₃) (α : A₂ ⟶ A₃)
    (q₀ : A₀ ⟶ B₀) (q₁ : A₁ ⟶ C₁) (q₂ : A₂ ⟶ C₂) (q₃ : A₃ ⟶ C₃)
    (j₀ : B₀ ⟶ B₁) (j₁ : B₁ ⟶ B₂) (j₂ : B₀ ⟶ B₃) (β : B₂ ≅ B₃)
    (t : B₁ ⟶ C₁) (n : B₂ ⟶ D₂) (k : C₁ ⟶ D₂) (r : D₂ ⟶ C₂)
    (v : C₂ ⟶ C₃)
    (hα : i₀ ≫ i₁ ≫ α = i₂) (hβ : j₀ ≫ j₁ ≫ β.hom = j₂)
    (hf : i₀ ≫ q₁ = q₀ ≫ j₀ ≫ t) (hg : i₁ ≫ q₂ = q₁ ≫ k ≫ r)
    (hn : t ≫ k = j₁ ≫ n) (hp : α ≫ q₃ = q₂ ≫ v) :
    i₂ ≫ q₃ = q₀ ≫ j₂ ≫ β.inv ≫ n ≫ r ≫ v := by
  calc
    _ = i₀ ≫ i₁ ≫ α ≫ q₃ := by rw [← hα]; simp only [Category.assoc]
    _ = i₀ ≫ i₁ ≫ q₂ ≫ v := by rw [hp]
    _ = i₀ ≫ q₁ ≫ k ≫ r ≫ v := by rw [reassoc_of% hg]
    _ = q₀ ≫ j₀ ≫ t ≫ k ≫ r ≫ v := by rw [reassoc_of% hf]
    _ = q₀ ≫ j₀ ≫ j₁ ≫ n ≫ r ≫ v := by rw [reassoc_of% hn]
    _ = _ := by rw [← hβ]; simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem ordinaryCandidate_normalized (X : Scheme.{u})
    {A B C : Type (max v (u + 1))} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f) :
    adicFiniteOrdinaryComparisonFormula X h (ordinaryCandidate X f g h e) := by
  intro M
  let fe := adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X)
  let ge := adicFiniteConstantMap g (smallModelComparisonEtaleTopology.{u, v} X)
  let he := adicFiniteConstantMap h (smallModelComparisonEtaleTopology.{u, v} X)
  let fp := adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X)
  let gp := adicFiniteConstantMap g (coefficientProEtaleModelTopology.{u, v} X)
  let hh := adicFiniteConstantMap h (coefficientProEtaleModelTopology.{u, v} X)
  let α := adicOrdinaryChangeComp fe ge he (adicFiniteConstantComp _ f g h e)
  let β := adicOrdinaryChangeComp fp gp hh (adicFiniteConstantComp _ f g h e)
  have hα := specified_change_insertion fe ge he (adicFiniteConstantComp _ f g h e) M
  have hβ := specified_change_insertion fp gp hh (adicFiniteConstantComp _ f g h e)
    ((adicFiniteOrdinaryPullback.{u, v} X A).obj M)
  have hf := (adicFiniteOrdinaryComparison_existsUnique.{u, v} X f).exists.choose_spec M
  have hg := (adicFiniteOrdinaryComparison_existsUnique.{u, v} X g).exists.choose_spec
    ((change fe).obj M)
  have hn := insertion_naturality gp ((adicFiniteOrdinaryComparison.{u, v} X f).hom.app M)
  have hp := pullInsertion_naturality (adicFiniteComparisonData.{u, v} X)
    (constantMap (adicFiniteComparisonData.{u, v} X) C) (α.hom.app M)
  let L := smallModelComparisonPullback.{u, v} X
  let q := adicFiniteComparisonData.{u, v} X
  let U := underlying (constant (coefficientProEtaleModelTopology.{u, v} X) C)
  have ha := congrArg L.map hα
  simp only [Functor.map_comp] at ha
  dsimp only [ordinaryCandidate, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
  simp only [Functor.map_comp]
  exact paste_insertions
    (L.map (insertion fe M))
    (L.map (insertion ge ((change fe).obj M)))
    (L.map (insertion he M))
    (L.map ((underlying _).map (α.hom.app M)))
    (pullInsertion q (constantMap q A) M)
    (pullInsertion q (constantMap q B) ((change fe).obj M))
    (pullInsertion q (constantMap q C) ((change ge).obj ((change fe).obj M)))
    (pullInsertion q (constantMap q C) ((change he).obj M))
    (insertion fp ((adicFiniteOrdinaryPullback.{u, v} X A).obj M))
    (insertion gp ((change fp).obj ((adicFiniteOrdinaryPullback.{u, v} X A).obj M)))
    (insertion hh ((adicFiniteOrdinaryPullback.{u, v} X A).obj M))
    (U.mapIso (β.app ((adicFiniteOrdinaryPullback.{u, v} X A).obj M)))
    ((underlying _).map ((adicFiniteOrdinaryComparison.{u, v} X f).hom.app M))
    (U.map ((change gp).map ((adicFiniteOrdinaryComparison.{u, v} X f).hom.app M)))
    (insertion gp ((adicFiniteOrdinaryPullback.{u, v} X B).obj ((change fe).obj M)))
    (U.map ((adicFiniteOrdinaryComparison.{u, v} X g).hom.app ((change fe).obj M)))
    (U.map ((adicFiniteOrdinaryPullback.{u, v} X C).map (α.hom.app M)))
    ha hβ hf hg hn hp

/-- The ordinary scalar/geometric comparisons commute with successive scalar extension.
Source: Stacks Project, Modules on Sites, `lemma-adjointness-tensor-restrict`
and `lemma-adjoint-pullback-pushforward-modules`; the tensor insertion calculation
in proof step 2 of `lem-sfb-adic-comparison-composition`.
(auxiliary; not a blueprint node).

Proof: precompose both module maps with inverse-image insertion, followed by the
insertions of one for the two coefficient extensions. Scalar reassociation carries
these two insertions to insertion for the composite map. For the other route,
naturality of insertion and the two ordinary comparison normalization equations
carry them to the same inverse image of the composite insertion. Equality on these
insertions determines a module map by the successive tensor/restriction adjunctions
and the inverse-image/module-direct-image adjunction. This calculation is independent
of the rings and includes identity maps and the zero ring. -/
theorem adicOrdinaryComparison_composition (X : Scheme.{u})
    {A B C : Type (max v (u + 1))} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (e : h = g.comp f)
    (M : Mod (constant (smallModelComparisonEtaleTopology.{u, v} X) A)) :
    (adicOrdinaryChangeComp
        (adicFiniteConstantMap f (coefficientProEtaleModelTopology.{u, v} X))
        (adicFiniteConstantMap g (coefficientProEtaleModelTopology.{u, v} X))
        (adicFiniteConstantMap h (coefficientProEtaleModelTopology.{u, v} X))
        (adicFiniteConstantComp _ f g h e)).hom.app
          ((adicFiniteOrdinaryPullback.{u, v} X A).obj M) ≫
        (adicFiniteOrdinaryComparison.{u, v} X h).hom.app M =
      (change (adicFiniteConstantMap g (coefficientProEtaleModelTopology.{u, v} X))).map
          ((adicFiniteOrdinaryComparison.{u, v} X f).hom.app M) ≫
        (adicFiniteOrdinaryComparison.{u, v} X g).hom.app
          ((change (adicFiniteConstantMap f
            (smallModelComparisonEtaleTopology.{u, v} X))).obj M) ≫
        (adicFiniteOrdinaryPullback.{u, v} X C).map
          ((adicOrdinaryChangeComp
            (adicFiniteConstantMap f (smallModelComparisonEtaleTopology.{u, v} X))
            (adicFiniteConstantMap g (smallModelComparisonEtaleTopology.{u, v} X))
            (adicFiniteConstantMap h (smallModelComparisonEtaleTopology.{u, v} X))
            (adicFiniteConstantComp _ f g h e)).hom.app M) := by
  have hc : ordinaryCandidate X f g h e = adicFiniteOrdinaryComparison X h :=
    (adicFiniteOrdinaryComparison_existsUnique X h).unique
      (ordinaryCandidate_normalized X f g h e)
      (adicFiniteOrdinaryComparison_existsUnique X h).exists.choose_spec
  have hh := congr_app (congrArg Iso.hom hc) M
  rw [← hh]
  simp [ordinaryCandidate]

end AlgebraicGeometry.Scheme
