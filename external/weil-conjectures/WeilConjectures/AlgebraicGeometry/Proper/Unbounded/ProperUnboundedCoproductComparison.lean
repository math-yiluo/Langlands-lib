/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Unbounded.ProperUnboundedWindow
public import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts

/-! # Transport bounded coproduct comparisons through canonical proper windows. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private def transportColimit
    {C D : Type*} [Category* C] [Category* D] {I : Type*}
    (G H : C ⥤ D) (α : G ⟶ H) (K : I → C) (c : Cofan K)
    (hi : ∀ i, IsIso (α.app (K i))) (hp : IsIso (α.app c.pt))
    (hc : IsColimit (G.mapCocone c)) : IsColimit (H.mapCocone c) := by
  let e : Discrete.functor K ⋙ G ≅ Discrete.functor K ⋙ H :=
    NatIso.ofComponents (fun i ↦ asIso (α.app (K i.as))) (by
      intro i j f
      exact α.naturality ((Discrete.functor K).map f))
  refine (IsColimit.equivOfNatIsoOfIso e _ _ ?_) hc
  refine Cocone.ext (asIso (α.app c.pt)) ?_
  intro i
  dsimp [e]
  rw [Category.assoc, α.naturality]
  simp

/-- Window transport of the bounded coproduct comparison. -/
theorem properUnbounded_coproductComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ)
    (hwindow : ProperUnboundedWindowAssertions Λ p d)
    (hsumX : ∀ (I : Type (u + 1)) (K : I → DerivedCategory (pulledBackModuleObjects Λ X))
      (c : Cofan K), IsColimit c →
      (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt))
    (hsumY : ∀ (I : Type (u + 1)) (K : I → DerivedCategory (pulledBackModuleObjects Λ Y))
      (c : Cofan K), IsColimit c →
      (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt))
    (htrunc : ∀ (K : DerivedCategory (pulledBackModuleObjects Λ X)) (n : ℤ),
      (∀ m, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) →
      (∀ m, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncLE n).obj K))) ∧
      (∀ m, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj K))))
    (hH : ∀ (I : Type (u + 1))
      (K : Discrete I ⥤ DerivedCategory (pulledBackModuleObjects Λ Y)) (c : Cocone K),
      IsColimit c → ∀ q : ℤ,
        Nonempty (IsColimit ((DerivedCategory.homologyFunctor _ q).mapCocone c)))
    (hT : ∀ (I : Type (u + 1))
      (K : I → DerivedCategory (pulledBackModuleObjects Λ X)) (c : Cofan K),
      IsColimit c → ∀ q r : ℤ,
      Nonempty (IsColimit (((DerivedCategory.TStructure.t.truncLE q) ⋙
        DerivedCategory.TStructure.t.truncGE r).mapCocone c)))
    (hbounded : ∀ (a b : ℤ) (I : Type (u + 1))
      (K : I → DerivedCategory (pulledBackModuleObjects Λ X)),
      (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      (∀ i n, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        Nonempty (IsColimit ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.mapCocone c))) :
    ∀ (I : Type (u + 1))
      (K : I → DerivedCategory (pulledBackModuleObjects Λ X)),
    (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
    ∃ (c : Cofan K) (_ : IsColimit c)
      (c' : Cofan (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj (K i)))
      (hc' : IsColimit c'),
      (∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt)) ∧
      (∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj c'.pt)) ∧
      IsIso (hc'.desc (Cofan.mk
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.map (c.inj i)))) := by
  classical
  let A := pulledBackModuleObjects Λ X
  let B := pulledBackModuleObjects Λ Y
  let F : DerivedCategory A ⥤ DerivedCategory B := (CondensedRing.lowerStar Λ p).rightDerivedFunctor
  have cop (Z : Scheme.{u}) : HasCoproducts.{u + 1}
      (DerivedCategory (pulledBackModuleObjects Λ Z)) := by
    have : HasColimitsOfSize.{u + 1, u + 1} (pulledBackModuleObjects Λ Z) :=
      IsGrothendieckAbelian.hasColimits _
    have : HasCoproducts.{u + 1} (pulledBackModuleObjects Λ Z) := fun J ↦
      HasColimitsOfShape.of_small.{u + 1, u + 1} _ (Discrete J)
    exact derived_hasCoproducts
  have : HasCoproducts.{u + 1} (DerivedCategory A) := cop X
  have : HasCoproducts.{u + 1} (DerivedCategory B) := cop Y
  intro I K hK
  let c : Cofan K := Cofan.mk (∐ K) (Sigma.ι K)
  have hc : IsColimit c := coproductIsCoproduct K
  let c' : Cofan (fun i ↦ F.obj (K i)) := Cofan.mk (∐ fun i ↦ F.obj (K i)) (Sigma.ι _)
  have hc' : IsColimit c' := coproductIsCoproduct _
  refine ⟨c, hc, c', hc', hsumX I K c hc hK,
    hsumY I _ c' hc' (fun i ↦ (hwindow (K i) (hK i)).1), ?_⟩
  let cmp := hc'.desc (Cofan.mk (F.obj c.pt) (fun i ↦ F.map (c.inj i)))
  change IsIso cmp
  apply (DerivedCategory.isIso_iff B cmp).2
  intro q
  let H := DerivedCategory.homologyFunctor B q
  let L := (DerivedCategory.TStructure.t (C := A)).truncLE q
  let T := L ⋙ DerivedCategory.TStructure.t.truncGE (q - 2 * d - 1)
  let W := fun i ↦ T.obj (K i)
  have hW : ∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj (W i)) := fun i ↦
    (htrunc _ (q - 2 * d - 1) ((htrunc _ q (hK i)).1)).2
  have hWB : ∀ i n, n < q - 2 * d - 1 ∨ q < n →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (W i)) := by
    intro i n hn
    rcases hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ _ _ hn
    · exact DerivedCategory.isZero_of_isLE _ q n hn
  obtain ⟨cw, hcw, hFcw⟩ := hbounded (q - 2 * d - 1) q I W hW hWB
  have : PreservesColimit (Discrete.functor W) F :=
    preservesColimit_of_preserves_colimit_cocone hcw hFcw.some
  have : PreservesColimit (Discrete.functor K ⋙ T) F :=
    preservesColimit_of_iso_diagram F
      (Discrete.natIso (fun _ ↦ Iso.refl _) :
        Discrete.functor W ≅ Discrete.functor K ⋙ T)
  have hcT := (hT I K c hc q (q - 2 * d - 1)).some
  have hF : IsColimit ((T ⋙ F).mapCocone c) := isColimitOfPreserves F hcT
  have hFH : IsColimit ((T ⋙ F ⋙ H).mapCocone c) :=
    (hH I _ _ hF q).some
  let α : L ⋙ F ⋙ H ⟶ F ⋙ H :=
    Functor.whiskerRight (DerivedCategory.TStructure.t.truncLEι q) (F ⋙ H)
  let β : L ⋙ F ⋙ H ⟶ T ⋙ F ⋙ H :=
    Functor.whiskerRight (Functor.whiskerLeft L
      (DerivedCategory.TStructure.t.truncGEπ (q - 2 * d - 1))) (F ⋙ H)
  have hiα : ∀ i, IsIso (α.app (K i)) := fun i ↦
    ((hwindow (K i) (hK i)).2.2.2 q).2.1
  have hiβ : ∀ i, IsIso (β.app (K i)) := fun i ↦
    ((hwindow (K i) (hK i)).2.2.2 q).2.2
  have hpα : IsIso (α.app c.pt) :=
    ((hwindow c.pt (hsumX I K c hc hK)).2.2.2 q).2.1
  have hpβ : IsIso (β.app c.pt) :=
    ((hwindow c.pt (hsumX I K c hc hK)).2.2.2 q).2.2
  let e : Discrete.functor K ⋙ (L ⋙ F ⋙ H) ≅
      Discrete.functor K ⋙ (T ⋙ F ⋙ H) :=
    NatIso.ofComponents (fun i ↦ asIso (β.app (K i.as))) (by
      intro i j f
      exact β.naturality ((Discrete.functor K).map f))
  have hLH : IsColimit ((L ⋙ F ⋙ H).mapCocone c) := by
    apply (IsColimit.equivOfNatIsoOfIso e _ _ _).symm hFH
    refine Cocone.ext (asIso (β.app c.pt)) ?_
    intro i
    dsimp [e]
    change inv (β.app (K i.as)) ≫ (L ⋙ F ⋙ H).map (c.ι.app i) ≫ β.app c.pt =
      (T ⋙ F ⋙ H).map (c.ι.app i)
    simpa [Category.assoc] using
      congrArg (fun z ↦ inv (β.app (K i.as)) ≫ z) (β.naturality (c.ι.app i))
  have hFH' : IsColimit ((F ⋙ H).mapCocone c) :=
    transportColimit _ _ α K c hiα hpα hLH
  have hsource := (hH I _ c' hc' q).some
  have hs := (Cofan.isColimitMapCoconeEquiv H _ c').1 hsource
  have ht := (Cofan.isColimitMapCoconeEquiv (F ⋙ H) K c).1 hFH'
  let target := Cofan.mk (H.obj (F.obj c.pt)) (fun i ↦ H.map (F.map (c.inj i)))
  have heq : H.map cmp = hs.desc target := by
    apply hs.hom_ext
    intro i
    change H.map (c'.inj i.as) ≫ H.map cmp = _
    rw [← H.map_comp]
    rw [show c'.inj i.as ≫ cmp = F.map (c.inj i.as) from hc'.fac _ i]
    exact (hs.fac target i).symm
  rw [heq]
  exact (hs.nonempty_isColimit_iff_isIso_desc).mp ⟨ht⟩

end AlgebraicGeometry.ProEtale
