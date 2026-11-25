/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorSignedRepresentatives
import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorLocalizationSections
import WeilConjectures.CategoryTheory.Abelian.ExtResolutionDerivedConnecting
/-! Independent comparison result for the principal torsor sign calculation. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite HomologicalComplex
namespace AlgebraicGeometry.Etale
/-- Normalized supported-Hom comparison commutes with the coefficient Yoneda boundary. -/
theorem principalTorsorConnectingComparison
    (C : PrincipalTorsorComparisons.{u}) (hC : C.Normalized)
    (T Z : Scheme.{u}) (i : Z ⟶ T) [IsClosedImmersion i] (W : T.Opens)
    (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hS : S.ShortExact) (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
    (L : InjectiveResolution S.X₃)
    (α : I.cocomplex ⟶ J.cocomplex) (β : J.cocomplex ⟶ L.cocomplex)
    (hαβ : α ≫ β = 0)
    (hα : I.ι ≫ α = (CochainComplex.single₀ _).map S.f ≫ J.ι)
    (hβ : J.ι ≫ β = (CochainComplex.single₀ _).map S.g ≫ L.ι)
    (hs : ∀ n : ℕ, Nonempty (((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    (x : Ext (principalTorsorLocalization i W h).X₃ S.X₃ 1) :
    C.relative T Z i W h S.X₁ I 1 (x.comp hS.extClass rfl) =
      relativeConnecting T (Scheme.Etale.mk W.ι) (ShortComplex.mk α β hαβ) hs 1
        (C.relative T Z i W h S.X₃ L 0 x) := by
  obtain ⟨z, hz, rfl⟩ := L.extMk_surjective x (0 + 1 + 1) rfl
  let s₁ : L.cocomplex.X 1 ⟶ J.cocomplex.X 1 := (hs 1).some.s
  let r₂ : J.cocomplex.X 2 ⟶ I.cocomplex.X 2 := (hs 2).some.r
  let s₂ : L.cocomplex.X 2 ⟶ J.cocomplex.X 2 := (hs 2).some.s
  let r₃ : J.cocomplex.X 3 ⟶ I.cocomplex.X 3 := (hs 3).some.r
  have hsg : s₁ ≫ β.f 1 = 𝟙 _ := (hs 1).some.s_g
  have hid : r₂ ≫ α.f 2 + β.f 2 ≫ s₂ = 𝟙 _ := (hs 2).some.id
  have hfr : α.f 3 ≫ r₃ = 𝟙 _ := (hs 3).some.f_r
  obtain ⟨b, hb⟩ : ∃ b : _ ⟶ J.cocomplex.X 1, b ≫ β.f 1 = z :=
    ⟨z ≫ s₁, by rw [Category.assoc, hsg, Category.comp_id]⟩
  have hbd : b ≫ J.cocomplex.d 1 2 ≫ β.f 2 = 0 := by
    rw [← β.comm, reassoc_of% hb, hz]
  obtain ⟨a, hba⟩ : ∃ a : _ ⟶ I.cocomplex.X 2, b ≫ J.cocomplex.d 1 2 = a ≫ α.f 2 := by
    refine ⟨b ≫ J.cocomplex.d 1 2 ≫ r₂, ?_⟩
    rw [Category.assoc, Category.assoc, eq_sub_of_add_eq hid, Preadditive.comp_sub,
      Preadditive.comp_sub, Category.comp_id, reassoc_of% hbd, zero_comp, sub_zero]
  have ha : a ≫ I.cocomplex.d 2 3 = 0 := by
    rw [← Category.comp_id (a ≫ I.cocomplex.d 2 3), ← hfr, Category.assoc,
      ← Category.assoc (I.cocomplex.d 2 3), ← α.comm 2 3, Category.assoc, ← Category.assoc a,
      ← hba]
    simp
  have hext : (L.extMk z (0 + 1 + 1) rfl hz).comp hS.extClass rfl =
      I.extMk a (1 + 1 + 1) rfl ha := by
    let := HasDerivedCategory.standard (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    have he := InjectiveResolution.extMk_resolution_connecting_eq_triangle hS
      (principalTorsorLocalization i W h).X₃ I J L α β hαβ hα hβ
      (fun k ↦ (hs k).some.shortExact) 1 z hz b hb a ha hba
    let := HasExt.standard (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    rw [Abelian.Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS _ rfl] at he
    apply Abelian.Ext.ext
    simpa only [Abelian.Ext.comp_hom, ShortComplex.ShortExact.extClass_hom,
      InjectiveResolution.extMk_hom] using he
  rw [hext]
  have hg := principalTorsorLocalization_g_one i W h (C.openSection T Z i W h)
    (hC.1 T Z i W h) (hC.2.1 T Z i W h)
  refine (hC.2.2 T Z i W h S.X₁ I 1 a ha).unique ?_
  refine (hC.2.2 T Z i W h S.X₃ L 0 z hz).connecting (ShortComplex.mk α β hαβ) hs
    (((principalTorsorLocalization i W h).g ≫ b).hom.app (op (Scheme.Etale.mk (𝟙 T)))
      (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))) ?_
    (principalTorsorLocalization_g_comp_restrict i W h hg b) _ ?_
  · rw [← hb]
    rfl
  · exact congrArg (fun k ↦ ((principalTorsorLocalization i W h).g ≫ k).hom.app
      (op (Scheme.Etale.mk (𝟙 T))) (torsorExtensionOne T (Scheme.Etale.mk (𝟙 T)))) hba.symm
end AlgebraicGeometry.Etale
