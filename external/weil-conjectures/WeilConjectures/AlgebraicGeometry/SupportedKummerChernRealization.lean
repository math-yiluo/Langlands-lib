/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerBoundary

/-!
# Chern normalization of the supported Cartier Kummer class

Source: blueprint lemma-cycle-class-cartier-divisor; Stacks 03PL and 0A45
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Match the stored instances of the boundary and scalar interfaces.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem integral_section (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : supportedIntegralConstant T ⟶ F) :
    (Sheaf.H.equiv₀ F (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).symm
      (f.hom.app (op (Scheme.Etale.mk (𝟙 T))) (supportedIntegralOne T)) = Ext.mk₀ f := by
  apply (Sheaf.H.equiv₀ F
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).injective
  rw [AddEquiv.apply_symm_apply]
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply]
  rw [show Ext.addEquiv₀ (Ext.mk₀ f) = f from Ext.addEquiv₀.apply_symm_apply _]
  rw [Adjunction.homAddEquiv_apply, constantSheafAdj_homEquiv_apply]
  rfl

/-- Forgetting support in the normalized relative boundary gives the positive Kummer
Chern class of the dual Cartier ideal, with the canonical integral constant unit.
Source: Stacks 03PL, 0A45; blueprint lemma-cycle-class-cartier-divisor, paragraphs 3--4
(auxiliary; not a blueprint node).

Proof: take the torsor extension in the boundary specification. Its fibre over the
supported section one is the frame torsor of O(D). Pulling this extension back along
the integral constant unit gives the extension classified by that frame torsor.
The torsor/H1 comparison identifies its boundary with the Picard class of O(D).
Compose with the positive Kummer boundary and the root tensor map. Naturality of
Yoneda composition and coefficient forgetting gives the displayed Chern class.
-/
theorem supported_kummer_chern_realization (T : Scheme.{u}) (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) {D : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (Scheme.finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ) :
    (Ext.mk₀ (supportedIntegralUnit i)).comp
      ((Ext.mk₀ (supportedIntegralGenerator A i)).comp
        (κ.mapExactFunctor (moduleAbelianForget A T)) (zero_add 2))
      (zero_add 2) = supportedKummerChern A N hA i hI hT := by
  classical
  let := hI.isInvertible_dual_toModules
  let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  let W : T.Opens :=
    ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  unfold SupportedKummerBoundary at hκ
  obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hext⟩ := hκ W rfl
  let P := Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)
  let terminal := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T
  let s := (supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
    (supportedIntegralOne T)
  let Q := Sheaf.Torsor.lifts terminal hE s
  have hp : Sheaf.Torsor.classH1 T.gmSheaf terminal ⟦P⟧ =
      Sheaf.H.δSections hE terminal s := by
    have heq := Sheaf.Torsor.classH1_eq_map_of_equivariant terminal (𝟙 T.gmSheaf) P Q
      (fun U p ↦ ⟨f.hom.app U p, hb U p⟩)
      (fun U V g p ↦ Subtype.ext (by
        change E.obj.map g (f.hom.app U p) = f.hom.app V (P.sheaf.obj.map g p)
        exact ConcreteCategory.congr_hom (f.hom.naturality g).symm p))
      (fun U g p ↦ Subtype.ext (by
        change f.hom.app U (P.vadd U g p) = (@id (E.obj.obj U) (f.hom.app U p)) + a.hom.app U g
        simpa only [id_eq, P, add_comm] using hf U g p))
    rw [Sheaf.Torsor.classH1_lifts] at heq
    simpa only [Sheaf.H.map_apply, Ext.comp_mk₀_id] using heq.symm
  have hpic : Scheme.Pic.toCohomologicalPicardGroup T
      (Scheme.Pic.ofIsInvertible (Scheme.Modules.dual i.ker.toModules)) =
      Sheaf.H.δSections hE terminal s := by
    rw [Scheme.Pic.toCohomologicalPicardGroup_apply, Scheme.Pic.ofIsInvertible,
      Scheme.Pic.etaleTorsorClass_mk]
    exact hp
  have hs : (Sheaf.H.equiv₀ _ terminal).symm s = Ext.mk₀ (supportedIntegralUnit i) :=
    integral_section T _ (supportedIntegralUnit i)
  rw [Sheaf.H.δ_apply, hs] at hpic
  have hchern : supportedKummerChern A N hA i hI hT =
      ((Ext.mk₀ (supportedIntegralUnit i)).comp
        (hE.extClass.comp (T.kummerSequence_shortExact N hT).extClass
          (rfl : 1 + 1 = 2)) (zero_add 2)).comp
        (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 2) := by
    unfold supportedKummerChern
    rw [hpic]
    change Sheaf.H.map _ 2
      (((Ext.mk₀ (supportedIntegralUnit i)).comp hE.extClass (zero_add 1)).comp
        (T.kummerSequence_shortExact N hT).extClass (rfl : 1 + 1 = 2)) = _
    simp only [Sheaf.H.map_apply, Ext.comp_assoc]
  rw [hext]
  simpa only [Ext.comp_assoc] using hchern.symm

end AlgebraicGeometry.Etale
