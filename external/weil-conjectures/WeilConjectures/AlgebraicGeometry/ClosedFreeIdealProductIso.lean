/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import WeilConjectures.AlgebraicGeometry.ClosedStructureIdealProductIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed

/-! # Closed finite free ideal-product comparison

Source: Stacks Project, Tag 01QY, the affine quotient description of closed pushforward.
(blueprint: lem-pc-g1-closed-free-ideal-product-iso)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
-- Coproduct and tensor comparison elaboration requires additional heartbeats.
/-- An ambient ideal times a closed finite free source is the pushforward of the
finite sum of its extended ideal, compatibly with the inclusions.
Source: Stacks Project, Tag 01QY, affine quotient calculation, applied coordinatewise.
(blueprint: lem-pc-g1-closed-free-ideal-product-iso)

Proof: On an affine V = Spec A of X the closed inverse image is Spec B, with
B = A/L. Write J = K(V). The extended ideal has sections J B = image(J -> B).
The finite free source has sections B^r; multiplication J tensor_A B^r -> B^r
has image (J B)^r, with coordinatewise inclusion. Thus both displayed sources,
with their monic arrows into the same closed free module, are the same subobject
on every affine open. The identifications commute with localization, because
extension of ideals and finite sums commute with localization. Their unique local
lifts through the monic inclusions consequently agree on overlaps and glue to
inverse global morphisms. Their composite with the ambient product inclusion is
exactly the pushforward of the coordinate inclusions. This proves the equation
as well as the isomorphism. Alternatively distribute the ambient ideal product
and the closed pushforward over the finite sum, then apply the rank-one closed
structure ideal-product isomorphism to every coordinate. No Noetherianity, open,
target, or local morphism is used. For r = 0 both sources are zero; for the zero
ideal both products are zero; for the unit ideal both inclusions are invertible.
The empty closed subscheme gives zero sources as well. -/
theorem closed_free_ideal_product_iso
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (K : X.IdealSheafData) (r : ℕ) :
    ∃ e : (pushforward i).obj (∐ fun _ : Fin r ↦ (K.comap i).toModules) ≅
        idealModuleProduct K.toModulesι
          ((pushforward i).obj (∐ fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf)),
      e.hom ≫ idealModuleProductι K.toModulesι
          ((pushforward i).obj (∐ fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf)) =
        (pushforward i).map (Sigma.desc (fun j : Fin r ↦ (K.comap i).toModulesι ≫
          Sigma.ι (fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) j)) := by
  classical
  let inst : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft K.toModules) :=
    (SheafOfModules.tensorHomAdjunction X.sheaf K.toModules).leftAdjoint_preservesColimits
  let B := (pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let Q := (pushforward i).obj (K.comap i).toModules
  let H := (pushforward i).obj (∐ fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf)
  let μB := K.toModulesι ▷ B ≫ (λ_ B).hom
  let μH := K.toModulesι ▷ H ≫ (λ_ H).hom
  obtain ⟨e, he⟩ := closed_structure_ideal_product_iso i K
  let pB : (∐ fun _ : Fin r ↦ B) ≅ H :=
    (PreservesCoproduct.iso (pushforward i)
      (fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf)).symm
  let pQ : (∐ fun _ : Fin r ↦ Q) ≅
      (pushforward i).obj (∐ fun _ : Fin r ↦ (K.comap i).toModules) :=
    (PreservesCoproduct.iso (pushforward i) (fun _ : Fin r ↦ (K.comap i).toModules)).symm
  let t : K.toModules ⊗ H ≅ (∐ fun _ : Fin r ↦ K.toModules ⊗ B) :=
    (tensorLeft K.toModules).mapIso pB.symm ≪≫
      PreservesCoproduct.iso (tensorLeft K.toModules) (fun _ : Fin r ↦ B)
  let j := (pushforward i).map (Sigma.desc (fun k : Fin r ↦ (K.comap i).toModulesι ≫
    Sigma.ι (fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) k))
  let c : K.toModules ⊗ B ⟶ Q := factorThruImage μB ≫ e.inv
  have hc : c ≫ (pushforward i).map (K.comap i).toModulesι = μB := by
    dsimp only [c]
    rw [← he]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, idealModuleProductι] using image.fac μB
  let q : K.toModules ⊗ H ⟶
      (pushforward i).obj (∐ fun _ : Fin r ↦ (K.comap i).toModules) :=
    t.hom ≫ CategoryTheory.Limits.Sigma.map (fun _ : Fin r ↦ c) ≫ pQ.hom
  have : Epi c := by dsimp [c]; infer_instance
  have : Epi q := by dsimp [q]; infer_instance
  have : Mono j := by
    have : HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts
    change Mono ((pushforward i).map
      (CategoryTheory.Limits.Sigma.map (fun _ : Fin r ↦ (K.comap i).toModulesι)))
    have : Mono (CategoryTheory.Limits.Sigma.map
        (fun _ : Fin r ↦ (K.comap i).toModulesι)) :=
      CategoryTheory.Limits.Sigma.map_mono _
    exact Functor.map_mono _ _
  have : StrongEpi q := strongEpi_of_epi q
  have hq : q ≫ j = μH := by
    apply (cancel_epi t.inv).1
    dsimp only [q]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [t, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv,
      PreservesCoproduct.inv_hom, pB, pQ]
    apply Sigma.hom_ext
    intro k
    simp only [Category.assoc, Sigma.ι_map_assoc]
    change c ≫ Sigma.ι (fun _ : Fin r ↦ Q) k ≫
      sigmaComparison (pushforward i) (fun _ : Fin r ↦ (K.comap i).toModules) ≫ j = _
    rw [ι_comp_sigmaComparison_assoc]
    change c ≫ (pushforward i).map
      (Sigma.ι (fun _ : Fin r ↦ (K.comap i).toModules) k) ≫ j =
      Sigma.ι (fun _ : Fin r ↦ (tensorLeft K.toModules).obj B) k ≫
        sigmaComparison (tensorLeft K.toModules) (fun _ : Fin r ↦ B) ≫
          (tensorLeft K.toModules).map pB.hom ≫ μH
    rw [ι_comp_sigmaComparison_assoc]
    dsimp only [j]
    rw [← Functor.map_comp, Sigma.ι_comp_desc, Functor.map_comp, ← Category.assoc, hc]
    change μB ≫ (pushforward i).map
      (Sigma.ι (fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) k) =
      (K.toModules ◁ Sigma.ι (fun _ : Fin r ↦ B) k) ≫
        (K.toModules ◁ sigmaComparison (pushforward i)
          (fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf)) ≫ μH
    rw [← whiskerLeft_comp_assoc, ι_comp_sigmaComparison]
    dsimp only [μB, μH]
    rw [whisker_exchange_assoc]
    have hunitor := @MonoidalCategory.leftUnitor_naturality X.Modules _ inst B H
      ((pushforward i).map
        (Sigma.ι (fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) k))
    change (K.toModulesι ▷ B ≫ (λ_ B).hom) ≫ _ =
      K.toModulesι ▷ B ≫ (𝟙_ X.Modules ◁ _) ≫ (λ_ H).hom
    simpa only [Category.assoc] using
      congrArg (fun f ↦ K.toModulesι ▷ B ≫ f) hunitor.symm
  refine ⟨(image.isoStrongEpiMono q j hq), ?_⟩
  exact image.isoStrongEpiMono_hom_comp_ι q j hq


end AlgebraicGeometry.Scheme.Modules
