/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor

/-!
# Finite-limit part of flatness after restriction to a slice

Source: Stacks Project, Modules on Sites, Tag 0E8J, Lemma `lemma-restriction-flat`
(auxiliary; not a blueprint node).

This is the finite-limit component of the tensor exactness argument used for restriction
of a flat module sheaf to a slice. The remaining colimit component follows from the
closed monoidal structure, while this component requires transporting the exactness
comparison through extension by zero.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

-- Comparing the two restriction presentations in the naturality square needs extra reduction.
set_option backward.isDefEq.respectTransparency false in
/-- If `F` is flat on a ringed site, tensoring by its restriction to a slice preserves
finite limits. The proof extends a finite-limit diagram by zero, applies finite-limit
preservation of tensoring by `F`, and transports the resulting cone comparison through
the natural extension-by-zero tensor isomorphism and exactness/reflection for the
slice extension.

Proof: extend a finite-limit cone from the slice by the sheafified direct-sum extension.
The extension exactness equivalence identifies exactness and monomorphisms after extension.
Tensor the extended cone with the flat sheaf, then use the natural extension-by-zero tensor
comparison to identify it with the extension of the restricted tensor cone. Reflect the
resulting exactness and monomorphism statements back to the slice.
Source: Stacks Project, Modules on Sites, Tag 0E8J
(auxiliary; not a blueprint node). -/
theorem isFlat_over_preservesFiniteLimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : C) (hF : IsFlat F)
    (m : MonoidalCategory (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))))
    (hm : m = SheafOfModules.monoidalCategory (R.over U)) :
    @PreservesFiniteLimits _ inferInstance _ inferInstance
      (@tensorRight _ _ m (F.over U)) := by
  classical
  subst m
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory (R.over U)
  let FU : SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U)) := F.over U
  let A := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let L := extensionByZeroPresheaf.{u} A U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 A.obj)
  let T := tensorRight F
  let TU : SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U)) ⥤
      SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U)) :=
    tensorRight FU
  have : TU.Additive := by
    dsimp only [TU]
    infer_instance
  have hT : PreservesFiniteLimits T ∧ PreservesFiniteColimits T := hF
  let : PreservesFiniteLimits T := hT.1
  let : PreservesFiniteColimits T := hT.2
  have hL : L.PreservesZeroMorphisms := by
    have : (extensionByZeroPresheaf.{u} A U).PreservesZeroMorphisms := by
      constructor
      intro G H
      ext V s
      change (DirectSum.lmap (R := A.obj.obj V)
        (fun φ : V.unop ⟶ U ↦ ((0 : G ⟶ H).val.app (Opposite.op (Over.mk φ))).hom)) s = 0
      induction s using DirectSum.induction_on with
      | zero => exact map_zero _
      | of φ x =>
        rw [DirectSum.lmap_of]
        change DirectSum.of (fun ψ : V.unop ⟶ U ↦ H.val.obj (Opposite.op (Over.mk ψ)))
          φ (0 : H.val.obj (Opposite.op (Over.mk φ))) = 0
        exact map_zero _
      | add x y hx hy => simp only [map_add, hx, hy, add_zero]
    exact inferInstance
  let := hL
  have he : ∀ S : ShortComplex (SheafOfModules.{u} (A.over U)),
      S.Exact ↔ (S.map L).Exact := by
    intro S
    simpa only [ShortComplex.exact_iff_image_eq_kernel, ShortComplex.map_f,
      ShortComplex.map_g] using
      ringedSliceExtension_exact_iff J R U S
  obtain ⟨e⟩ := ringedSlice_extension_tensor J R U
  let comparison : TU ⋙ L ≅ L ⋙ T := NatIso.ofComponents
    (fun G ↦ L.mapIso (tensorObjIsoSheafification (R := R.over U) G FU) ≪≫
      e.app (G, F) ≪≫ (tensorObjIsoSheafification (R := R) (L.obj G) F).symm)
    (by
      intro G H f
      dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
      have h₁ := congrArg L.map
        (whiskerRight_tensorObjIsoSheafification_hom (R := R.over U) f FU)
      have h₂ := e.hom.naturality (X := (G, F)) (Y := (H, F)) (f, 𝟙 F)
      have h₃ := whiskerRight_tensorObjIsoSheafification_hom (R := R) (L.map f) F
      dsimp only [TU, T, tensorRight, Functor.flip_obj_map, curriedTensor_map_app]
      simp only [Functor.map_comp] at h₁
      simp only [Functor.comp_map, Functor.prod_map, MonoidalCategory.tensor_map,
        CategoryTheory.Functor.map_id] at h₂
      erw [MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_id] at h₂
      -- Paste the three naturality squares, reversing the final comparison isomorphism.
      simpa only [Category.assoc, Iso.app_hom] using
        ((CommSq.mk h₁).vert_comp
          ((CommSq.mk h₂).vert_comp (CommSq.mk h₃).vert_inv)).w)
  have hex : ∀ S : ShortComplex (SheafOfModules.{u} (A.over U)),
      S.Exact → (S.map TU).Exact := by
    intro S hS
    apply (he (S.map TU)).mpr
    have h := ((he S).mp hS).map T
    exact ShortComplex.exact_of_iso (S.mapNatIso comparison).symm h
  have : TU.PreservesHomology := TU.preservesHomology_of_map_exact hex
  exact TU.preservesFiniteLimits_of_preservesHomology

end SheafOfModules
