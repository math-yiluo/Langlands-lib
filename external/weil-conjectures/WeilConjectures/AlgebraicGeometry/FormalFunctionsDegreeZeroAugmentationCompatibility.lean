/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.FormalFibreCohomology
import all WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso
import WeilConjectures.AlgebraicGeometry.FormalFunctionsDegreeZeroAugmentedSections
/-! # Degree-zero formal-fibre augmentation compatibility

Source: Stacks Project, Tags 01E4 and 01FB, with formal-fibre notation from Tag 02OD.
The component and transition calculations use the canonical construction already
proved in FormalFunctionsDegreeZeroSystemIso, imported with `import all` to use
its private canonical components and transition theorem.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-augmentation-compatibility).
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

/-- The fibre-system identification intertwines theta with section pullback on
classes obtained from the fixed degree-zero direct-image augmentation.
Source: Stacks Project, Tags 01E4 and 01FB (degree zero), and Tag 02OD for the
formal-fibre notation. No formal-functions completion theorem is used.
(blueprint: lem-weil-pbc-formal-functions-degree-zero-augmentation-compatibility).

Proof: At each n compose the inverse of the global-sections degree-zero
augmentation with global sections of tensorPullbackObjUnitToUnit. Both maps are
isomorphisms; restrict their scalars to the completed local ring. The augmentation
square for moduleCohomologyFMap and the tensor-unit equation show that these
component isomorphisms commute with the transition morphisms. They therefore
form an inverse-system isomorphism b. Fix n, theta, V, hy, hV and t. In the
restricted injective resolution take xi to be the global-sections augmentation
of t. The resolutionSectionClass construction followed by isoRightDerivedObj.inv
sends xi to the direct-image augmentation of t on V: both are the class of the
resolution's zeroth augmentation of t. Naturality of germs identifies its germ
with the displayed stalk-map image. Apply IsFormalFunctionsTheta to xi. By the
augmentation square, the right-hand cohomology map corresponds under b to
section pullback of t. The containment hV says the inverse-image open is top;
hence the left restriction is the identity after transport along that equality.
Cancelling it gives the formula. This argument also covers empty fibres (all
sections and cohomology are zero) and t = 0, and requires no properness. -/
theorem formalFunctions_degreeZero_augmentation_compatibility {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y,
        ∀ (n : ℕ)
          (θ : formalFunctionsStalk f y (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[
            Y.presheaf.stalk y]
            formalFibreCohomologyLocal f y (SheafOfModules.unit X.ringCatSheaf) 0 n),
          IsFormalFunctionsTheta f y (SheafOfModules.unit X.ringCatSheaf) 0 n θ →
          ∀ (V : Y.Opens) (hy : y ∈ V)
            (hV : (⊤ : (formalFibre f y n).Opens) ≤
              (formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)) (t : Γ(X, f ⁻¹ᵁ V)),
            (b.hom.app (op n)) (θ (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map
              ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app
                (SheafOfModules.unit X.ringCatSheaf))).hom (TopCat.Presheaf.germ
              ((Scheme.Modules.pushforward f).obj
                (SheafOfModules.unit X.ringCatSheaf)).val.presheaf V y hy t))) =
              (formalFibreι f y n).appLE (f ⁻¹ᵁ V) ⊤ hV t := by
  let b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ⟶
      formalFibreSectionsSystem f y :=
    NatTrans.ofOpSequence (fun n ↦ (levelIso f y n).hom) (by
      intro n
      simpa only [formalFibreCohomologySystem, formalFibreSectionsSystem,
        Functor.ofOpSequence_map_homOfLE_succ] using levelIso_naturality f y n)
  have : ∀ n, IsIso (b.app n) := by
    intro n
    change IsIso (levelIso f y n.unop).hom
    infer_instance
  have : IsIso b := NatIso.isIso_of_isIso_app b
  refine ⟨asIso b, ?_⟩
  intro n θ hθ V hy hV t
  have ht := formalFunctions_degreeZero_augmented_sections f y
    (SheafOfModules.unit X.ringCatSheaf) n θ hθ V hy hV t
  change (levelIso f y n).hom.hom _ = _
  rw [ht]
  let Z := formalFibre f y n
  let F' := (Scheme.Modules.tensorPullback (formalFibreι f y n)).obj
    (SheafOfModules.unit X.ringCatSheaf)
  let S := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  let k := Scheme.Modules.tensorPullbackObjUnitToUnit (formalFibreι f y n)
  let a := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
    (formalFibreι f y n))).unit.app (SheafOfModules.unit X.ringCatSheaf)
  change (S.map k).hom
    ((zeroIso Z F').hom.hom ((S.toRightDerivedZero.app F').hom _)) = _
  have hc : S.toRightDerivedZero.app F' ≫ (zeroIso Z F').hom = 𝟙 _ := by
    exact (zeroIso Z F').inv_hom_id
  have hc' (s : S.obj F') :
      (zeroIso Z F').hom.hom ((S.toRightDerivedZero.app F').hom s) = s :=
    congrArg (fun m ↦ m.hom s) hc
  rw [hc']
  have hs := congrArg (fun φ ↦ (φ.val.app (op (f ⁻¹ᵁ V))).hom t)
    (Scheme.Modules.tensorPullbackObjUnitToUnit_isIso (formalFibreι f y n)).2
  change (k.val.app (op ((formalFibreι f y n) ⁻¹ᵁ (f ⁻¹ᵁ V)))).hom
      ((a.val.app (op (f ⁻¹ᵁ V))).hom t) = (formalFibreι f y n).app (f ⁻¹ᵁ V) t at hs
  change (k.val.app (op ⊤)).hom (F'.val.map (homOfLE hV).op
    ((a.val.app (op (f ⁻¹ᵁ V))).hom t)) = _
  rw [PresheafOfModules.naturality_apply k.val (homOfLE hV).op, hs]
  rfl
end AlgebraicGeometry
