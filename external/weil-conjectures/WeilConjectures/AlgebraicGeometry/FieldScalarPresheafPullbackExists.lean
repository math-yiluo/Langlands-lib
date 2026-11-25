/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldScalarPresheafRingMap
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback

/-! # Existence of presheaf scalar extension in larger universes

Source: Stacks Project, Sheaves on Spaces, Tag 0096; Mathlib's presheaf pullback construction.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SheafOfModules

section ScalarExtension

variable {A B : Type u} [Ring A] [Ring B] (a : A →+* B)
  (M : ModuleCat.{max u v} A)

/-- Relations presenting extension of scalars for arbitrary, possibly noncommutative rings. -/
private noncomputable def relations : Submodule B (M →₀ B) :=
  Submodule.span B
    (Set.range (fun p : M × M ↦
      Finsupp.single (p.1 + p.2) 1 - Finsupp.single p.1 1 - Finsupp.single p.2 1) ∪
    Set.range (fun p : A × M ↦
      Finsupp.single (p.1 • p.2) 1 - a p.1 • Finsupp.single p.2 1))

private abbrev extended := (M →₀ B) ⧸ relations a M

private noncomputable def generator (m : M) : extended a M :=
  (relations a M).mkQ (Finsupp.single m 1)

private lemma generator_add (m n : M) :
    generator a M (m + n) = generator a M m + generator a M n := by
  have h : Finsupp.single (m + n) 1 - Finsupp.single m 1 - Finsupp.single n 1 ∈
      relations a M := Submodule.subset_span (Or.inl ⟨(m, n), rfl⟩)
  have hh := (Submodule.Quotient.mk_eq_zero (relations a M)).2 h
  change (relations a M).mkQ _ = 0 at hh
  simpa only [map_sub, sub_sub, sub_eq_zero, map_add, generator] using hh

private lemma generator_smul (r : A) (m : M) :
    generator a M (r • m) = a r • generator a M m := by
  have h : Finsupp.single (r • m) 1 - a r • Finsupp.single m 1 ∈
      relations a M := Submodule.subset_span (Or.inr ⟨(r, m), rfl⟩)
  have hh := (Submodule.Quotient.mk_eq_zero (relations a M)).2 h
  change (relations a M).mkQ _ = 0 at hh
  simpa only [map_sub, map_smul, sub_eq_zero, generator] using hh

private noncomputable def extensionLift {N : ModuleCat.{max u v} B}
    (f : M →+ N) (hf : ∀ r m, f (r • m) = a r • f m) : extended a M →ₗ[B] N :=
  (relations a M).liftQ (Finsupp.lift N B M f) (by
    apply Submodule.span_le.mpr
    rintro z (⟨⟨m, n⟩, rfl⟩ | ⟨⟨r, m⟩, rfl⟩)
    · change (Finsupp.lift N B M f)
        (Finsupp.single (m + n) 1 - Finsupp.single m 1 - Finsupp.single n 1) = 0
      rw [map_sub, map_sub]
      simp [Finsupp.lift_apply]
    · change (Finsupp.lift N B M f)
        (Finsupp.single (r • m) 1 - a r • Finsupp.single m 1) = 0
      rw [map_sub, map_smul]
      simp [Finsupp.lift_apply, hf])

private lemma extensionLift_generator {N : ModuleCat.{max u v} B}
    (f : M →+ N) (hf : ∀ r m, f (r • m) = a r • f m) (m : M) :
    extensionLift a M f hf (generator a M m) = f m := by
  simp [extensionLift, generator, Submodule.mkQ_apply,
    Submodule.liftQ_apply, Finsupp.lift_apply]

private lemma extension_hom_ext {N : ModuleCat.{max u v} B}
    {f g : extended a M →ₗ[B] N}
    (h : ∀ m, f (generator a M m) = g (generator a M m)) : f = g := by
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext
  intro m b
  have hs : Finsupp.single m b = b • Finsupp.single m 1 := by simp
  simp only [LinearMap.comp_apply, hs, map_smul]
  exact congrArg (b • ·) (h m)

end ScalarExtension

section PresheafExtension

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Ring k] (X : TopCat.{u})
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (α : k →+* R.obj.obj (op ⊤))

private noncomputable abbrev scalarMap (U : (Opens X)ᵒᵖ) :=
  show k →+* R.obj.obj U from ((fieldScalarPresheafRingMap X R α).app U).hom

private lemma scalarMap_naturality {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (r : k) :
    R.obj.map f (scalarMap X R α U r) = scalarMap X R α V r := by
  exact (RingHom.congr_fun
    (congrArg RingCat.Hom.hom ((fieldScalarPresheafRingMap X R α).naturality f)) r).symm

variable (V : PresheafOfModules.{max u v} ((Functor.const (Opens X)ᵒᵖ).obj (RingCat.of k)))

private noncomputable def extensionGenerator (U : (Opens X)ᵒᵖ) :
    V.obj U →+ extended (scalarMap X R α U) (V.obj U) where
  toFun := generator (scalarMap X R α U) (V.obj U)
  map_zero' := by
    have h := generator_add (scalarMap X R α U) (V.obj U) 0 0
    exact add_left_cancel (show generator _ _ 0 + generator _ _ 0 =
      generator _ _ 0 + 0 by simpa using h.symm)
  map_add' := generator_add _ _

private noncomputable def extensionMap {U W : (Opens X)ᵒᵖ} (f : U ⟶ W) :
    ModuleCat.of (R.obj.obj U) (extended (scalarMap X R α U) (V.obj U)) ⟶
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj W) (extended (scalarMap X R α W) (V.obj W))) :=
  ModuleCat.ofHom (X := ModuleCat.of (R.obj.obj U) (extended (scalarMap X R α U) (V.obj U)))
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj W) (extended (scalarMap X R α W) (V.obj W))))
    (extensionLift (N :=
      (ModuleCat.restrictScalars (R.obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj W) (extended (scalarMap X R α W) (V.obj W))))
      (scalarMap X R α U) (V.obj U)
      ((extensionGenerator X R α V W).comp (V.map f).hom.toAddMonoidHom) (by
        intro r m
        change generator (scalarMap X R α W) (V.obj W) (V.map f (r • m)) =
          R.obj.map f (scalarMap X R α U r) •
            generator (scalarMap X R α W) (V.obj W) (V.map f m)
        rw [V.map_smul]
        change generator (scalarMap X R α W) (V.obj W) (r • V.map f m) = _
        rw [generator_smul, scalarMap_naturality]))

private lemma extensionMap_generator {U W : (Opens X)ᵒᵖ} (f : U ⟶ W) (m : V.obj U) :
    extensionMap X R α V f (generator (scalarMap X R α U) (V.obj U) m) =
      generator (scalarMap X R α W) (V.obj W) (V.map f m) := by
  simp only [extensionMap, ModuleCat.hom_ofHom, extensionLift_generator]
  rfl

/-- The balanced quotient construction, with restriction maps induced on generators. -/
private noncomputable def extensionObj : PresheafOfModules.{max u v} R.obj where
  obj U := ModuleCat.of (R.obj.obj U) (extended (scalarMap X R α U) (V.obj U))
  map f := extensionMap X R α V f
  map_id U := by
    apply ModuleCat.hom_ext
    apply extension_hom_ext (scalarMap X R α U) (V.obj U)
    intro m
    rw [extensionMap_generator]
    change generator _ _ (V.map (𝟙 U) m) = generator _ _ m
    congr 1
    exact ConcreteCategory.congr_hom (V.map_id U) m
  map_comp {U W Z} f g := by
    apply ModuleCat.hom_ext
    apply extension_hom_ext (scalarMap X R α _) (V.obj _)
    intro m
    change extensionMap X R α V (f ≫ g) (generator (scalarMap X R α U) (V.obj U) m) =
      extensionMap X R α V g
        (extensionMap X R α V f (generator (scalarMap X R α U) (V.obj U) m))
    rw [extensionMap_generator, extensionMap_generator, extensionMap_generator]
    rw [V.map_comp_apply]

private noncomputable def extensionUnit :
    V ⟶ (PresheafOfModules.pushforward (fieldScalarPresheafRingMap X R α)).obj
      (extensionObj X R α V) where
  app U := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (scalarMap X R α U)).obj
      ((extensionObj X R α V).obj U))
    { toFun := generator (scalarMap X R α U) (V.obj U)
      map_add' := generator_add _ _
      map_smul' := generator_smul _ _ }
  naturality {U W} f := by
    ext m
    change generator (scalarMap X R α W) (V.obj W) (V.map f m) =
      extensionMap X R α V f (generator (scalarMap X R α U) (V.obj U) m)
    rw [extensionMap_generator]

private noncomputable def extensionDesc (N : PresheafOfModules.{max u v} R.obj)
    (f : V ⟶ (PresheafOfModules.pushforward (fieldScalarPresheafRingMap X R α)).obj N) :
    extensionObj X R α V ⟶ N where
  app U := ModuleCat.ofHom (X := (extensionObj X R α V).obj U)
    (extensionLift (N := N.obj U) (scalarMap X R α U) (V.obj U)
      (f.app U).hom.toAddMonoidHom
      (fun r m ↦ (f.app U).hom.map_smul r m))
  naturality {U W} g := by
    apply ModuleCat.hom_ext
    apply extension_hom_ext (scalarMap X R α U) (V.obj U)
    intro m
    change extensionLift (N := N.obj W) (scalarMap X R α W) (V.obj W)
      (f.app W).hom.toAddMonoidHom (fun r m ↦ (f.app W).hom.map_smul r m)
      (extensionMap X R α V g (generator (scalarMap X R α U) (V.obj U) m)) =
      N.map g (extensionLift (N := N.obj U) (scalarMap X R α U) (V.obj U)
        (f.app U).hom.toAddMonoidHom (fun r m ↦ (f.app U).hom.map_smul r m)
        (generator (scalarMap X R α U) (V.obj U) m))
    rw [extensionMap_generator, extensionLift_generator, extensionLift_generator]
    exact PresheafOfModules.naturality_apply f g m

private lemma extensionDesc_generator (N : PresheafOfModules.{max u v} R.obj)
    (f : V ⟶ (PresheafOfModules.pushforward (fieldScalarPresheafRingMap X R α)).obj N)
    (U : (Opens X)ᵒᵖ) (m : V.obj U) :
    (extensionDesc X R α V N f).app U
      (generator (scalarMap X R α U) (V.obj U) m) = f.app U m := by
  change extensionLift (N := N.obj U) (scalarMap X R α U) (V.obj U)
    (f.app U).hom.toAddMonoidHom (fun r m ↦ (f.app U).hom.map_smul r m)
    (generator (scalarMap X R α U) (V.obj U) m) = _
  exact extensionLift_generator _ _ _ _ m

/-- The universal property is natural in the target presheaf. -/
private noncomputable def extensionHomEquiv (N : PresheafOfModules.{max u v} R.obj) :
    (extensionObj X R α V ⟶ N) ≃
      (V ⟶ (PresheafOfModules.pushforward (fieldScalarPresheafRingMap X R α)).obj N) where
  toFun f := extensionUnit X R α V ≫
    (PresheafOfModules.pushforward (fieldScalarPresheafRingMap X R α)).map f
  invFun f := extensionDesc X R α V N f
  left_inv f := by
    ext U : 1
    apply ModuleCat.hom_ext
    apply extension_hom_ext (scalarMap X R α U) (V.obj U)
    intro m
    change (extensionDesc X R α V N
      (extensionUnit X R α V ≫
        (PresheafOfModules.pushforward (fieldScalarPresheafRingMap X R α)).map f)).app U
      (generator (scalarMap X R α U) (V.obj U) m) = _
    erw [extensionDesc_generator]
    rfl
  right_inv f := by
    ext U m
    change (extensionDesc X R α V N f).app U
      (generator (scalarMap X R α U) (V.obj U) m) = f.app U m
    rw [extensionDesc_generator]

end PresheafExtension

/-- Restriction from R-module presheaves to constant-ring module presheaves has a
left adjoint, also when the modules live in a universe larger than the site.

Source: Stacks Project, Sheaves on Spaces, Tag 0096; Mathlib presheaf pullback construction.
(blueprint: lem-sc-field-scalar-presheaf-pullback-exists).

Proof: for each open U, form R(U) tensor over k with the sections of the input
presheaf. For a possibly noncommutative R(U), the right k-action is
r · c = r α_U(c), and the left R(U)-action is left multiplication. The restriction
maps send r tensor m to r restricted tensor m restricted. The balanced relations
are respected because α is natural. A map out of this presheaf is determined by
its values on 1 tensor m. Conversely a natural k-linear map to scalar restriction
extends uniquely by r tensor m mapping to r times the image of m. These are
inverse natural hom bijections and give the adjunction. Tensor products and
sectionwise quotients stay in Type (max u v), since the rings and the site are
u-small. This proves the existence without a field hypothesis, and includes the
zero ring and empty space. The adjunction determines the extension functor up
to unique natural isomorphism; no arbitrary algebraic object is chosen. -/
theorem fieldScalarPresheafPullback_isRightAdjoint
    {k : Type u} [Ring k] (X : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (α : k →+* R.obj.obj (op ⊤)) :
    (PresheafOfModules.pushforward.{max u v}
      (fieldScalarPresheafRingMap X R α)).IsRightAdjoint := by
  exact (Adjunction.adjunctionOfEquivLeft
    (fun V N ↦ extensionHomEquiv X R α V N)
    (fun V N N' g f ↦ by
      ext U m
      rfl)).isRightAdjoint

end SheafOfModules
