/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.FieldTheory.SeparableClosure
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField

/-!
# Automorphisms of stalks and of the function field induced by an automorphism

Let `E` be an automorphism of a scheme `X` fixing a point `x`. It induces an automorphism of the
local ring `𝒪_{X, x}` (`AlgebraicGeometry.Scheme.stalkAut`), compatible with the specialization
maps between fixed points and with `Spec 𝒪_{X, x} ⟶ X`. For an integral scheme the generic point
is fixed, so `E` induces an automorphism `e` of the function field `k(X)`, and this automorphism
extends to every separable closure `Ω` of `k(X)`: there is an automorphism `φ` of `Ω` with
`Spec φ ≫ η̄ = η̄ ≫ E` for the generic geometric point `η̄ : Spec Ω ⟶ X`
(`AlgebraicGeometry.Scheme.exists_ringEquiv_separableClosure`).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace IsSepClosure

/-- An automorphism `e` of a field `F` extends to an automorphism of any separable closure
`Ω` of `F`. -/
theorem exists_ringEquiv_algebraMap {F Ω : Type*} [Field F] [Field Ω] [inst : Algebra F Ω]
    [hΩ : IsSepClosure F Ω] (e : F ≃+* F) :
    ∃ φ : Ω ≃+* Ω, ∀ f, φ (algebraMap F Ω f) = algebraMap F Ω (e f) := by
  have hsc : IsSepClosed Ω := hΩ.sep_closed
  have hsep : Algebra.IsSeparable F Ω := hΩ.separable
  let i' : Algebra F Ω := ((algebraMap F Ω).comp e.toRingHom).toAlgebra
  have hsep' : @Algebra.IsSeparable F Ω _ _ i' :=
    @Algebra.IsSeparable.of_equiv_equiv F Ω F Ω _ _ _ _ inst i' e.symm (RingEquiv.refl Ω)
      (RingHom.ext fun f ↦ congrArg (@algebraMap F Ω _ _ inst) (e.apply_symm_apply f)) hsep
  have hcl : @IsSepClosure F _ Ω _ i' := @IsSepClosure.mk F _ Ω _ i' hsc hsep'
  let φ := @IsSepClosure.equiv F _ Ω Ω _ _ i' hcl inst hΩ
  refine ⟨@AlgEquiv.toRingEquiv F Ω Ω _ _ _ inst i' φ, fun f ↦ ?_⟩
  exact @AlgEquiv.commutes F Ω Ω _ _ _ inst i' φ f

end IsSepClosure

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (E : X ≅ X)

/-- The automorphism of the local ring `𝒪_{X, x}` induced by an automorphism `E` of `X` fixing
`x`. -/
noncomputable def stalkAut {x : X} (hx : E.hom x = x) :
    X.presheaf.stalk x ≅ X.presheaf.stalk x :=
  X.presheaf.stalkCongr (Inseparable.of_eq hx.symm) ≪≫ asIso (E.hom.stalkMap x)

lemma stalkAut_hom {x : X} (hx : E.hom x = x) :
    (stalkAut E hx).hom = X.presheaf.stalkSpecializes (Inseparable.of_eq hx.symm).ge ≫
      E.hom.stalkMap x :=
  rfl

/-- The automorphisms of the stalks at two fixed points `y ⤳ x` are compatible with the
specialization map. -/
@[reassoc]
lemma stalkAut_hom_stalkSpecializes {x y : X} (hx : E.hom x = x) (hy : E.hom y = y) (h : y ⤳ x) :
    (stalkAut E hx).hom ≫ X.presheaf.stalkSpecializes h =
      X.presheaf.stalkSpecializes h ≫ (stalkAut E hy).hom := by
  rw [stalkAut_hom, stalkAut_hom, Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap,
    TopCat.Presheaf.stalkSpecializes_comp_assoc, TopCat.Presheaf.stalkSpecializes_comp_assoc]

@[reassoc]
lemma SpecMap_stalkAut_hom_fromSpecStalk {x : X} (hx : E.hom x = x) :
    Spec.map (stalkAut E hx).hom ≫ X.fromSpecStalk x = X.fromSpecStalk x ≫ E.hom := by
  rw [stalkAut_hom, Spec.map_comp, Category.assoc, SpecMap_stalkSpecializes_fromSpecStalk,
    SpecMap_stalkMap_fromSpecStalk]

/-- The automorphism of the stalk acts on germs of global sections through `E`. -/
lemma germ_stalkAut_hom {x : X} (hx : E.hom x = x) :
    X.presheaf.germ ⊤ x trivial ≫ (stalkAut E hx).hom =
      E.hom.appTop ≫ X.presheaf.germ ⊤ x trivial := by
  rw [stalkAut_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  rfl

section Integral

variable [IrreducibleSpace X]

lemma hom_genericPoint : E.hom (genericPoint X) = genericPoint X := by
  have h := (genericPoint_spec X).image (E.hom.continuous)
  rw [Set.image_univ, E.hom.surjective.range_eq, closure_univ] at h
  exact h.eq (genericPoint_spec X)

/-- The automorphism of the function field induced by an automorphism of an irreducible
scheme. -/
noncomputable def functionFieldAut : X.functionField ≅ X.functionField :=
  stalkAut E (hom_genericPoint E)

@[reassoc]
lemma SpecMap_functionFieldAut_hom_fromSpecFunctionField :
    Spec.map (functionFieldAut E).hom ≫ X.fromSpecFunctionField =
      X.fromSpecFunctionField ≫ E.hom :=
  SpecMap_stalkAut_hom_fromSpecStalk E _

/-- The automorphism of a stalk at a fixed point is compatible with that of the function
field. -/
lemma functionFieldAut_algebraMap {x : X} (hx : E.hom x = x) (o : X.presheaf.stalk x) :
    (functionFieldAut E).hom (algebraMap _ X.functionField o) =
      algebraMap _ X.functionField ((stalkAut E hx).hom o) := by
  have := stalkAut_hom_stalkSpecializes E hx (hom_genericPoint E)
    ((genericPoint_spec X).specializes trivial)
  exact (ConcreteCategory.congr_hom this o).symm

/-- The automorphism of the function field acts on germs of global sections through `E`. -/
lemma functionFieldAut_germ (f : Γ(X, ⊤)) :
    (functionFieldAut E).hom (X.presheaf.germ ⊤ (genericPoint X) trivial f) =
      X.presheaf.germ ⊤ (genericPoint X) trivial (E.hom.appTop f) :=
  ConcreteCategory.congr_hom (germ_stalkAut_hom E (hom_genericPoint E)) f

end Integral

variable [IsIntegral X]

/-- **Lifting an automorphism to the separable closure of the function field.** An automorphism
`E` of an integral scheme `X` lifts to an automorphism `φ` of a separable closure `Ω` of the
function field: `φ` restricts to the automorphism of `k(X)` induced by `E`, and
`Spec φ ≫ η̄ = η̄ ≫ E` for the generic geometric point `η̄ : Spec Ω ⟶ X`. -/
theorem exists_ringEquiv_separableClosure (Ω : Type u) [Field Ω] [Algebra X.functionField Ω]
    [IsSepClosure X.functionField Ω] :
    ∃ φ : Ω ≃+* Ω, (∀ f, φ (algebraMap X.functionField Ω f) =
        algebraMap X.functionField Ω ((functionFieldAut E).hom f)) ∧
      Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫ X.fromSpecFunctionField =
        Spec.map (CommRingCat.ofHom (algebraMap X.functionField Ω)) ≫
          X.fromSpecFunctionField ≫ E.hom := by
  obtain ⟨φ, hφ⟩ := IsSepClosure.exists_ringEquiv_algebraMap (Ω := Ω)
    (functionFieldAut E).commRingCatIsoToRingEquiv
  refine ⟨φ, hφ, ?_⟩
  rw [← SpecMap_functionFieldAut_hom_fromSpecFunctionField, ← Category.assoc, ← Spec.map_comp,
    ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext f
  exact hφ f

end AlgebraicGeometry.Scheme
