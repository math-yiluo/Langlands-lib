/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusElement
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction

/-!
# Frobenius elements along an open immersion

Let `j : U ⟶ C` be an open immersion and `x` a point of `U` with finite residue field. The map
`π₁(U, s) → π₁(C, t)` induced by `j` and a path `τ : F_s ∘ j^* ≅ F_t` carries Frobenius
elements at `x` to Frobenius elements at `j x`
(`AlgebraicGeometry.Scheme.FiniteEtale.IsFrobeniusElement.fundamentalGroupMap`).

The geometric points `x̄ ≫ j` and `(j x)‾` differ by the isomorphism `κ(j x) ≅ κ(x)` extended
to the algebraic closures, which commutes with the arithmetic Frobenius maps since both residue
fields have the same number of elements.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsSepClosed Ω₁] [Field Ω₂] [IsSepClosed Ω₂]

/-- An isomorphism `e : Spec Ω₁ ≅ Spec Ω₂` with `e ≫ t₂ = t₁` induces, by precomposition, an
isomorphism of the fibre functors at `t₂` and `t₁`. -/
noncomputable def fiberIsoOfIso {t₁ : Spec (.of Ω₁) ⟶ Y} {t₂ : Spec (.of Ω₂) ⟶ Y}
    (e : Spec (.of Ω₁) ≅ Spec (.of Ω₂)) (he : e.hom ≫ t₂ = t₁) : fiber t₂ ≅ fiber t₁ :=
  NatIso.ofComponents
    (fun P ↦ FintypeCat.equivEquivIso
      { toFun y := fiberMk t₁ P (e.hom ≫ y.left) (by
          rw [Category.assoc]
          change e.hom ≫ (y.left ≫ P.obj.hom) = t₁
          rw [fiber_left_comp, he])
        invFun y := fiberMk t₂ P (e.inv ≫ y.left) (by
          rw [Category.assoc]
          change e.inv ≫ (y.left ≫ P.obj.hom) = t₂
          rw [fiber_left_comp, ← he, e.inv_hom_id_assoc])
        left_inv y := fiber_ext _ (by simp)
        right_inv y := fiber_ext _ (by simp) })
    (by
      intro P Q φ
      ext y
      apply fiber_ext
      change (e.hom ≫ y.left ≫ φ.hom.left) = (e.hom ≫ y.left) ≫ φ.hom.left
      rw [Category.assoc])

lemma fiberIsoOfIso_hom_app_left {t₁ : Spec (.of Ω₁) ⟶ Y} {t₂ : Spec (.of Ω₂) ⟶ Y}
    (e : Spec (.of Ω₁) ≅ Spec (.of Ω₂)) (he : e.hom ≫ t₂ = t₁) (P : Y.FiniteEtale)
    (y : (fiber t₂).obj P) : ((fiberIsoOfIso e he).hom.app P y).left = e.hom ≫ y.left :=
  rfl

lemma specMapIso_hom {Ω : Type u} [CommRing Ω] (σ : Ω ≃+* Ω) :
    (specMapIso σ).hom = Spec.map (CommRingCat.ofHom σ.toRingHom) :=
  rfl

section OpenImmersion

variable {U C : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] (x : U)

/-- The residue fields at `x` and `j x` are isomorphic. -/
noncomputable def residueFieldEquiv : C.residueField (j x) ≃+* U.residueField x :=
  (asIso (j.residueFieldMap x)).commRingCatIsoToRingEquiv

/-- The isomorphism of the algebraic closures of the residue fields at `j x` and `x`. -/
noncomputable def algebraicClosureEquiv :
    AlgebraicClosure (C.residueField (j x)) ≃+* AlgebraicClosure (U.residueField x) :=
  IsAlgClosure.equivOfEquiv _ _ (residueFieldEquiv j x)

lemma spec_map_algebraicClosureEquiv_comp :
    Spec.map (CommRingCat.ofHom (algebraicClosureEquiv j x).toRingHom) ≫
        residueFieldPoint C (j x) = residueFieldPoint U x ≫ j := by
  rw [residueFieldPoint_eq, residueFieldPoint_eq, Category.assoc,
    ← Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext a
  exact IsAlgClosure.equivOfEquiv_algebraMap _ _ (residueFieldEquiv j x) a

/-- The path `(j x)‾ → x̄ ≫ j` between the geometric points over `j x`. -/
noncomputable def residueFieldPointFiberIso :
    fiber (residueFieldPoint C (j x)) ≅ fiber (residueFieldPoint U x ≫ j) :=
  fiberIsoOfIso (Scheme.Spec.mapIso (algebraicClosureEquiv j x).toCommRingCatIso.op)
    (spec_map_algebraicClosureEquiv_comp j x)


lemma natCard_residueField_eq : Nat.card (C.residueField (j x)) = Nat.card (U.residueField x) :=
  Nat.card_congr (residueFieldEquiv j x).toEquiv

/-- The isomorphism of algebraic closures commutes with the inverse arithmetic Frobenius maps. -/
lemma algebraicClosureEquiv_arithmeticFrobeniusAt_symm [Finite (U.residueField x)]
    [Finite (C.residueField (j x))] (a : AlgebraicClosure (C.residueField (j x))) :
    (arithmeticFrobeniusAt x).symm (algebraicClosureEquiv j x a) =
      algebraicClosureEquiv j x ((arithmeticFrobeniusAt (j x)).symm a) := by
  apply (arithmeticFrobeniusAt x).injective
  rw [AlgEquiv.apply_symm_apply, arithmeticFrobeniusAt_apply, ← map_pow,
    ← natCard_residueField_eq j x, ← arithmeticFrobeniusAt_apply, AlgEquiv.apply_symm_apply]

omit [IsOpenImmersion j] in
lemma pullbackFiberIso_hom_app_fiberPrecompIso {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ U) (e : Spec (.of Ω) ≅ Spec (.of Ω)) (he : e.hom ≫ s = s)
    (P : C.FiniteEtale) (v : (fiber s).obj ((pullback j).obj P)) :
    (pullbackFiberIso j s).hom.app P ((fiberPrecompIso s e he).hom.app _ v) =
      (fiberPrecompIso (s ≫ j) e (by rw [← Category.assoc, he])).hom.app P
        ((pullbackFiberIso j s).hom.app P v) := by
  apply fiber_ext
  rw [pullbackFiberIso_hom_app_left, fiberPrecompIso_hom_app_left, fiberPrecompIso_hom_app_left,
    pullbackFiberIso_hom_app_left, Category.assoc]

/-- The path `(j x)‾ → x̄ ≫ j` intertwines the geometric Frobenius at `j x` with that at `x`. -/
lemma geometricFrobeniusAt_residueFieldPointFiberIso [Finite (U.residueField x)]
    [Finite (C.residueField (j x))] (P : C.FiniteEtale)
    (z : (fiber (residueFieldPoint C (j x))).obj P) :
    (pullbackFiberIso j (residueFieldPoint U x)).hom.app P
        ((geometricFrobeniusAt x).hom.app _ ((pullbackFiberIso j (residueFieldPoint U x)).inv.app P
          ((residueFieldPointFiberIso j x).hom.app P z))) =
      (residueFieldPointFiberIso j x).hom.app P ((geometricFrobeniusAt (j x)).hom.app P z) := by
  rw [geometricFrobeniusAt, pullbackFiberIso_hom_app_fiberPrecompIso]
  rw [← ConcreteCategory.comp_apply ((pullbackFiberIso j (residueFieldPoint U x)).inv.app P),
    Iso.inv_hom_id_app]
  apply fiber_ext
  change _ ≫ (Spec.map (CommRingCat.ofHom (algebraicClosureEquiv j x).toRingHom) ≫ z.left) =
    Spec.map (CommRingCat.ofHom (algebraicClosureEquiv j x).toRingHom) ≫ (_ ≫ z.left)
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [specMapIso_hom, specMapIso_hom, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact algebraicClosureEquiv_arithmeticFrobeniusAt_symm j x a

variable {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  {s : Spec (.of Ω) ⟶ U} {t : Spec (.of Ω') ⟶ C} (τ : pullback j ⋙ fiber s ≅ fiber t)
  (GU : Type u) [Group GU] [∀ P, MulAction GU ((fiber s).obj P)] [IsNaturalSMul (fiber s) GU]
  [ConnectedSpace C] (GC : Type u) [Group GC] [TopologicalSpace GC] [IsTopologicalGroup GC]
  [CompactSpace GC] [∀ P, MulAction GC ((fiber t).obj P)] [IsFundamentalGroup (fiber t) GC]

/-- The map of fundamental groups induced by an open immersion carries Frobenius elements at
`x` to Frobenius elements at `j x`. -/
theorem IsFrobeniusElement.fundamentalGroupMap [Finite (U.residueField x)]
    [Finite (C.residueField (j x))] {g : GU} (hg : IsFrobeniusElement s GU x g) :
    IsFrobeniusElement t GC (j x) (fundamentalGroupMap τ GU GC g) := by
  obtain ⟨σ, hσ⟩ := hg
  refine ⟨residueFieldPointFiberIso j x ≪≫ (pullbackFiberIso j (residueFieldPoint U x)).symm ≪≫
    Functor.isoWhiskerLeft (pullback j) σ ≪≫ τ, fun P z ↦ ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [fundamentalGroupMap_smul]
  erw [hσ ((pullback j).obj P)]
  rw [← geometricFrobeniusAt_residueFieldPointFiberIso,
    ← ConcreteCategory.comp_apply ((pullbackFiberIso j (residueFieldPoint U x)).hom.app P),
    Iso.hom_inv_id_app]
  rfl

end OpenImmersion

end AlgebraicGeometry.Scheme.FiniteEtale
