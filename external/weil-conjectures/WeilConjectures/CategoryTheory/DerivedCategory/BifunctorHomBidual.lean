/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.BifunctorHomBidual
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The double-dual morphism of a derived hom

Let `H : Cᵒᵖ ⥤ C ⥤ C` be a bifunctor on an abelian category with K-injective resolutions,
`I` a cochain complex, and `G = RHom_H(-, I) : D(C)ᵒᵖ ⥤ D(C)` the derived hom into `I`
(`DerivedCategory.bifunctorRHomOfComplex`), computed on K-injective representatives of the first
variable. Suppose that precomposition with a quasi-isomorphism is a quasi-isomorphism of hom
complexes into `I` (`DerivedCategory.PrecompQuasiIso`), as it is when `I` is K-injective and `H` is
the internal hom of sheaves of modules. Then:

* `G` is computed on every complex `K`, not only on the K-injective ones:
  `G (Q K) ≅ Q (bifunctorHomObj H K I)`, naturally in `K`
  (`DerivedCategory.bifunctorRHomOfComplexQObjIso`);
* given evaluation morphisms `a ⟶ H(H(a, b), b)` (`CochainComplex.BifunctorEvaluation`), the
  double-dual morphisms of hom complexes (`CochainComplex.bifunctorHomBidual`) descend to a natural
  transformation `𝟭 ⟶ G.rightOp ⋙ G` (`DerivedCategory.bifunctorRHomBidual`), whose component at
  `Q K` is an isomorphism if and only if the double-dual morphism of `K` is a quasi-isomorphism
  (`DerivedCategory.isIso_bifunctorRHomBidual_app_Q_obj_iff`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite

universe v u

namespace DerivedCategory

open CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]
  [Abelian.HasKInjectiveResolutions C] [HasCountableProducts C]
  (H : Cᵒᵖ ⥤ C ⥤ C) [H.Additive] [∀ M, (H.obj M).Additive]

namespace BifunctorRHomOfComplex

set_option quotPrecheck false in
local notation "R" => (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.inverse ⋙
  HomotopyCategory.KInjectives.ι

instance (K : DerivedCategory C) : CochainComplex.IsKInjective (((R).obj K).as) := by
  rw [CochainComplex.isKInjective_iff_rightOrthogonal]
  exact ((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.inverse.obj K).property

/-- The morphism in the homotopy category from a complex `K` to the K-injective representative of
`Q K` chosen by the derived hom. -/
noncomputable def eta (K : CochainComplex C ℤ) :
    (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶ (R).obj (Q.obj K) :=
  (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj K)
    ((R).obj (Q.obj K)).as).surjective
    ((quotientCompQhIso C).hom.app K ≫
      (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.counitIso.inv.app (Q.obj K))
    |>.choose

omit [HasCountableProducts C] in
lemma eta_spec (K : CochainComplex C ℤ) :
    Qh.map (eta K) = (quotientCompQhIso C).hom.app K ≫
      (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.counitIso.inv.app (Q.obj K) :=
  (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient C (.up ℤ)).obj K)
    ((R).obj (Q.obj K)).as).surjective _ |>.choose_spec

omit [HasCountableProducts C] in
lemma eta_naturality {K L : CochainComplex C ℤ} (a : K ⟶ L) :
    (HomotopyCategory.quotient C (.up ℤ)).map a ≫ eta L = eta K ≫ (R).map (Q.map a) := by
  apply (CochainComplex.IsKInjective.Qh_map_bijective _ ((R).obj (Q.obj L)).as).injective
  simp only [Functor.map_comp, eta_spec, Category.assoc]
  rw [quotientCompQhIso_hom_naturality_assoc]
  exact congrArg ((quotientCompQhIso C).hom.app K ≫ ·)
    ((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.counitIso.inv.naturality
      (Q.map a))

/-- The comparison `RHom_H(Q K, I) ⟶ Q (bifunctorHomObj H K I)`, for any complex `K`. -/
noncomputable def comparison (K I : CochainComplex C ℤ) :
    (bifunctorRHomOfComplex H I).obj (op (Q.obj K)) ⟶ Q.obj (bifunctorHomObj H K I) :=
  ((bifunctorHomHomotopyFunctor H I).map (eta K)).unop ≫
    (quotientCompQhIso C).hom.app (bifunctorHomObj H K I)

lemma comparison_naturality {K L : CochainComplex C ℤ} (a : K ⟶ L) (I : CochainComplex C ℤ) :
    (bifunctorRHomOfComplex H I).map (Q.map a).op ≫ comparison H K I =
      comparison H L I ≫ Q.map (bifunctorHomMapLeft (H := H) (Y := I) a) := by
  let F := bifunctorHomHomotopyFunctor H I
  have hh := congrArg (fun f ↦ (F.map f).unop) (eta_naturality a)
  simp only [Functor.map_comp, unop_comp] at hh
  change (F.map ((R).map (Q.map a))).unop ≫ (F.map (eta K)).unop ≫ _ = _
  rw [← Category.assoc, ← hh, Category.assoc, bifunctorHomHomotopyFunctor_map]
  simpa only [comparison, Quiver.Hom.unop_op, Category.assoc] using
    congrArg ((F.map (eta L)).unop ≫ ·)
      (quotientCompQhIso_hom_naturality (bifunctorHomMapLeft (H := H) (Y := I) a))

lemma comparison_kinj (K I : CochainComplex C ℤ) [K.IsKInjective] :
    comparison H K I = (bifunctorRHomOfComplexObjIso H I K).hom := by
  have : eta K = (HomotopyCategory.KInjectives.ι.mapIso
      ((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.inverse.mapIso
        ((quotientCompQhIso C).app K).symm ≪≫
        ((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.unitIso.app
          (HomotopyCategory.KInjectives.mk K)).symm)).inv := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ ((R).obj (Q.obj K)).as).injective
    rw [eta_spec]
    simp only [Functor.mapIso_inv, Iso.trans_inv, Iso.symm_inv]
    change _ = (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.functor.map
      (((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.unitIso.app
          (HomotopyCategory.KInjectives.mk K)).hom ≫
        (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.inverse.map
          ((quotientCompQhIso C).hom.app K))
    rw [Functor.map_comp]
    exact ((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.counitIso.inv.naturality
      ((quotientCompQhIso C).hom.app K)).trans
        (congrArg (· ≫ (HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.functor.map
          ((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.inverse.map
            ((quotientCompQhIso C).hom.app K)))
          ((HomotopyCategory.KInjectives.Qh (C := C)).asEquivalence.counitInv_app_functor
            (HomotopyCategory.KInjectives.mk K)))
  simp only [comparison, this, bifunctorRHomOfComplexObjIso, Iso.trans_hom, Iso.unop_hom,
    Iso.symm_hom, Functor.mapIso_inv]
  rfl

end BifunctorRHomOfComplex

open BifunctorRHomOfComplex

/-- Precomposition with a quasi-isomorphism is a quasi-isomorphism of hom complexes into `I`. -/
def PrecompQuasiIso (I : CochainComplex C ℤ) : Prop :=
  ∀ ⦃K L : CochainComplex C ℤ⦄ (a : K ⟶ L) [QuasiIso a],
    QuasiIso (bifunctorHomMapLeft (H := H) (Y := I) a)

variable {H}

lemma isIso_comparison {I : CochainComplex C ℤ} (hI : PrecompQuasiIso H I)
    (K : CochainComplex C ℤ) : IsIso (comparison H K I) := by
  obtain ⟨J, hJ, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  have := hI a
  have := hJ
  have h := comparison_naturality H a I
  rw [comparison_kinj H J I] at h
  have : IsIso ((bifunctorRHomOfComplex H I).map (Q.map a).op ≫ comparison H K I) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left ((bifunctorRHomOfComplex H I).map (Q.map a).op) _

variable (H) in
/-- On any complex `K`, the derived hom into `I` is the hom complex, provided precomposition with
quasi-isomorphisms is a quasi-isomorphism of hom complexes into `I`. -/
noncomputable def bifunctorRHomOfComplexQObjIso {I : CochainComplex C ℤ}
    (hI : PrecompQuasiIso H I) (K : CochainComplex C ℤ) :
    (bifunctorRHomOfComplex H I).obj (op (Q.obj K)) ≅ Q.obj (bifunctorHomObj H K I) :=
  have := isIso_comparison hI K
  asIso (comparison H K I)

lemma bifunctorRHomOfComplexQObjIso_hom_naturality {I : CochainComplex C ℤ}
    (hI : PrecompQuasiIso H I) {K L : CochainComplex C ℤ} (a : K ⟶ L) :
    (bifunctorRHomOfComplex H I).map (Q.map a).op ≫
        (bifunctorRHomOfComplexQObjIso H hI K).hom =
      (bifunctorRHomOfComplexQObjIso H hI L).hom ≫
        Q.map (bifunctorHomMapLeft (H := H) (Y := I) a) :=
  comparison_naturality H a I

variable (E : BifunctorEvaluation H) {I : CochainComplex C ℤ} (hI : PrecompQuasiIso H I)

/-- The double-dual morphism `Q K ⟶ RHom(RHom(Q K, I), I)` of a complex `K`: the double-dual
morphism of hom complexes, through the identifications of the derived homs with hom complexes. -/
noncomputable def bifunctorRHomBidualAux :
    Q ⟶ Q ⋙ (bifunctorRHomOfComplex H I).rightOp ⋙ bifunctorRHomOfComplex H I where
  app K := Q.map (bifunctorHomBidual E K I) ≫
    (bifunctorRHomOfComplexQObjIso H hI (bifunctorHomObj H K I)).inv ≫
      (bifunctorRHomOfComplex H I).map (bifunctorRHomOfComplexQObjIso H hI K).hom.op
  naturality K L a := by
    have h1 := bifunctorHomBidual_naturality E I a
    have h2 := bifunctorRHomOfComplexQObjIso_hom_naturality hI
      (bifunctorHomMapLeft (H := H) (Y := I) a)
    have h3 := bifunctorRHomOfComplexQObjIso_hom_naturality hI a
    have h2' : Q.map (bifunctorHomMapLeft (H := H) (Y := I)
        (bifunctorHomMapLeft (H := H) (Y := I) a)) ≫
        (bifunctorRHomOfComplexQObjIso H hI (bifunctorHomObj H L I)).inv =
      (bifunctorRHomOfComplexQObjIso H hI (bifunctorHomObj H K I)).inv ≫
        (bifunctorRHomOfComplex H I).map
          (Q.map (bifunctorHomMapLeft (H := H) (Y := I) a)).op :=
      (Iso.comp_inv_eq _).2 (by rw [assoc, h2, Iso.inv_hom_id_assoc])
    simp only [Functor.comp_obj, Functor.rightOp_obj, Functor.comp_map,
      Functor.rightOp_map, assoc]
    rw [← Functor.map_comp_assoc, h1, Functor.map_comp, assoc, reassoc_of% h2',
      ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, h3]

/-- The double-dual natural transformation `𝟭 ⟶ RHom(RHom(-, I), I)` on the derived category. -/
noncomputable def bifunctorRHomBidual :
    𝟭 (DerivedCategory C) ⟶ (bifunctorRHomOfComplex H I).rightOp ⋙ bifunctorRHomOfComplex H I :=
  Localization.liftNatTrans Q (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) Q
    (Q ⋙ (bifunctorRHomOfComplex H I).rightOp ⋙ bifunctorRHomOfComplex H I) _ _
    (bifunctorRHomBidualAux E hI)

lemma bifunctorRHomBidual_app_Q_obj (K : CochainComplex C ℤ) :
    (bifunctorRHomBidual E hI).app (Q.obj K) = (bifunctorRHomBidualAux E hI).app K := by
  simp [bifunctorRHomBidual]

lemma isIso_bifunctorRHomBidual_app_Q_obj_iff (K : CochainComplex C ℤ) :
    IsIso ((bifunctorRHomBidual E hI).app (Q.obj K)) ↔ QuasiIso (bifunctorHomBidual E K I) := by
  rw [bifunctorRHomBidual_app_Q_obj, ← isIso_Q_map_iff_quasiIso]
  dsimp only [bifunctorRHomBidualAux]
  constructor
  · intro h
    exact IsIso.of_isIso_comp_right _
      ((bifunctorRHomOfComplexQObjIso H hI (bifunctorHomObj H K I)).inv ≫
        (bifunctorRHomOfComplex H I).map (bifunctorRHomOfComplexQObjIso H hI K).hom.op)
  · intro h
    infer_instance

end DerivedCategory
