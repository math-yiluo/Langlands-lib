import Langlands.AlgebraicGeometry.Modules.TildePullback
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.Effective

/-! # Ordinary pullback of a specified trivialization -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme.Modules

section General

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (f : Z ⟶ Y) (g : Z ⟶ X)
  (h : g = f ≫ p) {N : X.Modules}

/-- Pull back a specified trivialization along a specified factorization of a morphism. -/
def compositeUnitIso
    (e : (Scheme.Modules.pullback p).obj N ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback g).obj N ≅ SheafOfModules.unit Z.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr h).app N ≪≫
    ((Scheme.Modules.pullbackComp f p).app N).symm ≪≫
      (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f

/-- The transpose of the specified composite on every open and every section. -/
lemma compositeUnitIso_adjoint_app
    (e : (Scheme.Modules.pullback p).obj N ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : X.Opens) (s : Γ(N, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (compositeUnitIso p f g h e).hom).app U s =
    Z.presheaf.map (homOfLE (le_of_eq (by rw [h])) : g ⁻¹ᵁ U ⟶ (f ≫ p) ⁻¹ᵁ U).op
      (f.app (p ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _ e.hom).app U s)) := by
  dsimp only [compositeUnitIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Functor.mapIso_hom]
  rw [Langlands.Scheme.UnitCocycleDescent.homEquiv_pullbackCongr_hom_app,
    Langlands.Scheme.UnitCocycleDescent.homEquiv_pullbackComp_inv_comp_app]

end General

section Affine

variable {R A C : CommRingCat.{u}} (φ : R ⟶ A) (ψ : A ⟶ C)
  (χ : R ⟶ C) (h : φ ≫ ψ = χ) (M : ModuleCat.{u} R)

/-- The ordinary pullback of a specified affine trivialization, with a specified composite. -/
def affineCompositeUnitIso
    (e : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      SheafOfModules.unit (Spec A).ringCatSheaf) :
    (Scheme.Modules.pullback (Spec.map χ)).obj (tilde M) ≅
      SheafOfModules.unit (Spec C).ringCatSheaf :=
  compositeUnitIso (Spec.map φ) (Spec.map ψ) (Spec.map χ)
    (by rw [← h, Spec.map_comp]) e

private lemma affineUnit_toOpen_map (V : (Spec A).Opens) (r : A) :
    (Spec.map ψ).app V (tilde.toOpen (ModuleCat.of A A) V r) =
      tilde.toOpen (ModuleCat.of C C) (Spec.map ψ ⁻¹ᵁ V) (ψ r) :=
  ConcreteCategory.congr_hom (StructureSheaf.toOpen_comp_comap ψ.hom V) r

private lemma affineUnit_toOpen_res (V W : (Spec C).Opens) (i : W ⟶ V) (r : C) :
    (Spec C).presheaf.map i.op (tilde.toOpen (ModuleCat.of C C) V r) =
      tilde.toOpen (ModuleCat.of C C) W r :=
  ConcreteCategory.congr_hom (tilde.toOpen_res (ModuleCat.of C C) V W i) r

/-- A prescribed generator formula pulls back along the actual ring map on every open. -/
lemma affineCompositeUnitIso_adjoint_toOpen
    (e : (Scheme.Modules.pullback (Spec.map φ)).obj (tilde M) ≅
      SheafOfModules.unit (Spec A).ringCatSheaf)
    (q : M → A)
    (he : ∀ (U : (Spec R).Opens) (m : M),
      (tildePullbackAdjoint φ e.hom).app U (tilde.toOpen M U m) =
        tilde.toOpen (ModuleCat.of A A) (Spec.map φ ⁻¹ᵁ U) (q m))
    (U : (Spec R).Opens) (m : M) :
    (tildePullbackAdjoint χ (affineCompositeUnitIso φ ψ χ h M e).hom).app U
        (tilde.toOpen M U m) =
      tilde.toOpen (ModuleCat.of C C) (Spec.map χ ⁻¹ᵁ U) (ψ (q m)) := by
  rw [tildePullbackAdjoint, affineCompositeUnitIso, compositeUnitIso_adjoint_app,
    he, affineUnit_toOpen_map]
  exact affineUnit_toOpen_res _ _ _ (ψ (q m))

end Affine

end Langlands.Scheme.Modules
