/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.SquareZeroQuotientLocalAction
import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.AlgebraicGeometry.SquareZeroGluedLinearOperators
import WeilConjectures.AlgebraicGeometry.SquareZeroGluedScalarExistsUnique
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroHorseshoeBoundaryLeibniz
import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The algebraic Čech and derivation identities for fixed compatible resolutions.
This is the local algebra step in the proof of the square-zero boundary derivation theorem.
Source: Stacks Project, Cohomology, Lemma 0B8S.
(blueprint: lem-sc-boundary-derivation-square-zero-algebraic-data) -/
theorem boundary_derivation_algebraic_data (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (_hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (_hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0)
    (IA : InjectiveResolution I)
    (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf B))
    (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf C))
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (_hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map i ≫ IB.ι)
    (_hιB : IB.ι ≫ β =
      (CochainComplex.single₀ _).map ((commAlgebraSheafModuleFunctor X.sheaf).map p) ≫ IC.ι)
    (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact) :
    ∃ (σ : ∀ U : X.Opens, C.right.obj.obj (op U) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U)))
      (μ : C.right.obj.obj (op ⊤) →+* End I)
      (ρ : C.right.obj.obj (op ⊤) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
          ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I))
      (δ : C.right.obj.obj (op ⊤) →+
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I)),
      (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        @id (B.right.obj.obj (op U)) (i.val.app (op U) (σ U (p.right.hom.app (op U) b) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) ∧
      (∀ (U V : X.Opens) (j : V ⟶ U) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
        I.val.map j.op (σ U f x) = σ V (C.right.obj.map j.op f) (I.val.map j.op x)) ∧
      (∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens) (x : I.val.obj (op U)),
        (μ f).asHom.val.app (op U) x = σ U (C.right.obj.map (homOfLE le_top).op f) x) ∧
      (∀ f : C.right.obj.obj (op ⊤), ρ f =
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map ((μ f)).asHom).hom) ∧
      (∀ f : C.right.obj.obj (op ⊤), δ f =
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
            (commAlgebraSheafModule X.sheaf C) ≫
          (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
          hΓ.δ 0 1 rfl ≫
          (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv).hom
            f)) ∧
      ∀ f g : C.right.obj.obj (op ⊤), δ (f * g) = ρ f (δ g) + ρ g (δ f) := by
  classical
  obtain ⟨σ, hσ, hres⟩ := square_zero_quotient_local_action X B C p I i hw _hS _hsq
  let μ : C.right.obj.obj (op ⊤) →+* End I :=
    { toFun := fun f ↦ End.of
        { val :=
            { app := fun U ↦ ModuleCat.ofHom
                (σ U.unop (C.right.obj.map (homOfLE le_top).op f))
              naturality := by
                intro U V j
                ext x
                change σ V.unop (C.right.obj.map (homOfLE le_top).op f)
                    (I.val.map j x) =
                  I.val.map j (σ U.unop (C.right.obj.map (homOfLE le_top).op f) x)
                have hr := hres U.unop V.unop j.unop
                  (C.right.obj.map (homOfLE le_top).op f) x
                change I.val.map j _ = _ at hr
                rw [hr]
                congr 2
                simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
                rfl } }
      map_one' := by
        apply End.ext
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        ext x
        change σ U.unop (C.right.obj.map (homOfLE le_top).op 1) x = x
        simp
      map_mul' := by
        intro f g
        apply End.ext
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        ext x
        change σ U.unop (C.right.obj.map (homOfLE le_top).op (f * g)) x =
          σ U.unop (C.right.obj.map (homOfLE le_top).op f)
            (σ U.unop (C.right.obj.map (homOfLE le_top).op g) x)
        simp
      map_zero' := by
        apply End.ext
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        ext x
        change σ U.unop (C.right.obj.map (homOfLE le_top).op 0) x = 0
        simp
      map_add' := by
        intro f g
        apply End.ext
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.hom_ext
        ext x
        change σ U.unop (C.right.obj.map (homOfLE le_top).op (f + g)) x =
          σ U.unop (C.right.obj.map (homOfLE le_top).op f) x +
            σ U.unop (C.right.obj.map (homOfLE le_top).op g) x
        simp }
  let : (RingedSpace.moduleCohomology X.toRingedSpace 1).Additive := by
    unfold RingedSpace.moduleCohomology
    infer_instance
  let H := RingedSpace.moduleCohomology X.toRingedSpace 1
  let e : End I →+* End (H.obj I) :=
    { __ := H.mapEnd I
      map_zero' := End.ext (H.map_zero I I)
      map_add' := fun f g ↦ End.ext H.map_add }
  let ρ : C.right.obj.obj (op ⊤) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) (H.obj I) :=
    (ModuleCat.endRingEquiv (H.obj I)).toRingHom.comp (e.comp μ)
  let d :=
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
        (commAlgebraSheafModule X.sheaf C) ≫
      (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
      hΓ.δ 0 1 rfl ≫
      (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv
  let δ : C.right.obj.obj (op ⊤) →+
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I) := d.hom.toAddMonoidHom
  refine ⟨σ, μ, ρ, δ, hσ, hres, ?_, ?_, ?_, ?_⟩
  · intro f U x
    rfl
  · intro f
    rfl
  · intro f
    rfl
  · have hlift : ∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens)
        (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        p.right.hom.app (op U) b = C.right.obj.map (homOfLE le_top).op f →
        @id (B.right.obj.obj (op U)) (i.val.app (op U) ((μ f).asHom.val.app (op U) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x) := by
      intro f U b x hb
      change i.val.app (op U)
          (σ U (C.right.obj.map (homOfLE le_top).op f) x) = _
      rw [← hb]
      exact hσ U b x
    exact square_zero_horseshoe_boundary_leibniz X B C p I i hw _hS _hsq
      IA IB IC α β hαβ _hιA _hιB _hH hΓ μ hlift

end AlgebraicGeometry
