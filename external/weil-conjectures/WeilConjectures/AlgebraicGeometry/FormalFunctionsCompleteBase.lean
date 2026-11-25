/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.FiniteFreeComplex


public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.TheoremFormalFunctions
import WeilConjectures.RingTheory.FiniteModuleComplete
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-!
# Theorem on formal functions over a complete Noetherian base ring

Source: Stacks Project, Cohomology of Schemes, Lemma 087U
(blueprint: lem-weil-pbc-formal-functions-complete-base).

The index n represents the positive level n+1. H^p and Γ are A-modules by restriction of
scalars along (ΓSpecIso A).inv ≫ f.appTop, as in lem-weil-pbc-theorem-formal-functions.
The isomorphism is specified on every limit projection, so it is the canonical map.
The degree-zero assertion uses actual global sections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry

private theorem finite_moduleCohomology
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : CoherentModules X) (p : ℕ) :
    Module.Finite A ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F.obj) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : F.obj.IsFinitePresentation := by
    have hq :=
      (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F.obj).mp F.property
    have : F.obj.IsQuasicoherent := hq.1
    have hs := (Scheme.Modules.isCoherent_pushforward_of_isFinite (𝟙 X) F.obj F.property).2
    have (U : X.affineOpens) : (F.obj.over U.1).IsFinitePresentation := by
      have : IsNoetherianRing Γ(X, U.1) :=
        IsLocallyNoetherian.component_noetherian U
      have : Module.Finite Γ(X, U.1) Γ(F.obj, U.1) := hs U.1 U.2 |>.2
      exact (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2
      F.obj inferInstance).1
        U.1 U.2).2.mpr (Module.finitePresentation_of_finite Γ(X, U.1) Γ(F.obj, U.1))
    exact SheafOfModules.IsFinitePresentation.of_coversTop F.obj (fun U : X.affineOpens ↦ U.1)
      ((Opens.coversTop_iff X _).mpr
        (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X)))
  have : IsNoetherianRing Γ(Spec (CommRingCat.of A), ⊤) :=
    isNoetherianRing_of_ringEquiv _
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have := Scheme.Modules.finite_sections_higherDirectImage f F.obj p
  obtain ⟨b, hb⟩ :=
    Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H f F.obj p
  let R := Γ(Spec (CommRingCat.of A), ⊤)
  let H := (RingedSpace.moduleCohomology X.toRingedSpace p).obj F.obj
  let : Module R H := Module.compHom H f.appTop.hom
  obtain ⟨a, ha⟩ := Scheme.Modules.exists_moduleCohomology_source_comparison X p
  let : Module R (F.obj.H p) := Module.compHom _ f.appTop.hom
  let aR : H ≃ₗ[R] F.obj.H p :=
    { a F.obj with
      map_smul' := fun r x ↦ by
        have hn := ha F.obj F.obj (F.obj.smulHom (f.appTop r)) x
        have hm := moduleCohomology_scalar_endomorphism F.obj
          (F.obj.smulHom (f.appTop r)) (f.appTop r)
          (fun U t ↦ Scheme.Modules.smulHom_app_apply F.obj (f.appTop r) U t) p x
        rw [hm] at hn
        exact hn }
  let bR : Γ((Scheme.Modules.higherDirectImage f p).obj F.obj, ⊤) →ₗ[R] F.obj.H p :=
    { b.toAddMonoidHom with map_smul' := fun r x ↦ b.map_smulₛₗ r x }
  have : Module.Finite R (F.obj.H p) := Module.Finite.of_surjective bR hb.2
  have : Module.Finite R H := Module.Finite.equiv aR.symm
  let C := (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F.obj
  let c : C →ₛₗ[(Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom] H :=
    { toFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let : RingHomSurjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective⟩
  exact (c.finite_iff_of_bijective Function.bijective_id).mpr inferInstance

/-- For a proper scheme over a complete Noetherian base, coherent cohomology is the
inverse limit of the cohomology of the infinitesimal quotients, as A-modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 087U
(blueprint: lem-weil-pbc-formal-functions-complete-base).

Proof: By lem-pc-coherent-hi (Lemma 02O6), the cohomology module H is finite over A.
By lem-weil-pbc-finite-module-complete-over-complete-noetherian (Algebra, Lemma 00MA),
the completion map c : H → H^ is bijective. By lem-weil-pbc-theorem-formal-functions
(Theorem 02OC), the map θ identifies the
resulting completion with the inverse limit of the cohomology of the quotients;
the map in the statement is the composite of these two canonical isomorphisms:
its nth projection sends x to the image of x under the quotient-induced map,
since the formal-functions map sends x modulo I^(n+1) to that same image.
Thus the composite has the displayed projections and is an isomorphism.
-/
theorem formalFunctions_complete_base
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : CoherentModules X) (p : ℕ) :
    ∃ e : (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F.obj ≅
      limit (formalCompletionSystem
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
        (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
      ∀ n : ℕ, e.hom ≫ limit.π (formalCompletionSystem
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
          (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
            ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
        (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
            (n + 1) F.obj) := by
  let C := RingedSpace.moduleCohomology X.toRingedSpace p ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let H := C.obj F.obj
  let : Module.Finite A H := finite_moduleCohomology f F p
  let : IsAdicComplete I H :=
    finite_module_complete_over_complete_noetherian A I H
  obtain ⟨θ, hθ, _, e, he⟩ := theorem_formal_functions I f J rfl F.obj F.property p
  let c : H ≅ ModuleCat.of A (AdicCompletion I H) :=
    (AdicCompletion.ofLinearEquiv I H).toModuleIso
  refine ⟨c ≪≫ e, ?_⟩
  intro n
  dsimp only [Iso.trans_hom]
  rw [Category.assoc, he]
  apply ModuleCat.hom_ext
  ext x
  change θ n (AdicCompletion.eval I H (n + 1)
    ((AdicCompletion.ofLinearEquiv I H) x)) = _
  rw [AdicCompletion.ofLinearEquiv_apply, AdicCompletion.eval_of]
  exact LinearMap.congr_fun (hθ n) x

/-- The degree-zero case: global sections are the inverse limit of the global sections of
the infinitesimal quotients, as A-modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 087U, p = 0
(blueprint: lem-weil-pbc-formal-functions-complete-base).

Proof: H^0 is global sections (the zeroth right derived functor of the left-exact
global-sections functor), naturally in the module; transport formalFunctions_complete_base
at p = 0 along this natural isomorphism, which carries the quotient-induced maps to the
quotient-induced maps on global sections.
-/
theorem globalSections_formalFunctions_complete_base
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (F : CoherentModules X) :
    ∃ e : (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
        ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F.obj ≅
      limit (formalCompletionSystem
        ((Scheme.IdealSheafData.ofIdealTop
          (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
        (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
      ∀ n : ℕ, e.hom ≫ limit.π (formalCompletionSystem
          ((Scheme.IdealSheafData.ofIdealTop
            (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f) F.obj ⋙
          (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
            ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
        (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ
            ((Scheme.IdealSheafData.ofIdealTop
              (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
            (n + 1) F.obj) := by
  let R := ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let C := RingedSpace.moduleCohomology X.toRingedSpace 0 ⋙ R
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ R
  let J := (Scheme.IdealSheafData.ofIdealTop
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f
  let : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  let α : C ≅ G := Functor.isoWhiskerRight
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedZeroIsoSelf R
  obtain ⟨e₀, he₀⟩ := formalFunctions_complete_base I f F 0
  let w := Functor.isoWhiskerLeft (formalCompletionSystem J F.obj) α
  let e := (α.app F.obj).symm ≪≫ e₀ ≪≫ HasLimit.isoOfNatIso w
  refine ⟨e, ?_⟩
  intro n
  change e.hom ≫ limit.π (formalCompletionSystem J F.obj ⋙ G) (op n) =
    G.map (formalModuleQuotientπ J (n + 1) F.obj)
  dsimp only [e, Iso.trans_hom]
  simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc e₀.hom, he₀]
  change (α.app F.obj).inv ≫
    (C.map (formalModuleQuotientπ J (n + 1) F.obj) ≫
      α.hom.app (formalModuleQuotient J (n + 1) F.obj)) = _
  rw [α.hom.naturality]
  simp

end AlgebraicGeometry
