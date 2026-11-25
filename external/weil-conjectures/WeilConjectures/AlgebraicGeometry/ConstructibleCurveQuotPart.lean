/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.CurveCoefficientPair
/-- Constructibility of the quotient in the six step dévissage argument.
Use the canonical integral-module comparison to transport the short exact sequence.
The curve is Noetherian because it is of finite type over a field. The Noetherian
module subobject theorem makes the first term constructible, and the cokernel
Serre property makes its cokernel constructible. Short exactness identifies this
cokernel with the quotient. Transport across that isomorphism, then apply the
integral comparison to the torsion quotient. Source: Stacks Project, Tag 09BH (2),
with the integral coefficient comparison recorded in the imported library.
(blueprint: lem-weil-pbc-curve-constructible-quot-part) -/
theorem constructible_quot_part {k : Type u} [Field k] [IsAlgClosed k]
    (P : AlgebraicGeometry.CurveCoefficientPair k)
    (F₁ F₂ : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h₁ : P.C.IsTorsionAbelianSheaf F₁) (h₂ : P.C.IsTorsionAbelianSheaf F₂)
    (α : F₁ ⟶ P.F) (β : P.F ⟶ F₂) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) (hF : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F))) :
    (fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
      { P with F := F₂, isTorsion :=
      ((Scheme.isTorsionAbelianSheaf_characterizations _).1.mp h₂) } := by
  have _ := h₁
  let := P.isCurve
  let : IsNoetherian P.C := isNoetherian_of_locallyOfFiniteType P.toSpec
  let : IsNoetherianRing (ULift.{u + 1} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let T := sheafCompose P.C.smallEtaleTopology E
  let : T.EssSurj := ⟨fun G ↦ by
    refine ⟨(sheafCompose P.C.smallEtaleTopology E.inv).obj G, ⟨?_⟩⟩
    exact ObjectProperty.isoMk _
      ((Functor.associator G.obj E.inv E) ≪≫
        Functor.isoWhiskerLeft G.obj E.asEquivalence.counitIso ≪≫ Functor.rightUnitor G.obj)⟩
  let : T.IsEquivalence := {}
  let : T.Additive := Functor.additive_of_preserves_binary_products T
  have hT := hS.map_of_exact T
  let : Scheme.IsConstructibleSheaf (T.obj P.F) :=
    (Scheme.isConstructibleSheaf_integral_iff P.F 
      ((Scheme.isTorsionAbelianSheaf_characterizations
        P.F).1.mpr P.isTorsion)).mpr hF
  let : Mono (T.map α) := hT.mono_f
  let : Scheme.IsConstructibleSheaf (T.obj F₁) :=
    Scheme.constructible_of_mono_noetherian (T.map α)
  let : Scheme.IsConstructibleSheaf (Limits.cokernel (T.map α)) :=
    Scheme.IsConstructibleSheaf.cokernel (T.map α)
  have h₂' : Scheme.IsConstructibleSheaf (T.obj F₂) :=
    Scheme.IsConstructibleSheaf.of_iso (F := Limits.cokernel (T.map α))
      ((Limits.cokernelIsCokernel (T.map α)).coconePointUniqueUpToIso hT.gIsCokernel)
  exact (Scheme.isConstructibleSheaf_integral_iff F₂ h₂).mp h₂'

end AlgebraicGeometry.CurveCoefficientPair
