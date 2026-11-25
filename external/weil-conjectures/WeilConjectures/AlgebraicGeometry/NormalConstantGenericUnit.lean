/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ConstantStrictFibreStalkComparison
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.PreservesSheafification

/-!
# Generic-point unit for a constant sheaf on an integrally closed integral scheme

This is the generic-point conjunct of Stacks Project Tag 09Z5, separated from the
normal-constant theorem so that the remaining geometric argument can be proved independently.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Limits Opposite Scheme TensorProduct in
private theorem normal_indEtale_local_domain (A C : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing C] [IsLocalRing C] [Algebra A C]
    [Algebra.IndEtale A C] :
    (IsDomain C ∧ IsIntegrallyClosed C) ∧
      Function.Injective (algebraMap A C) := by
  classical
  obtain ⟨I, hI, hf, P, hP⟩ :=
    Algebra.IndEtale.exists_colimitPresentation (R := A) (S := C)
  let e := P.isColimit.coconePointUniqueUpToIso (colimit.isColimit P.diag)
  let r : C ≃+* ↥(colimit P.diag) :=
    ((forget₂ (CommAlgCat A) CommRingCat).mapIso e).commRingCatIsoToRingEquiv
  let : IsLocalRing ↥(colimit P.diag) := r.isLocalRing
  have hA : ∀ (p : Ideal A) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
    intro p _
    refine ⟨inferInstance, ?_⟩
    exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime p)
      p.primeCompl p.primeCompl_le_nonZeroDivisors
  obtain ⟨⟨hd, hc⟩, hinj⟩ :=
    CommAlgCat.isDomain_isIntegrallyClosed_injective_of_etale_colimit A hA P.diag hP
  let := hd
  let := hc
  refine ⟨⟨MulEquiv.isDomain _ r.toMulEquiv, IsIntegrallyClosed.of_equiv r.symm⟩, ?_⟩
  intro a b hab
  apply hinj
  have hr (x : A) : r (algebraMap A C x) = algebraMap A ↥(colimit P.diag) x :=
    e.hom.hom.commutes x
  simpa only [hr] using congrArg r hab

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Limits Opposite Scheme TensorProduct in
private theorem normal_strict_generic_fibre_chart {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ Y) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    letI : Nonempty (Spec R) := ⟨xR (IsLocalRing.closedPoint Ω)⟩
    letI : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion i
    IsIntegral (pullback ((Spec R).fromSpecStalk (genericPoint (Spec R)) ≫ i)
      (strictLocalizationToBase (xR ≫ i))) := by
  classical
  let : Nonempty (Spec R) := ⟨xR (IsLocalRing.closedPoint Ω)⟩
  let : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion i
  let : IsDomain R := (affine_isIntegral_iff R).1 inferInstance
  have hn : ∀ r : Spec R, IsIntegrallyClosed ((Spec R).presheaf.stalk r) := by
    intro r
    let := hY (i r)
    exact IsIntegrallyClosed.of_equiv
      (asIso (i.stalkMap r)).commRingCatIsoToRingEquiv
  let : Nonempty (⊤ : (Spec R).Opens) := ⟨⟨xR (IsLocalRing.closedPoint Ω), trivial⟩⟩
  let : IsIntegrallyClosed Γ(Spec R, ⊤) :=
    isIntegrallyClosed_of_isIntegrallyClosed_stalk hn ⊤
  let : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv
    (ΓSpecIso R).commRingCatIsoToRingEquiv
  obtain ⟨hc, ρ, hρ, _⟩ := strictHenselization_chart_maximalIdeal R i xR
  let := hc
  let C := strictHenselization (xR ≫ i)
  let : Algebra R C := ρ.hom.toAlgebra
  have hInd : Algebra.IndEtale R C :=
    strictHenselization_indEtale_of_affine_chart (xR ≫ i) R i
      ⟨xR (IsLocalRing.closedPoint Ω), rfl⟩ (Iso.refl _) ρ.hom (by simpa using hρ)
  let := hInd
  obtain ⟨⟨hdom, _⟩, hinj⟩ := normal_indEtale_local_domain R C
  let := hdom
  let K := (Spec R).functionField
  let : Algebra C (K ⊗[R] C) := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
      (K ⊗[R] C) := IsLocalization.tensorRight K (nonZeroDivisors R)
  let := hloc
  have hnon : Algebra.algebraMapSubmonoid C (nonZeroDivisors R) ≤ nonZeroDivisors C :=
    map_le_nonZeroDivisors_of_injective (algebraMap R C) hinj le_rfl
  let : IsDomain (K ⊗[R] C) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hnon
  let f := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let g := Spec.map ρ
  have hi : IsIntegral (pullback f g) :=
    IsIntegral.of_isIso (pullbackSpecIso R K C).inv
  let := hi
  let e : pullback f g ≅ pullback (f ≫ i) (g ≫ i) :=
    (pullbackIsPullbackOfCompMono f g i).conePointUniqueUpToIso
    (pullback.isLimit (f ≫ i) (g ≫ i))
  have hf : f = (Spec R).fromSpecStalk (genericPoint (Spec R)) := by
    rw [Spec.fromSpecStalk_eq']
    rfl
  have he : IsIntegral (pullback (f ≫ i) (g ≫ i)) := IsIntegral.of_isIso e.hom
  change g ≫ i = strictLocalizationToBase (xR ≫ i) at hρ
  simpa only [hf, hρ] using he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Limits Opposite Scheme TensorProduct in
private theorem normal_strict_generic_fibre_integral {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) :
    IsIntegral (pullback (Y.fromSpecStalk (genericPoint Y))
      (strictLocalizationToBase s)) := by
  classical
  obtain ⟨R, i, hi, hs, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) (by trivial)
  let := hi
  have hrange : Set.range s ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint Ω)] using hs
  obtain ⟨xR, hxR⟩ : ∃ xR : Spec (.of Ω) ⟶ Spec R, xR ≫ i = s :=
    ⟨IsOpenImmersion.lift i s hrange, IsOpenImmersion.lift_fac i s hrange⟩
  subst s
  let : Nonempty (Spec R) := ⟨xR (IsLocalRing.closedPoint Ω)⟩
  let : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion i
  let g := strictLocalizationToBase (xR ≫ i)
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R)) ≫ i
  let := normal_strict_generic_fibre_chart hY R i xR
  have hh := Scheme.SpecMap_stalkMap_fromSpecStalk i (x := genericPoint (Spec R))
  have he : i (genericPoint (Spec R)) = genericPoint Y :=
    genericPoint_eq_of_isOpenImmersion i
  let k := pullback.map f g (Y.fromSpecStalk (i (genericPoint (Spec R)))) g
    (Spec.map (i.stalkMap (genericPoint (Spec R)))) (𝟙 _) (𝟙 _)
    (by simpa only [Category.comp_id, f] using hh.symm) (by simp)
  have hresult := IsIntegral.of_isIso k
  change IsIntegral (pullback (Y.fromSpecStalk (i (genericPoint (Spec R)))) g) at hresult
  rw [he] at hresult
  exact hresult


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Limits Opposite Scheme TensorProduct in
private theorem module_connected_sections (Λ : Type (u + 1)) [CommRing Λ]
    (X : Scheme.{u}) [ConnectedSpace X] (M : ModuleCat.{u + 1} Λ) :
    IsIso ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M)).app
      (op (Scheme.Etale.mk (𝟙 X)))) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} (Int.castRingHom Λ)).isLeftAdjoint
    infer_instance
  let J := X.smallEtaleTopology
  have : J.PreservesSheafification U :=
    GrothendieckTopology.instPreservesSheafification J U
  let P := (Functor.const X.Etaleᵒᵖ).obj M
  let T := Scheme.Etale.mk (𝟙 X)
  have h : IsIso ((toSheafify J (P ⋙ U)).app (op T)) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (Scheme.bijective_toSheafify_app_terminal X (U.obj M))
  have hf := congrArg (fun a ↦ a.app (op T)) (sheafComposeIso_hom_fac J U P)
  change (toSheafify J (P ⋙ U)).app (op T) ≫
    (sheafifyComposeIso J U P).hom.app (op T) =
      U.map ((toSheafify J P).app (op T)) at hf
  have : IsIso (U.map ((toSheafify J P).app (op T))) := by
    rw [← hf]
    infer_instance
  exact isIso_of_reflects_iso _ U

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open Limits Opposite Scheme TensorProduct in
private theorem isIso_constant_unit_stalk_of_connected_strict_fibre
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y)
    [ConnectedSpace ↥(pullback f (Scheme.strictLocalizationToBase s))]
    (M : ModuleCat.{u + 1} Λ) :
    IsIso (((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let Φ := Scheme.pointSmallEtale s
  let Z := pullback f (Scheme.strictLocalizationToBase s)
  let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F
  let T := Scheme.Etale.mk (𝟙 Y)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  let t := (Φ.uniqueFiberObj T hT).default
  obtain ⟨r, hr, hcoef⟩ := constant_strict_fibre_stalk_comparison Λ f s M t
  let := hr
  let c := (toSheafify Z.smallEtaleTopology ((Functor.const Z.Etaleᵒᵖ).obj M)).app
    (op (Scheme.Etale.mk (𝟙 Z)))
  have hc : IsIso c := module_connected_sections Λ Z M
  let a := (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)).app
    (op T) ≫ Φ.toPresheafFiber T t F.obj
  let P := (Functor.const Y.Etaleᵒᵖ).obj M
  have hg : IsIso (Φ.toPresheafFiber T t P) := by
    have : IsIso (Φ.toPresheafFiber T t P ≫ (Φ.presheafFiberConstIso M).hom) := by
      change IsIso (Φ.toPresheafFiber T t ((Functor.const Y.Etaleᵒᵖ).obj M) ≫
        (Φ.presheafFiberConstIso M).hom)
      rw [Φ.toPresheafFiber_presheafFiberConstIso_hom]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Φ.presheafFiberConstIso M).hom
  have ha : IsIso a := by
    have hn := Φ.toPresheafFiber_naturality
      (toSheafify Y.smallEtaleTopology P) T t
    change IsIso ((toSheafify Y.smallEtaleTopology P).app (op T) ≫
      Φ.toPresheafFiber T t (sheafify Y.smallEtaleTopology P))
    rw [← hn]
    infer_instance
  have hcomp : IsIso (a ≫ Φ.sheafFiber.map η ≫ r) := by
    change IsIso (_ ≫ _ ≫ _ ≫ _)
    rw [hcoef]
    exact hc
  have : IsIso (Φ.sheafFiber.map η ≫ r) := IsIso.of_isIso_comp_left a _
  have hi : IsIso (Φ.sheafFiber.map η) := IsIso.of_isIso_comp_right _ r
  exact (NatIso.isIso_map_iff
    (Φ.uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)) η).2 hi

/-- The unit from a constant sheaf to its generic-point pushforward is an isomorphism.
Source: Stacks Project, Tag 09Z5, generic-point part.
(blueprint: lem-weil-pbc-normal-constant-generic-unit)

Proof: evaluate the unit at an arbitrary geometric point and use the strict-henselization
stalk formula for the direct image. The strict henselization of the normal local domain at that
point is again a normal domain, and the fibre over the generic point is a nonempty localization
of it, hence is connected. Sections of a constant sheaf on this connected fibre are therefore
one copy of the coefficient module. Under the canonical pullback comparison, the stalk map of
the unit sends a coefficient to the same constant section, so it is an isomorphism. Geometric
stalks are conservative, which proves that the unit itself is an isomorphism.
-/
theorem isIso_unit_constantSheaf_generic_unit
    (Λ : Type (u + 1)) [CommRing Λ] {Y : Scheme.{u}} [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (M : ModuleCat.{u + 1} Λ) :
    IsIso ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        (Y.fromSpecStalk (genericPoint Y))).unit.app
          ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
  open Limits Opposite Scheme TensorProduct in by
    let j := Y.fromSpecStalk (genericPoint Y)
    let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
    let η := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app F
    apply Scheme.isIso_of_isIso_sheafFiber_map η
    intro y
    let s := Y.algClosurePoint y
    let : IsIntegral (pullback j (strictLocalizationToBase s)) :=
      normal_strict_generic_fibre_integral hY s
    let : ConnectedSpace ↥(pullback j (strictLocalizationToBase s)) := inferInstance
    exact isIso_constant_unit_stalk_of_connected_strict_fibre Λ j s M

end AlgebraicGeometry.Etale
