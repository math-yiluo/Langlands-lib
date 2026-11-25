/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedGlobalScalar
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.AffineOpenPerfectSourceModel
import WeilConjectures.AlgebraicGeometry.AffineOpenSupportedTargetModel
import WeilConjectures.AlgebraicGeometry.AffineOpenRealizationScalar
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-! # Affine module models with supported cohomology

Source: Stacks Project, Tags 08EJ, 08EB and 06Z0.
(blueprint: lem-sc-perfect-support-affine-module-model).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

private theorem affineSheafification_preservesFiniteLimits
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) :
    PreservesFiniteLimits (affinePerfectSheafification X U hU) := by
  let : (Modules.restrictFunctor hU.isoSpec.hom).Additive :=
    Functor.additive_of_preserves_binary_products _
  let A := X.presheaf.obj (op U)
  let T := tilde.functor A
  let : T.PreservesMonomorphisms := ⟨by
    intro M N g hg
    let : Mono g := hg
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro V s t h
    apply Subtype.ext
    funext x
    apply IsLocalizedModule.map_injective x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl N)
      g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)
    exact congrArg (fun z ↦ z.val x) h⟩
  let : T.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels T
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  unfold affinePerfectSheafification
  exact comp_preservesFiniteLimits _ _

/-- Affine sheafification has a full additive realization on derived categories. -/
private theorem exists_affinePerfect_full_realization
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let A := ↑(X.presheaf.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    ∃ F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)),
      F.Full ∧ F.Additive ∧ Nonempty (DerivedCategory.Q ⋙ F ≅
        (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) := by
  let A := ↑(X.presheaf.obj (op U))
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  -- Reuse the abelian structures throughout the derived comparisons.
  let : Abelian (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    inferInstance
  let : Abelian
      (SheafOfModules.{u} (moduleRings (Spec (X.presheaf.obj (op U))).toRingedSpace)) :=
    inferInstance
  let H := affinePerfectSheafification X U hU
  let : PreservesFiniteLimits H := affineSheafification_preservesFiniteLimits X U hU
  let : H.Additive := Functor.additive_of_preserves_binary_products H
  let : PreservesFiniteColimits H := by
    dsimp [H, affinePerfectSheafification]
    exact comp_preservesFiniteColimits _ _
  let F : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    H.mapDerivedCategory.{u + 1, w}
  let : HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings (Spec (X.presheaf.obj (op U))).toRingedSpace)) :=
    HasDerivedCategory.standard _
  obtain ⟨e, ⟨ce⟩, _, _⟩ := exists_affineQCohDerivedEquivalence.{u, u + 1, u + 1}
      (X.presheaf.obj (op U))
  obtain ⟨t, ⟨ct⟩⟩ := affine_localized_site_derived_transport.{u, u + 1, w} X U hU
  let G := e.functor ⋙
    (schemeDerivedQCohProperty (Spec (X.presheaf.obj (op U)))).ι ⋙ t.functor
  let : G.Full := inferInstance
  let c : DerivedCategory.Q ⋙ G ≅
      H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight ce t.functor ≪≫ ct
  let d : G ≅ F := Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ))
    (DerivedCategory.Q ⋙ G) (H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    G F c
  exact ⟨F, Functor.Full.of_iso d, inferInstance, ⟨H.mapDerivedCategoryFactors⟩⟩

set_option linter.unusedVariables false in
/-- Affine restriction admits a bounded finite-projective source model and a target
whose cohomology is elementwise power torsion. The comparison is full and additive
and intertwines the scalar identity of the source with restriction of global scalars.
Source: Stacks Project, Tag 08EJ, affine paragraph; Tags 08EB and 06Z0.
(blueprint: lem-sc-perfect-support-affine-module-model).

Proof: Compare localized-site restriction with restriction to the open subscheme U
using open_derived_restriction_comparison. Perfectness restricts: intersect each
strictly perfect neighbourhood with U and restrict the finite-free retractions.
Quasi-coherence and stalkwise support restrict by the comparison theorem, including
for the shifted target. Identify U with Spec of its section ring A using its affine
presentation. The affine derived equivalence, followed by transport through this
scheme isomorphism and the inverse localized-site comparison, gives F. These functors
are fully faithful and additive. The bounded-projective criterion applied to the
restricted perfect source gives P, its bounds, finite and projective terms, and eP.
Choose the inverse-equivalence image M of the restricted shifted target and the
counit isomorphism eM. Exactness identifies H^i(M) with the corresponding affine
module of the restricted cohomology sheaf. Its localization at the restricted f is
zero, since its stalks vanish on D(f). The localization zero criterion makes every
cohomology element power torsion. Finally, associated sheaf, open restriction and
scheme-isomorphism transport all act sectionwise, so multiplication by the component
of any global scalar a at U corresponds to restriction of schemeDerivedScalar X a.
This gives the displayed identity after composing with eP.hom. When U is empty, A is
the zero ring and all these categories are zero; the zero models give the same data.
No assertion about torsion of derived morphisms is used in this construction. -/
theorem perfect_support_affine_module_model
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E E' : schemeDerivedQCohCategory X)
    (hE : X.IsPerfect E.obj)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ) :
    let A := ↑(X.sheaf.obj.obj (op U))
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ)
      (M : DerivedCategory (ModuleCat.{u} A))
      (F : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))),
      F.Full ∧ F.Additive ∧
      (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Finite A (P.X i)) ∧
      (∀ i : ℤ, Module.Projective A (P.X i)) ∧
      (∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj M),
        ∃ n : ℕ, (f.val (op U)) ^ n • m = 0) ∧
      ∃ (eP : F.obj (DerivedCategory.Q.obj P) ≅ R.obj E.obj)
        (eM : F.obj M ≅ R.obj (E'.obj⟦k⟧)),
        ∀ a : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}),
          F.map ((show A from a.val (op U)) • 𝟙 (DerivedCategory.Q.obj P)) ≫ eP.hom =
            eP.hom ≫ R.map (schemeDerivedScalar X a (𝟙 E.obj)) := by
  obtain ⟨F, hfull, hadd, hF⟩ := exists_affinePerfect_full_realization X U hU
  obtain ⟨P, hb, hf, hp, ⟨eP⟩⟩ :=
    affine_open_perfect_source_model X E hE U hU F hF
  obtain ⟨M, htors, ⟨eM⟩⟩ :=
    affine_open_supported_target_model X f E' hSupport U hU k F hF
  refine ⟨P, M, F, hfull, hadd, hb, hf, hp, htors, eP, eM, ?_⟩
  intro a
  exact affine_open_realization_scalar X U hU F hF P E.obj eP a

end AlgebraicGeometry.Scheme
