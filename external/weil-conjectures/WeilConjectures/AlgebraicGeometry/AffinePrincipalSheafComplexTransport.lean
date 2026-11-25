/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Transporting a finite-free complex to a principal affine open

(blueprint: lem-pc-affine-principal-sheaf-complex-transport)
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
-- Evaluate Mathlib's pushforward/scalar-restriction comparison at the full open.
private noncomputable def transport_pushforward_globalSections
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom := by
  exact Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso φ)
    (TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (.op ⊤))

-- The two functors have naturally isomorphic right adjoints, hence are isomorphic.
private noncomputable def transport_tilde_localization (A : Type u) [CommRing A] (f : A) :
    tilde.functor (.of A) ⋙ Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) ≅
      ModuleCat.extendScalars (algebraMap A (Localization.Away f)) ⋙
        tilde.functor (.of (Localization.Away f)) := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of (Localization.Away f) :=
    CommRingCat.ofHom (algebraMap A (Localization.Away f))
  exact ((tilde.adjunction (R := .of A)).comp
    (Scheme.Modules.restrictAdjunction (Spec.map φ))).ofNatIsoRight
      (transport_pushforward_globalSections φ) |>.leftAdjointUniq
        ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
          (tilde.adjunction (R := .of (Localization.Away f))))

/-- Restrict a finite-free sheaf complex and its derived comparison to `Spec(A_f)`.
Source: Stacks Project, Tag 08E7, converse proof, local-model comparison;
Tag 01HV (sections on principal opens), and Tag 08BS (exact open restriction).
(blueprint: lem-pc-affine-principal-sheaf-complex-transport).

Proof: Let V = D(f). Restrict P from the localized open site of U to that of V,
then use the equivalence with modules on the open subscheme V and the scheme
isomorphism V ≅ Spec(A_f). Define C to be this termwise image of P, with the
image differentials. Restriction and transport are additive and exact; hence the
complex identities hold and zero terms above the original bound remain zero.
They carry a free sheaf on a finite set to the free sheaf on the same set:
restriction commutes with the direct sums of copies of the structure sheaf,
and the scheme isomorphism identifies the structure sheaves. Apply these
functors to each given finite-free term isomorphism to obtain the asserted ranks.
The principal-open sections formula identifies the transported restriction of
tilde N with tilde(A_f tensor_A N). On the basis of principal opens in Spec(A_f),
both sides are the further localization of N, with identical restriction maps.
The identifications are natural in N and therefore commute with differentials,
yielding the comparison of complexes for M. Exactness allows termwise restriction
and transport to descend to derived categories. Use the canonical localization
comparison between choices of derived categories when the morphism universes
are wX and wY; it identifies their Q functors. Apply the induced functor to hiso,
use its compatibility with Q, compose with the preceding complex comparison,
and invert the result to obtain Q(C) ≅ Q(tilde(A_f tensor_A M)).
If V is empty, its localized module category and the module category of the
zero ring A_f have only zero objects, and the same construction applies.
No bound below, nonzero-ring assumption, or rank-positivity assumption is used.
This step constructs only a sheaf complex: lifting its differentials to modules
through affine full faithfulness is a separate theorem. -/
theorem affine_principal_sheaf_complex_transport (A : Type u) [CommRing A]
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{wX}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (f : A)
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (P : CochainComplex
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ)
    (hb : ∃ N : ℤ, ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
      (R := (moduleRings (Spec (.of A)).toRingedSpace).over U) (ULift.{u} (Fin r))))
    (hiso : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M)) ≅
      DerivedCategory.Q.obj P)) :
    ∃ C : CochainComplex
      (SheafOfModules.{u}
        (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace)) ℤ,
      (∃ b : ℤ, ∀ i : ℤ, b < i → CategoryTheory.Limits.IsZero (C.X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (C.X i ≅ SheafOfModules.free
        (R := moduleRings (Spec (.of (Localization.Away f))).toRingedSpace)
        (ULift.{u} (Fin r)))) ∧
      Nonempty (DerivedCategory.Q.obj C ≅
        DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Localization.Away f))
            (SheafOfModules.{u}
              (moduleRings (Spec (.of (Localization.Away f))).toRingedSpace))
            _ _ _ _ (tilde.functor (.of (Localization.Away f)))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
              ((Functor.mapHomologicalComplex
                (ModuleCat.extendScalars (algebraMap A (Localization.Away f)))
                (ComplexShape.up ℤ)).obj M))) := by
  classical
  let j := (basicOpenIsoSpecAway (R := .of A) f).inv ≫ (Spec (.of A)).homOfLE hf
  let E := (Scheme.Modules.overEquiv U).functor
  let T := Scheme.Modules.restrictFunctor j
  have : Limits.PreservesLimitsOfSize.{u, u} T := inferInstance
  have : T.Additive := Functor.additive_of_preserves_binary_products _
  have : E.Additive := Functor.additive_of_preserves_binary_products _
  let F : SheafOfModules.{u}
      ((moduleRings (Spec (.of A)).toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings
        (Spec (.of (Localization.Away f))).toRingedSpace) := E ⋙ T
  have : Limits.PreservesFiniteLimits F := Limits.comp_preservesFiniteLimits E T
  have : F.Additive := inferInstance
  have : Limits.PreservesFiniteColimits T := inferInstance
  have : Limits.PreservesFiniteColimits F := Limits.comp_preservesFiniteColimits E T
  -- This is the actual termwise restriction, including the image differentials.
  let C := (F.mapHomologicalComplex (.up ℤ)).obj P
  refine ⟨C, ?_, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hb
    exact ⟨b, fun i hi ↦ F.map_isZero (hb i hi)⟩
  · intro i
    obtain ⟨r, ⟨e⟩⟩ := hfree i
    let eU : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
        E.obj (SheafOfModules.unit ((moduleRings (Spec (.of A)).toRingedSpace).over U)) :=
      ((Scheme.Modules.overFunctorEquiv U).app _ ≪≫
        Scheme.Modules.restrictUnitIso U.ι).symm
    let eF : SheafOfModules.unit (moduleRings
        (Spec (.of (Localization.Away f))).toRingedSpace) ≅
        F.obj (SheafOfModules.unit
          ((moduleRings (Spec (.of A)).toRingedSpace).over U)) :=
      (Scheme.Modules.restrictUnitIso j).symm ≪≫ T.mapIso eU
    exact ⟨r, ⟨F.mapIso e ≪≫
      (SheafOfModules.mapFreeIso F (ULift.{u} (Fin r)) eF).symm⟩⟩
  · let L := SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U
    let R := Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))
    have fac : j ≫ U.ι =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))) := by
      dsimp [j]
      rw [Category.assoc, Scheme.homOfLE_ι, Iso.inv_comp_eq]
      exact (basicOpenIsoSpecAway_hom_SpecMap (R := .of A) f).symm
    let eR : L ⋙ F ≅ R :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) T ≪≫
        (Scheme.Modules.restrictFunctorComp j U.ι).symm ≪≫
        Scheme.Modules.restrictFunctorCongr fac
    have : L.Additive := by dsimp [L]; infer_instance
    have : R.Additive := Functor.additive_of_iso eR
    have : (tilde.functor (.of A)).PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ tilde.map_zero⟩
    have : (tilde.functor (.of (Localization.Away f))).PreservesZeroMorphisms :=
      ⟨fun _ _ ↦ tilde.map_zero⟩
    let K := ((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).obj M
    let eK := (Functor.mapHomologicalComplexCompIso eR (.up ℤ)).app K
    let eS := (NatIso.mapHomologicalComplex (transport_tilde_localization A f) (.up ℤ)).app M
    -- Map the supplied derived isomorphism, then compare both sides through Q.
    obtain ⟨e⟩ := hiso
    refine ⟨(F.mapDerivedCategoryFactors.app P).symm ≪≫
      F.mapDerivedCategory.mapIso e.symm ≪≫
      F.mapDerivedCategory.mapIso (L.mapDerivedCategoryFactors.app K) ≪≫
      F.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso eK ≪≫
      DerivedCategory.Q.mapIso eS⟩

end AlgebraicGeometry
