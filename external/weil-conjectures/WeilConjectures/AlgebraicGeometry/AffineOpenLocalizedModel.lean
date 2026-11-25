/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.AffineModuleComplexRepresentative
import WeilConjectures.AlgebraicGeometry.AffineOpenPseudoCoherentLocalizationPoint
import WeilConjectures.AlgebraicGeometry.AffinePrincipalCoverQuasiIsoDetection

/-! # Affine module models on a quasi-compact open

Source: Stacks Project, Tag 08EE, module-model reduction and final sheafification
(blueprint: lem-sc-affine-open-localized-model).
-/

@[expose] public section

set_option autoImplicit false

universe u w wL

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

local instance instAdditiveModuleCatExtendScalars_affineOpenLocalizedModel
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u} f).left_adjoint_additive

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-coherent derived object on an affine scheme, pseudo-coherent on a
quasi-compact open, has a module-complex representative and a finite collection
of localizations where it is pseudo-coherent. Quasi-isomorphisms at these
localizations become derived isomorphisms after sheafification and restriction.
This statement supplies the comparison, not a finite-free replacement.

Source: Stacks Project, Tag 08EE, proof of lemma-lift-pseudo-coherent, affine
module model, finite principal-open cover, and final sheafification; Tag 06Z0
and Tag 08E7 (blueprint: lem-sc-affine-open-localized-model).

Proof:
Write A = Gamma(X,O_X), and use the canonical isomorphism X ≅ Spec A.
The affine quasi-coherent derived equivalence of Tag 06Z0 gives an object of
D(A) representing E'. Choose a complex M representing that derived object;
the equivalence's termwise tilde comparison, transported along X ≅ Spec A
and the given natural isomorphism hT, gives Q(T M) ≅ E'. Quasi-compactness
and the principal-open basis give a finite cover of U by D(f_j) contained
in U. Restrict the given isomorphism E'|U ≅ E to each member of the cover.
Pseudo-coherence restricts to open subsets by restricting the local finite-free
models. The associated sheaf of M restricts to the associated sheaf of M_fj,
by exactness of localization and the sections formula for tilde. The affine
pseudo-coherence criterion of Tag 08E7 therefore makes each M_fj pseudo-coherent.
For any chain map alpha into M, a quasi-isomorphism after every localization
sheafifies to a quasi-isomorphism on every member of this cover: exact tilde
commutes with cohomology. Its restriction to U is a quasi-isomorphism, since
an isomorphism of cohomology sheaves can be checked on an open cover. The
exact restriction functor commutes with Q, so its derived image is invertible.
No unit-ideal condition on the f_j is required: their principal opens cover U,
not necessarily X. If U is empty choose the empty family; restriction has
zero target category and every morphism is invertible there.
-/
theorem exists_affine_open_localized_model
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [∀ f : X.presheaf.obj (.op ⊤), HasDerivedCategory.{wL}
      (ModuleCat.{u} (Localization.Away f))]
    (T : ModuleCat.{u} (X.presheaf.obj (.op ⊤)) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace)) [T.PreservesZeroMorphisms]
    (hT : Nonempty (T ≅ tilde.functor (X.presheaf.obj (.op ⊤)) ⋙
      Modules.restrictFunctor X.isoSpec.hom))
    (E' : schemeDerivedQCohCategory X) (E : schemeDerivedCategory U.toScheme)
    (hE : IsPseudoCoherent U.toScheme E)
    (e : Nonempty
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj E'.obj ≅ E)) :
    ∃ (M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ)
      (r : ℕ) (f : Fin r → X.presheaf.obj (.op ⊤)),
      (∀ j : Fin r, DerivedCategory.IsPseudoCoherent
        (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars
            (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away (f j))))
          (ComplexShape.up ℤ)).obj M))) ∧
      Nonempty (DerivedCategory.Q.obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≅ E'.obj) ∧
      ∀ (F : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op ⊤))) ℤ) (α : F ⟶ M),
        (∀ j : Fin r, QuasiIso ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars
            (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map α)) →
        IsIso (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.map
              (DerivedCategory.Q.map ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map α))) :=
  by
    classical
    obtain ⟨M, ⟨eM⟩⟩ := exists_affine_module_complex_representative X E'.obj E'.property
    obtain ⟨t⟩ := hT
    have c : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅
        ((Modules.restrictFunctor X.toSpecΓ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
          ((@Functor.mapHomologicalComplex ℤ _ _ _ _ _ _
            (tilde.functor (X.presheaf.obj (.op ⊤)))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj M) := by
      exact HomologicalComplex.Hom.isoOfComponents (fun i ↦ t.app (M.X i))
        (fun i j _ ↦ (t.hom.naturality (M.d i j)).symm)
    have eTM : DerivedCategory.Q.obj
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≅ E'.obj :=
      DerivedCategory.Q.mapIso c ≪≫ eM.symm
    let R := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)).mapDerivedCategory
    obtain ⟨eU⟩ := e
    have hM : IsPseudoCoherent U.toScheme (R.obj
        (DerivedCategory.Q.obj ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) := by
      intro x
      obtain ⟨V, hx, P, hb, hfree, ⟨hP⟩⟩ := hE x
      exact ⟨V, hx, P, hb, hfree, ⟨(SheafOfModules.overFunctor.{u}
        (moduleRings U.toScheme.toRingedSpace) V).mapDerivedCategory.mapIso
          (R.mapIso eTM ≪≫ eU) ≪≫ hP⟩⟩
    let S := {a : X.presheaf.obj (.op ⊤) // X.basicOpen a ≤ U ∧
      DerivedCategory.IsPseudoCoherent
        (DerivedCategory.Q.obj ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars
            (algebraMap (X.presheaf.obj (.op ⊤)) (Localization.Away a)))
          (ComplexShape.up ℤ)).obj M))}
    have hpoint : (U : Set X) ⊆ ⋃ a : S, (X.basicOpen a.val : Set X) := by
      intro x hx
      obtain ⟨a, hxa, haU, ha⟩ :=
        affine_open_pseudoCoherent_localization_point X U T ⟨t⟩ M hM x hx
      exact Set.mem_iUnion.mpr ⟨⟨a, haU, ha⟩, hxa⟩
    obtain ⟨s, hs⟩ := hU.elim_finite_subcover
      (fun a : S ↦ (X.basicOpen a.val : Set X)) (fun a ↦ (X.basicOpen a.val).isOpen) hpoint
    let enum : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
    let f : Fin (Fintype.card s) → X.presheaf.obj (.op ⊤) := fun j ↦ (enum j).val.val
    have hsub : ∀ j, X.basicOpen (f j) ≤ U := fun j ↦ (enum j).val.property.1
    have hcover : ∀ x : X, x ∈ U → ∃ j, x ∈ X.basicOpen (f j) := by
      intro x hx
      obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (hs hx)
      refine ⟨enum.symm ⟨a, ha⟩, ?_⟩
      change x ∈ (X.basicOpen (f (enum.symm ⟨a, ha⟩)) : Set X)
      simpa only [f, Equiv.apply_symm_apply] using hxa
    refine ⟨M, Fintype.card s, f, fun j ↦ (enum j).val.property.2, ⟨eTM⟩, ?_⟩
    intro F α hα
    exact affine_principal_cover_quasiIso_detection X U T ⟨t⟩
      (Fintype.card s) f hsub hcover F M α hα

end AlgebraicGeometry.Scheme
