/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechConstruction
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.Grp.Zero

/-! # Godement augmentation on principal affine intersections

Source: Stacks Project, Tags 0FKS, 01ET, and 01XB.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem principalIntersection_affine (A : CommRingCat.{u}) (I : Ideal A)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (p : ℕ) (t : Fin (p + 1) ↪o Fin r) :
    IsAffineOpen (alternatingCechIntersection (ringComplexPrincipalCover A I f) t) := by
  let W : (Spec A).Opens := ⨅ j : Fin (p + 1), PrimeSpectrum.basicOpen (f (t j))
  have hW : IsAffineOpen W := by
    apply IsAffineOpen.iInf
    intro j
    exact IsAffineOpen.Spec_basicOpen _
  have hWU : W ≤ (ringComplexOpen A I).ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    intro x hx
    have hx' : f (t 0) ∉ x.asIdeal :=
      (iInf_le (fun j : Fin (p + 1) ↦ PrimeSpectrum.basicOpen (f (t j))) 0) hx
    change ¬ I ≤ x.asIdeal
    intro h
    apply hx'
    apply h
    rw [← hf]
    exact Ideal.subset_span (Set.mem_range_self (t 0))
  have heq : alternatingCechIntersection (ringComplexPrincipalCover A I f) t =
      (ringComplexOpen A I).ι ⁻¹ᵁ W := by
    ext x
    simp only [alternatingCechIntersection, ringComplexPrincipalCover, W]
    change x ∈ (⨅ k, (ringComplexOpen A I).ι ⁻¹ᵁ
      PrimeSpectrum.basicOpen (f (t k)) : (ringComplexOpen A I).toScheme.Opens) ↔
        x.val ∈ (⨅ j : Fin (p + 1), PrimeSpectrum.basicOpen (f (t j)))
    simp only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    rfl
  rw [heq]
  exact hW.preimage_of_isOpenImmersion _ hWU

private theorem godement_eval_quasiIso (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) :
    QuasiIso (((SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation (moduleRings X.toRingedSpace).obj (op U)).mapHomologicalComplex
        (.up ℤ)).map (ringComplexGodementUnit X)) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let E := RingedSpace.openModuleSections X.toRingedSpace U
  have : E.Additive := inferInstance
  have : PreservesFiniteLimits E := by
    dsimp [E, RingedSpace.openModuleSections]
    infer_instance
  let F := SheafOfModules.unit (moduleRings X.toRingedSpace)
  have : F.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have hF : E.rightAcyclic F := by
    intro q
    have := subsingleton_openModuleCohomology_of_isAffineOpen X F U hU (q + 1)
      (Nat.succ_pos q)
    change IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace (q + 1) U).obj F)
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hG : ∀ n, E.rightAcyclic ((ringComplexGodementResolution X).X n) := by
    apply HomologicalComplex.prop_extend_X E.rightAcyclic ComplexShape.embeddingUpNat
    intro n
    have hm := (Scheme.Modules.moduleCup_godement_models_exist X F).choose_spec.choose_spec.1
    obtain ⟨h, -⟩ := hm
    change E.rightAcyclic ((ringComplexGodementModel X).obj ⦋n⦌)
    have ht : (ringComplexGodementModel X).obj (SimplexCategory.mk n) =
        Scheme.Modules.moduleCup_godementIterate X F (n + 1) := h n
    exact E.rightAcyclic.prop_of_iso (eqToIso ht).symm (by
      apply Scheme.Modules.rightAcyclic_of_isFlasque E
      · intro S hS h₁
        exact Scheme.Modules.epi_app_of_shortExact_of_isFlasque hS h₁ U
      · exact Scheme.Modules.moduleCup_godement_object_flasque X _)
  have hsingle : ∀ n, E.rightAcyclic
      (((CochainComplex.singleFunctor X.Modules 0).obj F).X n) := by
    intro n
    by_cases hn : n = 0
    · subst n
      exact E.rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F).symm hF
    · exact E.rightAcyclic.prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F n hn)
  have : QuasiIso (ringComplexGodementUnit X) :=
    Scheme.Modules.moduleCup_godement_model_quasiIso X F (ringComplexGodementModel X)
      (ringComplexGodementUnit X)
      (Scheme.Modules.moduleCup_godement_models_exist X F).choose_spec.choose_spec.1
  have : (ringComplexGodementResolution X).IsStrictlyGE 0 := by
    unfold ringComplexGodementResolution
    infer_instance
  have : ((CochainComplex.singleFunctor X.Modules 0).obj F).IsStrictlyGE 0 := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F n (by omega)
  have h := E.quasiIso_map_of_rightAcyclic (ringComplexGodementUnit X) 0 hsingle hG
  let S := SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
    PresheafOfModules.evaluation (moduleRings X.toRingedSpace).obj (op U)
  let V := forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op U)))
    AddCommGrpCat.{u}
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((S.mapHomologicalComplex (.up ℤ)).map (ringComplexGodementUnit X)) V).mp
  exact h

/-- The chosen Godement augmentation remains a quasi-isomorphism on every
principal affine intersection of a generating cover.
Source: Stacks Project, Tags 0FKS, 01ET and 01XB.
(auxiliary; not a blueprint node)

Proof: the span equality shows D(f_i) lies in Spec A minus V(I).
The intersection indexed by t is therefore the principal open D(product f(t i)),
viewed inside that complement; it is affine, including when the product is zero.
The structure module restricts to its structure module and is quasi-coherent,
so its positive cohomology vanishes by affine vanishing. The prescribed Godement
augmentation is a quasi-isomorphism, extended by zero in negative degrees. Each
nonnegative term is a product of stalk skyscrapers, hence flasque. Restriction
to an open remains flasque and is exact. These restricted terms are acyclic for
sections. Apply the bounded-below acyclic-resolution comparison to the coefficient
single complex and this Godement complex: both have section-acyclic terms, so
sections preserve this quasi-isomorphism. This is the displayed evaluation map,
without changing the augmentation. If the cover is empty, there are no tuples;
if the intersection is empty, every section module is zero. Zero rings and
repeated generators require no additional case. -/
theorem ringComplexGodement_affineSections (A : CommRingCat.{u}) (I : Ideal A)
    (r : ℕ) (f : Fin r → A) (hf : Ideal.span (Set.range f) = I) :
    ∀ (p : ℕ) (t : Fin (p + 1) ↪o Fin r),
      QuasiIso (((SheafOfModules.forget.{u}
        (moduleRings (ringComplexOpen A I).toScheme.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u}
          (moduleRings (ringComplexOpen A I).toScheme.toRingedSpace).obj
          (op (alternatingCechIntersection
            (ringComplexPrincipalCover A I f) t))).mapHomologicalComplex (.up ℤ)).map
              (ringComplexGodementUnit (ringComplexOpen A I).toScheme)) := by
  intro p t
  exact godement_eval_quasiIso (ringComplexOpen A I).toScheme _
    (principalIntersection_affine A I f hf p t)

end AlgebraicGeometry
