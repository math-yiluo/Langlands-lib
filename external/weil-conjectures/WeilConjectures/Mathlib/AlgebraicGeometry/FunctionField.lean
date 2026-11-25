/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite

/-!
# The generic point as a morphism from the spectrum of the function field

For an integral scheme `X`, `Scheme.functionField` is the stalk of the structure sheaf at the
generic point, and `Scheme.fromSpecStalk` turns a stalk into a morphism from its spectrum.
This file names the composite, the canonical morphism `Spec k(X) ⟶ X`, and shows that for an
integral scheme `X` it is dominant and stays scheme-theoretically dominant after flat base
change: for a flat `U ⟶ X`, functions on `U` are determined by their restriction to the
generic fibre `U ×_X Spec k(X)`. An element of the function field lying in the local rings at
all points of a nonempty open `U` is a section over `U`
(`AlgebraicGeometry.Scheme.exists_germToFunctionField_eq`). It also shows that the sections of
an integral scheme with integrally closed local rings over a nonempty open form an integrally
closed domain (`AlgebraicGeometry.Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk`), and
that if moreover the function field is separably closed then all local rings are strictly
henselian
(`AlgebraicGeometry.Scheme.henselianLocalRing_stalk_of_isSepClosed_functionField`,
`AlgebraicGeometry.Scheme.isSepClosed_residueField_of_isSepClosed_functionField`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- The canonical morphism `Spec k(X) ⟶ X` from the spectrum of the function field of an
irreducible scheme `X`, namely `Scheme.fromSpecStalk` at the generic point. -/
noncomputable abbrev fromSpecFunctionField (X : Scheme.{u}) [IrreducibleSpace X] :
    Spec X.functionField ⟶ X :=
  X.fromSpecStalk (genericPoint X)

/-- The sections of an integral scheme over a nonempty open `U` at whose points the local rings
are integrally closed form an integrally closed domain: an element of the function field which
is integral over `Γ(X, U)` is integral over every local ring at a point of `U`, hence lies in each
of them, and the sections over `U` are exactly the elements of the function field lying in all
these local rings. -/
theorem isIntegrallyClosed_of_isIntegrallyClosed_stalk_of_mem {X : Scheme.{u}} [IsIntegral X]
    (U : X.Opens) [Nonempty U] (hX : ∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIntegrallyClosed Γ(X, U) := by
  have hinj := X.germToFunctionField_injective U
  have : FaithfulSMul Γ(X, U) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : IsIntegrallyClosedIn Γ(X, U) X.functionField := by
    refine isIntegrallyClosedIn_iff.mpr ⟨hinj, fun {g} hg ↦ ?_⟩
    have H (y : U) : ∃ (V : X.Opens) (hyV : (y : X) ∈ V) (hVU : V ≤ U) (t : Γ(X, V)),
        @Scheme.germToFunctionField X _ V ⟨⟨y, hyV⟩⟩ t = g := by
      have := hX y y.2
      obtain ⟨s, hs⟩ := (IsIntegrallyClosed.isIntegral_iff (R := X.presheaf.stalk y)).mp
        (hg.tower_top (A := X.presheaf.stalk y))
      obtain ⟨W, hyW, t, rfl⟩ := X.presheaf.exists_germ_eq s
      have : Nonempty W := ⟨⟨y, hyW⟩⟩
      refine ⟨W ⊓ U, ⟨hyW, y.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
      rw [← hs, Scheme.algebraMap_germ_eq_germToFunctionField]
      exact X.presheaf.germ_res_apply _ _ _ t
    choose V hyV hVU t ht using H
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun y ↦ homOfLE (hVU y))
      (fun y hy ↦ Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV _⟩) t fun i j ↦ by
        obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (V i).isOpen (V j).isOpen
          ⟨i, hyV i⟩ ⟨j, hyV j⟩
        have : Nonempty (V i ⊓ V j : X.Opens) := ⟨⟨z, hz⟩⟩
        apply X.germToFunctionField_injective (V i ⊓ V j)
        exact (X.presheaf.germ_res_apply _ _ _ _).trans
          ((ht i).trans ((ht j).symm.trans (X.presheaf.germ_res_apply _ _ _ _).symm))
    obtain ⟨y⟩ := ‹Nonempty U›
    refine ⟨s, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ← ht y, ← hs y]
    exact (X.presheaf.germ_res_apply _ _ _ s).symm
  exact .of_isIntegrallyClosedIn Γ(X, U) X.functionField

/-- An element `g` of the function field of an integral scheme `X` which lies in the local ring of
every point of a nonempty open `U` is a section over `U`: the local representatives of `g` agree
on overlaps, since `X` is irreducible and the restriction maps to the function field are
injective, so they glue. -/
theorem exists_germToFunctionField_eq {X : Scheme.{u}} [IsIntegral X] (U : X.Opens)
    [Nonempty U] (g : X.functionField)
    (hg : ∀ x ∈ U, g ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = g := by
  have H (y : U) : ∃ (V : X.Opens) (hyV : (y : X) ∈ V) (hVU : V ≤ U) (t : Γ(X, V)),
      @Scheme.germToFunctionField X _ V ⟨⟨y, hyV⟩⟩ t = g := by
    obtain ⟨s, hs⟩ := hg y y.2
    obtain ⟨W, hyW, t, rfl⟩ := X.presheaf.exists_germ_eq s
    have : Nonempty W := ⟨⟨y, hyW⟩⟩
    refine ⟨W ⊓ U, ⟨hyW, y.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
    rw [← hs, Scheme.algebraMap_germ_eq_germToFunctionField]
    exact X.presheaf.germ_res_apply _ _ _ t
  choose V hyV hVU t ht using H
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V U (fun y ↦ homOfLE (hVU y))
    (fun y hy ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV _⟩) t fun i j ↦ by
      obtain ⟨z, hz⟩ := nonempty_preirreducible_inter (V i).isOpen (V j).isOpen
        ⟨i, hyV i⟩ ⟨j, hyV j⟩
      have : Nonempty (V i ⊓ V j : X.Opens) := ⟨⟨z, hz⟩⟩
      apply X.germToFunctionField_injective (V i ⊓ V j)
      exact (X.presheaf.germ_res_apply _ _ _ _).trans
        ((ht i).trans ((ht j).symm.trans (X.presheaf.germ_res_apply _ _ _ _).symm))
  obtain ⟨y⟩ := ‹Nonempty U›
  refine ⟨s, ?_⟩
  rw [← ht y, ← hs y]
  exact (X.presheaf.germ_res_apply _ _ _ s).symm

/-- The sections of an integral scheme with integrally closed local rings over a nonempty open
`U` form an integrally closed domain; see
`AlgebraicGeometry.Scheme.isIntegrallyClosed_of_isIntegrallyClosed_stalk_of_mem`. -/
theorem isIntegrallyClosed_of_isIntegrallyClosed_stalk {X : Scheme.{u}} [IsIntegral X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) :=
  isIntegrallyClosed_of_isIntegrallyClosed_stalk_of_mem U fun x _ ↦ hX x

/-- The stalks of an integral normal scheme with separably closed function field are henselian.
-/
theorem henselianLocalRing_stalk_of_isSepClosed_functionField {S : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (x : S) : HenselianLocalRing (S.presheaf.stalk x) :=
  have := hS x
  HenselianLocalRing.of_isSepClosed_fractionRing S.functionField

/-- The residue fields of an integral normal scheme with separably closed function field are
separably closed. -/
theorem isSepClosed_residueField_of_isSepClosed_functionField {S : Scheme.{u}}
    [IsIntegral S] (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (x : S) : IsSepClosed (S.residueField x) :=
  have := hS x
  IsLocalRing.isSepClosed_residueField_of_isSepClosed_fractionRing S.functionField

variable (X : Scheme.{u}) [IsIntegral X]

/-- The generic point `Spec k(X) ⟶ X` of an integral scheme is dominant: its image contains
the generic point. -/
instance isDominant_fromSpecFunctionField : IsDominant X.fromSpecFunctionField := by
  rw [isDominant_iff, DenseRange]
  refine dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset ?_)
  rw [← genericPoint_spec X]
  exact closure_mono (Set.singleton_subset_iff.2 ⟨_, X.fromSpecStalk_closedPoint⟩)

/-- For a flat morphism `f : U ⟶ X` to an integral scheme, pulling back functions along the
projection `U ×_X Spec k(X) ⟶ U` from the generic fibre is injective on global sections:
`Spec k(X) ⟶ X` is scheme-theoretically dominant, as a dominant morphism to a reduced
scheme, and this is preserved by the flat base change along `f`. -/
lemma injective_Γ_map_pullback_fst_fromSpecFunctionField {U : Scheme.{u}} (f : U ⟶ X)
    [Flat f] :
    Function.Injective (Scheme.Γ.map (pullback.fst f X.fromSpecFunctionField).op) := by
  have := IsSchemeTheoreticallyDominant.of_isDominant X.fromSpecFunctionField
  have : IsSchemeTheoreticallyDominant (pullback.fst f X.fromSpecFunctionField) := by
    rw [← pullbackSymmetry_hom_comp_snd]
    infer_instance
  exact (pullback.fst f X.fromSpecFunctionField).app_injective ⊤

/-- A nonempty open of an irreducible scheme contains the generic point. -/
lemma genericPoint_mem_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X] (W : X.Opens)
    [h : Nonempty W] : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)

/-- The generic point `Spec k(X) ⟶ X` maps into every nonempty open of `X`. -/
lemma top_le_preimage_fromSpecFunctionField {X : Scheme.{u}} [IsIntegral X] (W : X.Opens)
    [Nonempty W] : ⊤ ≤ X.fromSpecFunctionField ⁻¹ᵁ W := fun x _ ↦ by
  have : x = IsLocalRing.closedPoint _ := Subsingleton.elim (α := PrimeSpectrum _) _ _
  subst this
  change X.fromSpecStalk _ _ ∈ W
  rw [fromSpecStalk_closedPoint]
  exact genericPoint_mem_of_nonempty W

/-- On sections over a nonempty open `W`, the generic point `Spec k(X) ⟶ X` is the germ map
`Γ(X, W) ⟶ k(X)`. -/
lemma fromSpecFunctionField_appLE_eq {X : Scheme.{u}} [IrreducibleSpace X] (W : X.Opens)
    [Nonempty W] (h : ⊤ ≤ X.fromSpecFunctionField ⁻¹ᵁ W) :
    X.fromSpecFunctionField.appLE W ⊤ h =
      X.germToFunctionField W ≫ (ΓSpecIso X.functionField).inv := by
  rw [Scheme.Hom.appLE, fromSpecStalk_app (genericPoint_mem_of_nonempty W), Category.assoc,
    Category.assoc, ← Functor.map_comp]
  have : ((homOfLE le_top).op ≫ (homOfLE h).op :
      (Opposite.op (⊤ : (Spec X.functionField).Opens)) ⟶ _) = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

/-- For a nonempty affine open `W` of an integral scheme `X`, the sections of `Spec k(X)` are
the localization of `Γ(X, W)` at its nonzero divisors. -/
lemma isLocalization_fromSpecFunctionField_appLE {X : Scheme.{u}} [IsIntegral X] {W : X.Opens}
    (hW : IsAffineOpen W) [Nonempty W] (h : ⊤ ≤ X.fromSpecFunctionField ⁻¹ᵁ W) :
    letI := (X.fromSpecFunctionField.appLE W ⊤ h).hom.toAlgebra
    IsLocalization (nonZeroDivisors Γ(X, W)) Γ(Spec X.functionField, ⊤) := by
  have := functionField_isFractionRing_of_isAffineOpen X W hW
  let e := (Scheme.ΓSpecIso X.functionField).symm.commRingCatIsoToRingEquiv
  have := (IsLocalization.isLocalization_iff_of_ringEquiv (nonZeroDivisors Γ(X, W)) e).mp this
  convert this using 1
  refine Algebra.algebra_ext _ _ fun r ↦ ?_
  exact congr($(fromSpecFunctionField_appLE_eq W h).hom r)


end AlgebraicGeometry.Scheme
