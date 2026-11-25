/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.Pullback

import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

private theorem pushforward_injectives
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    [PreservesFiniteLimits i] :
    (i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).PreservesInjectiveObjects := by
  let := flat_of_preservesFiniteLimits i
  let := preservesFiniteLimits_op_lan_of_flat (H := AddCommGrpCat.{u}) i
  let := Functor.sheafPullbackConstruction.preservesFiniteLimits
    i AddCommGrpCat.{u} (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  exact (i.sheafAdjunctionContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
    ).preservesInjectiveObjects_of_preservesFiniteLimits

set_option backward.isDefEq.respectTransparency false in
/-- Push an injective resolution through a left exact, injective-preserving functor
when its higher derived images vanish. The complex and augmentation are constructed
explicitly; kernel preservation treats degree zero, and vanishing treats positive degrees. -/
private noncomputable def mapResolution
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasInjectiveResolutions A]
    (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T]
    [T.PreservesInjectiveObjects] {X : A} (I : InjectiveResolution X)
    (h : ∀ q : ℕ, 0 < q → IsZero ((T.rightDerived q).obj X)) :
    InjectiveResolution (T.obj X) where
  cocomplex := (T.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  injective n := T.injective_obj_of_injective (I.injective n)
  ι := (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨T.map (I.ι.f 0), by
      change T.map (I.ι.f 0) ≫ T.map (I.cocomplex.d 0 1) = 0
      rw [← T.map_comp, I.ι_f_zero_comp_complex_d, T.map_zero]⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff]
      apply (ShortComplex.quasiIso_iff_of_zeros _ (by rfl) (by
        change ((CochainComplex.single₀ B).obj (T.obj X)).d 0 1 = 0
        simp) (by
          simp [HomologicalComplex.shortComplexFunctor'])).2
      apply (ShortComplex.exact_and_mono_f_iff_f_is_kernel _).2
      constructor
      refine IsLimit.ofIsoLimit (KernelFork.mapIsLimit _ I.isLimitKernelFork T) ?_
      exact Fork.ext (Iso.refl _) (by
        simp only [InjectiveResolution.kernelFork, CochainComplex.single₀_obj_zero,
          Functor.mapHomologicalComplex_obj_X, Functor.mapHomologicalComplex_obj_d, Fork.ofι_pt,
          Iso.refl_hom, Fork.ι_ofι, HomologicalComplex.shortComplexFunctor'_map_τ₂,
          Category.id_comp, KernelFork.map_ι]
        exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _)
    | succ n =>
      rw [quasiIsoAt_iff_exactAt]
      · rw [HomologicalComplex.exactAt_iff_isZero_homology]
        exact (h (n + 1) (Nat.zero_lt_succ n)).of_iso
          (I.isoRightDerivedObj T (n + 1)).symm
      · exact CochainComplex.exactAt_succ_single_obj _ _⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Acyclic Leray for right-derived terminal sections, without either Ext model.
Source: Stacks Project, Tags 072Z and 0733(1).
(blueprint: new-etale-zariski-derived-sections-acyclic-leray)

Proof: A continuous finite-limit-preserving i gives an exact inverse image on
abelian sheaves: finite-limit preservation gives representable flatness, hence
left exactness of inverse image on sets; its lift to abelian group objects is
left exact and, being a left adjoint, right exact. Its right adjoint T therefore
preserves injectives. T is left exact as a right adjoint. Choose an injective
resolution I of F. If all positive right-derived images of F vanish, the
augmented complex T(F) -> T(I) is exact: left exactness proves the augmentation
is the degree-zero kernel, and its positive homology is R^q T(F), hence zero.
Every T(I^k) is injective, so T(I) is an injective resolution of T(F).
Evaluation of T(I) at the top open is definitionally evaluation of I at i(top).
Compute right-derived Zariski evaluation using T(I), and right-derived etale
evaluation using I. Their section complexes are identical, giving c F hF n.
For F -> G lift the morphism to a comparison I_F -> I_G. Applying T gives a
comparison of the pushed resolutions. The degreewise section identification
commutes with this comparison, so the resulting homology equivalences satisfy
the displayed naturality equation. Homotopic lifts give equal maps on homology;
proof irrelevance removes dependence on hF and hG. On zero coefficients all
positive groups are zero. Empty schemes cause no exception to the resolution
argument. This assertion has no cohomology/Ext comparison in its conclusion. -/
theorem etaleZariskiDerivedSectionsAcyclicLeray
    (X : Scheme.{u}) (i : X.Opens ⥤ X.Etale)
    [i.IsContinuous (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology]
    [(i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits i] :
    let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
    let Z := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
    let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op (i.obj ⊤))
    ∃ c : ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) (n : ℕ),
        ((Z.rightDerived (n + 1)).obj (T.obj F)) ≃+
          ((E.rightDerived (n + 1)).obj F),
      ∀ (F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F))
        (hG : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj G))
        (φ : F ⟶ G) (n : ℕ) (x : (Z.rightDerived (n + 1)).obj (T.obj F)),
        c G hG n ((Z.rightDerived (n + 1)).map (T.map φ) x) =
          (E.rightDerived (n + 1)).map φ (c F hF n x) := by
  classical
  let T := i.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let Z := sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let E := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u}).obj (op (i.obj ⊤))
  let : T.PreservesInjectiveObjects := pushforward_injectives X i
  let : PreservesFiniteLimits T := by
    let : PreservesFiniteLimits (T ⋙
        sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :=
      show PreservesFiniteLimits (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj i.op) from inferInstance
    exact preservesFiniteLimits_of_reflects_of_preserves T
      (sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
  let I (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) := injectiveResolution F
  let P (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) :=
    mapResolution T (I F) (fun q hq ↦ by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
      exact hF n)
  let e : T ⋙ Z ≅ E := Iso.refl _
  let ec (n : ℕ) :=
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (.up ℕ))
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) n)
  let c (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (hF : ∀ n : ℕ, IsZero ((T.rightDerived (n + 1)).obj F)) (n : ℕ) :=
    (P F hF).isoRightDerivedObj Z (n + 1) ≪≫ (ec (n + 1)).app (I F).cocomplex ≪≫
      ((I F).isoRightDerivedObj E (n + 1)).symm
  refine ⟨fun F hF n ↦ (c F hF n).addCommGroupIsoToAddEquiv, ?_⟩
  intro F G hF hG φ n x
  have hc : (Z.rightDerived (n + 1)).map (T.map φ) ≫ (c G hG n).hom =
      (c F hF n).hom ≫ (E.rightDerived (n + 1)).map φ := by
    let f := InjectiveResolution.desc φ (I G) (I F)
    have hf : (P F hF).ι.f 0 ≫ ((T.mapHomologicalComplex (.up ℕ)).map f).f 0 =
        T.map φ ≫ (P G hG).ι.f 0 := by
      change T.map ((I F).ι.f 0) ≫ T.map (f.f 0) =
        T.map φ ≫ T.map ((I G).ι.f 0)
      rw [← T.map_comp, InjectiveResolution.desc_commutes_zero, T.map_comp]
    dsimp only [c, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [InjectiveResolution.isoRightDerivedObj_hom_naturality_assoc
      (T.map φ) (P F hF) (P G hG) ((T.mapHomologicalComplex (.up ℕ)).map f) hf Z,
      InjectiveResolution.isoRightDerivedObj_inv_naturality φ (I F) (I G) f
        (InjectiveResolution.desc_commutes_zero φ (I G) (I F)) E]
    congr 1
    exact (ec (n + 1)).hom.naturality_assoc f _
  exact ConcreteCategory.congr_hom hc x

end AlgebraicGeometry.Scheme.Modules
