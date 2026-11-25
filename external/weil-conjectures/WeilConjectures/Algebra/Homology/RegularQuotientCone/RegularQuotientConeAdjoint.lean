/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeAugmentation
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Adjoint formula for the normalized regular quotient cone

Source: Stacks 06YY and 07A6, normalized derived tensor adjunction.
(blueprint: lem-cbc-regular-quotient-cone-adjoint).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v r wR wS
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings
namespace SheafOfModules.RegularQuotientCone

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  [HasDerivedCategory.{wR} (Modules R)] [HasDerivedCategory.{wS} (Modules S)]
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
  (d : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
  (b : Augmentation φ t d)

local instance {A : Sheaf J CommRingCat.{r}} (M : Modules A) (U : Cᵒᵖ) :
    Module (A.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule

private theorem ordinary_unit
    (o : d.E ⊣ restriction φ)
    (ho : ∀ (M : Modules R) (N : Modules S) (f : changeOfRings φ M ⟶ N)
      (U : Cᵒᵖ) (x : M.val.obj U),
      (o.homEquiv M N (eqToHom (d.obj_eq M) ≫ f)).val.app U x =
        f.val.app U ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(φ.hom.app U).hom] x)))
    (P : CochainComplex (Modules R) ℤ) :
    ((o.mapHomologicalComplex (.up ℤ)).unit.app P) = b.ρ.app P := by
  apply HomologicalComplex.hom_ext
  intro q
  ext U x
  have h := ho (P.X q) (changeOfRings φ (P.X q)) (𝟙 _) U x
  simp only [Category.comp_id, Adjunction.homEquiv_unit] at h
  have hb := b.ρ_sections P q U x
  let F := SheafOfModules.evaluation (derivedChangeRingIndependentCoefficients J S) U
  have hi : IsIso (F.map (eqToHom (d.obj_eq (P.X q)))) := inferInstance
  apply (ConcreteCategory.bijective_of_isIso (F.map (eqToHom (d.obj_eq (P.X q))))).1
  change (eqToHom (d.obj_eq (P.X q))).val.app U
    ((o.unit.app (P.X q)).val.app U x) = _
  have he := o.homEquiv_naturality_right (𝟙 (d.E.obj (P.X q)))
    (eqToHom (d.obj_eq (P.X q)))
  simp only [Category.id_comp, Adjunction.homEquiv_id] at he
  have hs := congrArg (fun f ↦ f.val.app U x) he
  exact hs.symm.trans (h.trans hb.symm)

/-- The normalized cone augmentation is the restricted derived adjoint of a strict
map to a quotient complex. The equation fixes the nullhomotopy to be zero.

Source: Stacks 06YY and 07A6, normalization of derived tensor on resolutions
(blueprint: lem-cbc-regular-quotient-cone-adjoint).

Proof: use the normalized ordinary tensor adjunction to transpose f to g. Its unit
is b.rho by the section formula. On a K-flat source, the universal counit followed
by Q(g) is the derived adjoint of Q(f), by the unit normalization. The component
formula for b.A identifies its restriction with the strict cone map whose shifted
component is zero and whose unshifted component is f. For an arbitrary source,
choose a K-flat resolution and precompose both sides by its invertible derived
tensor image. Naturality of b.A, of the cone factor, and of the adjunction reduces
the equation to that K-flat case. No boundedness or fullness of derived restriction
is used. -/
theorem augmentation_adjoint
    (P : CochainComplex (Modules R) ℤ) (N : CochainComplex (Modules S) ℤ)
    (f : P ⟶ ((restriction φ).mapHomologicalComplex (.up ℤ)).obj N)
    (hf : (complexScalar R t).app P ≫ f = 0) :
    b.V.map ((b.adjunction.homEquiv (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj N)).symm
      (DerivedCategory.Q.map f ≫ b.restriction_factor.inv.app N)) =
      b.A.inv.app (DerivedCategory.Q.obj P) ≫ b.cone_factor.hom.app P ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.desc
          ((complexScalar R t).app P) 0 f (by simp [hf])) ≫
        b.restriction_factor.inv.app N := by
  classical
  obtain ⟨hlim, hcol, ho⟩ := sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨o, ho⟩ := ho d.E d.obj_eq d.map_eq
  let O := o.mapHomologicalComplex (.up ℤ)
  let Vc := (restriction φ).mapHomologicalComplex (.up ℤ)
  have hρ : ∀ K, O.unit.app K = b.ρ.app K := ordinary_unit φ t d b o ho
  have hgood (K : CochainComplex (Modules R) ℤ)
      (hK : CochainComplex.IsKFlatIndependentCoefficients (R := R) K)
      (a : K ⟶ Vc.obj N) (ha : (complexScalar R t).app K ≫ a = 0) :
      b.V.map ((b.adjunction.homEquiv (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj N)).symm
        (DerivedCategory.Q.map a ≫ b.restriction_factor.inv.app N)) =
      b.A.inv.app (DerivedCategory.Q.obj K) ≫ b.cone_factor.hom.app K ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.desc
          ((complexScalar R t).app K) 0 a (by simp [ha])) ≫
        b.restriction_factor.inv.app N := by
    let g := (O.homEquiv K N).symm a
    have hg : b.ρ.app K ≫ Vc.map g = a := by
      rw [← hρ]
      exact (Adjunction.homEquiv_unit O K N g).symm.trans
        ((O.homEquiv K N).apply_symm_apply a)
    have hadj : (b.adjunction.homEquiv (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj N)) (d.ε.app K ≫ DerivedCategory.Q.map g) =
        DerivedCategory.Q.map a ≫ b.restriction_factor.inv.app N := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp]
      apply (cancel_mono (b.restriction_factor.hom.app N)).1
      simp only [Category.assoc, Iso.inv_hom_id_app]
      have hn : b.V.map (DerivedCategory.Q.map g) ≫ b.restriction_factor.hom.app N =
          b.restriction_factor.hom.app _ ≫ DerivedCategory.Q.map (Vc.map g) :=
        b.restriction_factor.hom.naturality g
      rw [hn]
      dsimp only [Functor.comp_obj]
      have hh := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map (Vc.map g))
        (b.unit_normalization K hK)
      have hh' : b.adjunction.unit.app (DerivedCategory.Q.obj K) ≫
          b.V.map (d.ε.app K) ≫ b.restriction_factor.hom.app _ ≫
          DerivedCategory.Q.map (Vc.map g) = DerivedCategory.Q.map a := by
        simpa only [Category.assoc, ← DerivedCategory.Q.map_comp, hg] using hh
      exact hh'.trans (Category.comp_id _).symm
    rw [← hadj, Equiv.symm_apply_apply, Functor.map_comp]
    have hcone : b.a.app K ≫ Vc.map g =
        CochainComplex.mappingCone.desc ((complexScalar R t).app K) 0 a
          (by simp [ha]) := by
      apply HomologicalComplex.hom_ext
      intro q
      rw [HomologicalComplex.comp_f, b.a_components]
      rw [CochainComplex.mappingCone.desc_f _ _ _ _ q (q + 1) rfl]
      simpa only [cone, CochainComplex.HomComplex.Cochain.zero_v, comp_zero,
        zero_add, Category.assoc, HomologicalComplex.comp_f] using
        congrArg (fun z ↦
          (CochainComplex.mappingCone.snd ((complexScalar R t).app K)).v q q
            (add_zero q) ≫ z.f q) hg
    apply (cancel_epi (b.A.hom.app (DerivedCategory.Q.obj K))).1
    simp only [Iso.hom_inv_id_app_assoc]
    apply (cancel_mono (b.restriction_factor.hom.app N)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    have hn : b.V.map (DerivedCategory.Q.map g) ≫ b.restriction_factor.hom.app N =
        b.restriction_factor.hom.app _ ≫ DerivedCategory.Q.map (Vc.map g) :=
      b.restriction_factor.hom.naturality g
    rw [hn]
    dsimp only [Functor.comp_obj]
    have hh := congrArg (fun z ↦ z ≫ DerivedCategory.Q.map (Vc.map g))
      (b.A_components K hK)
    have hh' : b.A.hom.app (DerivedCategory.Q.obj K) ≫
        b.V.map (d.ε.app K) ≫ b.restriction_factor.hom.app _ ≫
        DerivedCategory.Q.map (Vc.map g) = b.cone_factor.hom.app K ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.desc ((complexScalar R t).app K) 0 a
          (by simp [ha])) := by
      simpa only [Category.assoc, ← DerivedCategory.Q.map_comp, hcone] using hh
    exact hh'.trans (by rw [Category.comp_id])
  obtain ⟨K, q, hK, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
  have : QuasiIso q := hq
  have hi : IsIso ((d.T ⋙ b.V).map (DerivedCategory.Q.map q)) := inferInstance
  apply (cancel_epi ((d.T ⋙ b.V).map (DerivedCategory.Q.map q))).1
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp, ← b.adjunction.homEquiv_naturality_left_symm]
  simp only [← Category.assoc, ← DerivedCategory.Q.map_comp]
  simp only [Category.assoc]
  have ha : (complexScalar R t).app K ≫ (q ≫ f) = 0 := by
    have hn : (complexScalar R t).app K ≫ q = q ≫ (complexScalar R t).app P :=
      ((complexScalar R t).naturality q).symm
    rw [← Category.assoc, hn, Category.assoc, hf, comp_zero]
  rw [hgood K hK (q ≫ f) ha]
  have hn : b.V.map (d.T.map (DerivedCategory.Q.map q)) ≫
      b.A.inv.app (DerivedCategory.Q.obj P) =
      b.A.inv.app (DerivedCategory.Q.obj K) ≫ b.D.map (DerivedCategory.Q.map q) :=
    b.A.inv.naturality (DerivedCategory.Q.map q)
  rw [reassoc_of% hn]
  have hc : b.D.map (DerivedCategory.Q.map q) ≫ b.cone_factor.hom.app P =
      b.cone_factor.hom.app K ≫ DerivedCategory.Q.map ((cone R t).map q) :=
    b.cone_factor.hom.naturality q
  rw [reassoc_of% hc]
  dsimp only [cone] at *
  simp only [← DerivedCategory.Q.map_comp_assoc]
  congr 2
  apply congrArg (fun z ↦ DerivedCategory.Q.map z ≫ b.restriction_factor.inv.app N)
  apply HomologicalComplex.hom_ext
  intro j
  apply CochainComplex.mappingCone.ext_from _ (j + 1) j rfl <;>
    simp [CochainComplex.mappingCone.map, HomologicalComplex.comp_f]

end SheafOfModules.RegularQuotientCone
