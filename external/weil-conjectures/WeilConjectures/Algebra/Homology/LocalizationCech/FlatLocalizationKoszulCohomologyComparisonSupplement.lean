/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LocalizationCech.ExtendedLocalizationCechSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Flat comparison on torsion Koszul cohomology

Source: Stacks Project, Tags 099H, 0GLY and 05E9
(blueprint: lem-weil-pbc-flat-localization-koszul-cohomology-comparison).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules.LocalizationCech

private def scalarWord {D : Type*} [Category D] {r : ℕ}
    (s : Fin r → (𝟭 D ⟶ 𝟭 D)) : List (Fin r) → (𝟭 D ⟶ 𝟭 D)
  | [] => 𝟙 _
  | j :: l => s j ≫ scalarWord s l

private theorem exact_natTrans_nilpotent
    {D : Type*} [Category D] [Abelian D] (F : D ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (η : 𝟭 D ⟶ F) {r : ℕ} (s : Fin r → (𝟭 D ⟶ 𝟭 D))
    (base : ∀ M, (∀ j, (s j).app M = 0) → IsIso (η.app M))
    (k : ℕ) (M : D)
    (hk : ∀ l : List (Fin r), l.length = k → (scalarWord s l).app M = 0) :
    IsIso (η.app M) := by
  induction k generalizing M with
  | zero =>
    have hz : IsZero M := (IsZero.iff_id_eq_zero M).2 (hk [] rfl)
    exact hz.isIso (Functor.map_isZero F hz) _
  | succ k ih =>
    let t : (∐ fun _ : Fin r => M) ⟶ M := Sigma.desc (fun j => (s j).app M)
    have hQ : ∀ j, (s j).app (cokernel t) = 0 := by
      intro j
      apply (cancel_epi (cokernel.π t)).1
      rw [comp_zero]
      rw [show cokernel.π t ≫ (s j).app (cokernel t) =
          (s j).app M ≫ cokernel.π t from (s j).naturality (cokernel.π t)]
      change (s j).app M ≫ cokernel.π t = 0
      rw [← Sigma.ι_comp_desc (fun j => (s j).app M) j]
      change (Sigma.ι (fun _ : Fin r => M) j ≫ t) ≫ cokernel.π t = 0
      simp
    have hN : ∀ l : List (Fin r), l.length = k →
        (scalarWord s l).app (Abelian.image t) = 0 := by
      intro l hl
      apply (cancel_mono (Abelian.image.ι t)).1
      rw [zero_comp]
      rw [show (scalarWord s l).app (Abelian.image t) ≫ Abelian.image.ι t =
          Abelian.image.ι t ≫ (scalarWord s l).app M from
        ((scalarWord s l).naturality (Abelian.image.ι t)).symm]
      apply (cancel_epi (Abelian.factorThruImage t)).1
      rw [comp_zero, ← Category.assoc, Abelian.image.fac]
      apply Sigma.hom_ext
      intro j
      change Sigma.ι (fun _ : Fin r => M) j ≫ t ≫ (scalarWord s l).app M =
        Sigma.ι (fun _ : Fin r => M) j ≫ 0
      rw [← Category.assoc, Sigma.ι_comp_desc, comp_zero]
      exact hk (j :: l) (by simp [hl])
    have := ih (Abelian.image t) hN
    have := base (cokernel t) hQ
    let S := ShortComplex.kernelSequence (cokernel.π t)
    have hS : S.ShortExact :=
      { exact := ShortComplex.kernelSequence_exact _
        mono_f := inferInstance
        epi_g := by change Epi (cokernel.π t); infer_instance }
    have h₁ : IsIso (S.mapNatTrans η).τ₁ :=
      ih (Abelian.image t) hN
    have h₃ : IsIso (S.mapNatTrans η).τ₃ := base (cokernel t) hQ
    exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ (S.mapNatTrans η)
      (hS.map_of_exact (𝟭 D)) (hS.map_of_exact F)

private def centralScalar {D : Type*} [Category D] [MonoidalCategory D]
    (s : End (𝟙_ D)) : 𝟭 D ⟶ 𝟭 D :=
  (rightUnitorNatIso D).inv ≫ (tensoringRight D).map s.asHom ≫ (rightUnitorNatIso D).hom

private theorem tensor_unit_on_killed
    {D : Type*} [Category D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D]
    [∀ M : D, PreservesFiniteColimits (tensorLeft M)]
    {P : D} (u : 𝟙_ D ⟶ P) {r : ℕ} (s : Fin r → End (𝟙_ D))
    (hQ : IsIso (((rightUnitorNatIso D).inv ≫ (tensoringRight D).map u).app
      (cokernel (Sigma.desc (fun j ↦ (s j).asHom)))))
    (M : D) (hM : ∀ j, (centralScalar (s j)).app M = 0) :
    IsIso (((rightUnitorNatIso D).inv ≫ (tensoringRight D).map u).app M) := by
  let t := Sigma.desc (fun j ↦ (s j).asHom)
  let Q := cokernel t
  let η : 𝟭 D ⟶ tensorRight P :=
    (rightUnitorNatIso D).inv ≫ (tensoringRight D).map u
  have ht : (tensorLeft M).map t = 0 := by
    apply (cancel_epi (sigmaComparison (tensorLeft M) (fun _ : Fin r => 𝟙_ D))).1
    apply Sigma.hom_ext
    intro j
    dsimp only [t]
    simp only [ι_comp_sigmaComparison_assoc, ← Functor.map_comp, Sigma.ι_comp_desc,
      comp_zero]
    have h := hM j
    change (ρ_ M).inv ≫ M ◁ (s j).asHom ≫ (ρ_ M).hom = 0 at h
    apply (cancel_epi (ρ_ M).inv).1
    apply (cancel_mono (ρ_ M).hom).1
    simpa using h
  have hp : IsIso (M ◁ cokernel.π t) :=
    CokernelCofork.IsColimit.isIso_π _
      (CokernelCofork.mapIsColimit _ (cokernelIsCokernel t) (tensorLeft M)) ht
  have hMQ : IsIso (η.app (M ⊗ Q)) := by
    have : IsIso (η.app Q) := hQ
    have he : η.app (M ⊗ Q) =
        M ◁ (η.app Q) ≫ (α_ M Q P).inv := by
      change (ρ_ (M ⊗ Q)).inv ≫ (M ⊗ Q) ◁ u = _
      change (ρ_ (M ⊗ Q)).inv ≫ (M ⊗ Q) ◁ u =
        M ◁ ((ρ_ Q).inv ≫ Q ◁ u) ≫ (α_ M Q P).inv
      rw [whiskerLeft_comp, Category.assoc, associator_inv_naturality_right,
        ← Category.assoc, whiskerLeft_rightUnitor_inv]
      simp
    rw [he]
    infer_instance
  let a : M ⟶ M ⊗ Q := (ρ_ M).inv ≫ M ◁ cokernel.π t
  have : IsIso a := inferInstance
  have h : a ≫ η.app (M ⊗ Q) = η.app M ≫ (tensorRight P).map a := η.naturality a
  have : IsIso (η.app M ≫ (tensorRight P).map a) := by rw [← h]; infer_instance
  exact IsIso.of_isIso_comp_right _ ((tensorRight P).map a)

private noncomputable def sectionScalar
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections) :
    𝟭 (CategoryTheory.ringedSiteModules.{u} (rings R)) ⟶ 𝟭 _ where
  app M :=
    ⟨{ app := fun U => ModuleCat.ofHom
          (LinearMap.lsmul (R.obj.obj U) (M.val.obj U) (s.val U))
       naturality := by
         intro U V i
         apply ModuleCat.hom_ext
         apply LinearMap.ext
         intro x
         change (show R.obj.obj V from s.val V) •
           (show M.val.obj V from M.val.map i x) =
             M.val.map i ((show R.obj.obj U from s.val U) • x)
         rw [M.val.map_smul]
         exact congrArg (fun a : R.obj.obj V ↦ a •
           (show M.val.obj V from M.val.map i x)) (s.property i).symm }⟩
  naturality {M N} a := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ((a.val.app U).hom.map_smul (s.val U) x).symm

private theorem monoidal_counit_rightUnitor
    {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
    (F : D ⥤ E) [F.Monoidal] {X : D} {M : E} (e : F.obj X ≅ M)
    (e₀ : F.obj (𝟙_ D) ≅ 𝟙_ E) (h₀ : e₀.inv = Functor.LaxMonoidal.ε F) :
    (e.inv ⊗ₘ e₀.inv) ≫ Functor.LaxMonoidal.μ F X (𝟙_ D) ≫
      F.map (ρ_ X).hom ≫ e.hom = (ρ_ M).hom := by
  rw [tensorHom_def, Category.assoc, h₀,
    ← Functor.LaxMonoidal.right_unitality_assoc, rightUnitor_naturality_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_rightUnitor_hom
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (M : CategoryTheory.ringedSiteModules.{u} (rings R)) :
    let := monoidalCategory R
    let S := PresheafOfModules.sheafification (𝟙 (rings R).obj)
    let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (rings R).obj)).counit
    (tensorObjIsoSheafification M (unit (rings R))).hom ≫
      S.map (ρ_ M.val).hom ≫ ε.app M = (ρ_ M).hom := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification (𝟙 (rings R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (rings R).obj)).counit
  exact monoidal_counit_rightUnitor S ((asIso ε).app M)
    ((asIso ε).app (unit (rings R))) rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sectionScalar_central
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections)
    (M : CategoryTheory.ringedSiteModules.{u} (rings R)) :
    let := monoidalCategory R
    (centralScalar (scalar R s)).app M = (sectionScalar R s).app M := by
  let := monoidalCategory R
  let S := PresheafOfModules.sheafification (𝟙 (rings R).obj)
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (rings R).obj)).counit
  have hpre : M.val ◁ (scalar R s).asHom.val ≫ (ρ_ M.val).hom =
      (ρ_ M.val).hom ≫ ((sectionScalar R s).app M).val := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x a
    change R.obj.obj U at a
    change (a * (show R.obj.obj U from s.val U)) • x =
      (show R.obj.obj U from s.val U) • (a • x)
    rw [mul_smul, smul_comm]
  change (ρ_ M).inv ≫ M ◁ (scalar R s).asHom ≫ (ρ_ M).hom = _
  apply (cancel_epi (ρ_ M).hom).1
  simp only [Iso.hom_inv_id_assoc]
  rw [← tensor_rightUnitor_hom R M]
  erw [whiskerLeft_tensorObjIsoSheafification_hom_assoc (R := R) M (scalar R s).asHom]
  rw [← Functor.map_comp_assoc, hpre, Functor.map_comp]
  have hε := ε.naturality ((sectionScalar R s).app M)
  change S.map ((sectionScalar R s).app M).val ≫ ε.app M =
    ε.app M ≫ (sectionScalar R s).app M at hε
  simpa only [Category.assoc] using congrArg
    (fun a => (tensorObjIsoSheafification M (unit (rings R))).hom ≫
      S.map (ρ_ M.val).hom ≫ a) hε

private theorem centralScalar_left
    {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D]
    (s : End (𝟙_ D)) (M : D) :
    s.asHom ▷ M ≫ (λ_ M).hom = (λ_ M).hom ≫ (centralScalar s).app M := by
  change s.asHom ▷ M ≫ (λ_ M).hom =
    (λ_ M).hom ≫ ((ρ_ M).inv ≫ M ◁ s.asHom ≫ (ρ_ M).hom)
  rw [← braiding_rightUnitor M]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact BraidedCategory.braiding_naturality_left_assoc s.asHom M (ρ_ M).hom

private theorem scalar_leftUnitor
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (s : (unit (rings R)).sections)
    (M : CategoryTheory.ringedSiteModules.{u} (rings R)) :
    letI := monoidalCategory R
    (scalar R s).asHom ▷ M ≫ (λ_ M).hom = (λ_ M).hom ≫ (sectionScalar R s).app M := by
  let := monoidalCategory R
  let := symmetricCategory R
  exact (centralScalar_left (scalar R s) M).trans
    (congrArg ((λ_ M).hom ≫ ·) (sectionScalar_central R s M))

private theorem restriction_colimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesColimitsOfSize.{u, u} (restriction φ) := by
  have h (S : Sheaf J RingCat.{u}) :
      PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} S) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful S).2.2.2.2.2 K).2.1
  have := h (rings R)
  have := h (rings B)
  have : ReflectsColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (rings R)) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u}
      (restriction φ ⋙ SheafOfModules.toSheaf.{u} (rings R)) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.toSheaf.{u} (rings B)))
  exact preservesColimits_of_reflects_of_preserves _ (SheafOfModules.toSheaf.{u} (rings R))

private theorem sectionScalar_word_zero
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (r : ℕ)
    (f : Fin r → (unit (rings R)).sections) (k : ℕ)
    (M : CategoryTheory.ringedSiteModules.{u} (rings R))
    (hkill : ∀ (X : Cᵒᵖ) (a : R.obj.obj X),
      a ∈ (Ideal.span (Set.range (fun j : Fin r =>
        (show R.obj.obj X from (f j).val X)))) ^ k →
      ∀ (x : M.val.obj X), a • x = 0) :
    ∀ l : List (Fin r), l.length = k →
      (scalarWord (fun j => sectionScalar R (f j)) l).app M = 0 := by
  let s := fun j : Fin r => sectionScalar R (f j)
  intro l hl
  have hw : ∀ (l : List (Fin r)) (X : Cᵒᵖ) (x : M.val.obj X),
      ((scalarWord s l).app M).val.app X x =
        (l.map (fun j => (show R.obj.obj X from (f j).val X))).prod • x := by
    intro l
    induction l with
    | nil => intro X x; simp [scalarWord]
    | cons j l ih =>
      intro X x
      change ((scalarWord s l).app M).val.app X
        ((show R.obj.obj X from (f j).val X) • x) = _
      rw [ih]
      simp only [List.map_cons, List.prod_cons, mul_smul]
      exact smul_comm _ _ _
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((scalarWord s l).app M).val.app X x = 0
  rw [hw]
  apply hkill X _ ?_ x
  have hm : ∀ l : List (Fin r),
      (l.map (fun j => (show R.obj.obj X from (f j).val X))).prod ∈
        (Ideal.span (Set.range (fun j : Fin r =>
          (show R.obj.obj X from (f j).val X)))) ^ l.length := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self j)) ih
  simpa only [hl] using hm l

end SheafOfModules.LocalizationCech
