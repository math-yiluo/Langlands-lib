/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.AlgebraicGeometry.PerfectTensorHomDuality
import WeilConjectures.CategoryTheory.MonoidalProjectionConjugate
import WeilConjectures.AlgebraicGeometry.PerfectRightAdjointTensorHomComparison
import Mathlib.CategoryTheory.Yoneda
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
private theorem projection_isIso
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) (R : D ⥤ C) [F.Monoidal] (a : F ⊣ R)
    (K L : C) [ExactPairing K L] (E : D) :
    IsIso ((a.homEquiv _ _)
      ((Functor.Monoidal.μIso F K (R.obj E)).inv ≫ F.obj K ◁ a.counit.app E)) := by
  let := ExactPairing.map F K L
  let b₁ := (tensorLeftAdjunction K L).comp a
  let b₂ := a.comp (tensorLeftAdjunction (F.obj K) (F.obj L))
  let p := conjugateEquiv b₁ b₂ (Functor.Monoidal.commTensorLeft F L).hom
  have : IsIso (p.app E) := inferInstance
  have hp := monoidal_projection_conjugate F R a K L E
  change p.app E = _ at hp
  rw [← hp]
  infer_instance

/-- Intermediate perfect comparison clause. Source: Stacks Tag 0A9T.
(blueprint: lem-sc-smooth-proper-tensor-perfect-case-core). -/
theorem smoothProper_tensor_perfect_case_core
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings Y.toRingedSpace).over U))]
    (hRf : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E.obj))
    (hO : schemeDerivedQCohProperty Y (𝟙_ (schemeDerivedCategory Y)))
    (hTensor : ∀ (K : schemeDerivedQCohCategory Y)
      (E : schemeDerivedQCohCategory X),
      schemeDerivedQCohProperty X (((derivedPullback f).obj K.obj) ⊗ E.obj)) :
        ∀ (_ : Functor.Monoidal (derivedPullback f))
        (a : derivedPullback f ⊣ schemeDerivedDirectImage f)
        (c : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
        (adj : (schemeDerivedQCohProperty Y).lift
          ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hRf ⊣ c)
        (K : schemeDerivedQCohCategory Y), Scheme.IsPerfect Y K.obj →
        ∃ pf : (schemeDerivedDirectImage f).obj
            (((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj) ≅
          K.obj ⊗ (schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj,
          pf.inv = (a.homEquiv _ _)
            ((Functor.Monoidal.μIso (derivedPullback f) K.obj
              ((schemeDerivedDirectImage f).obj (c.obj ⟨𝟙_ _, hO⟩).obj)).inv ≫
              (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj ⟨𝟙_ _, hO⟩).obj) ∧
          IsIso ((adj.homEquiv
            ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj ⟨𝟙_ _, hO⟩).obj,
              hTensor K (c.obj ⟨𝟙_ _, hO⟩)⟩ K)
            (ObjectProperty.homMk (pf.hom ≫
              K.obj ◁ (adj.counit.app ⟨𝟙_ _, hO⟩).hom ≫ (ρ_ K.obj).hom))) := by
  intro m a c adj K hK
  let := m
  obtain ⟨D, ⟨pairKD⟩, ⟨pairDK⟩, _, _, _, _⟩ := perfect_tensor_hom_duality Y K hK
  let := pairKD
  let := pairDK
  let := ExactPairing.map (derivedPullback f) K.obj D.obj
  let O : schemeDerivedQCohCategory Y := ⟨𝟙_ _, hO⟩
  let pf : ∀ (J : schemeDerivedQCohCategory Y) [ExactPairing J.obj K.obj]
      (E : schemeDerivedQCohCategory X),
      (schemeDerivedDirectImage f).obj (((derivedPullback f).obj J.obj) ⊗ E.obj) ≅
        J.obj ⊗ (schemeDerivedDirectImage f).obj E.obj := fun J _ E ↦ by
    have := projection_isIso (derivedPullback f) (schemeDerivedDirectImage f)
      a J.obj K.obj E.obj
    exact (asIso ((a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) J.obj
        ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
        (derivedPullback f).obj J.obj ◁ a.counit.app E.obj))).symm
  have hpf : ∀ (J : schemeDerivedQCohCategory Y) [ExactPairing J.obj K.obj]
      (E : schemeDerivedQCohCategory X), (pf J E).inv = (a.homEquiv _ _)
      ((Functor.Monoidal.μIso (derivedPullback f) J.obj
        ((schemeDerivedDirectImage f).obj E.obj)).inv ≫
        (derivedPullback f).obj J.obj ◁ a.counit.app E.obj) := by
    intro J _ E
    rfl
  have hpK := projection_isIso (derivedPullback f) (schemeDerivedDirectImage f)
    a K.obj D.obj (c.obj O).obj
  let pfK := (asIso ((a.homEquiv _ _)
    ((Functor.Monoidal.μIso (derivedPullback f) K.obj
      ((schemeDerivedDirectImage f).obj (c.obj O).obj)).inv ≫
      (derivedPullback f).obj K.obj ◁ a.counit.app (c.obj O).obj))).symm
  refine ⟨pfK, rfl, ?_⟩
  apply isIso_of_yoneda_map_bijective
  intro E
  let T : schemeDerivedQCohCategory X :=
    ⟨((derivedPullback f).obj D.obj) ⊗ E.obj, hTensor D E⟩
  let S : schemeDerivedQCohCategory X :=
    ⟨((derivedPullback f).obj K.obj) ⊗ (c.obj O).obj, hTensor K (c.obj O)⟩
  let e : (E ⟶ S) ≃ (E ⟶ c.obj K) :=
    (schemeDerivedQCohProperty X).fullyFaithfulι.homEquiv.trans
      ((tensorLeftHomEquiv E.obj ((derivedPullback f).obj K.obj)
        ((derivedPullback f).obj D.obj) (c.obj O).obj).symm.trans
        ((schemeDerivedQCohProperty X).fullyFaithfulι.homEquiv.symm.trans
          ((adj.homEquiv T O).symm.trans
            ((schemeDerivedQCohProperty Y).fullyFaithfulι.homEquiv.trans
              ((Iso.homCongr (pf D E) (Iso.refl O.obj)).trans
                ((tensorLeftHomEquiv ((schemeDerivedDirectImage f).obj E.obj)
                  K.obj D.obj O.obj).trans
                  ((Iso.homCongr (Iso.refl _) (ρ_ K.obj)).trans
                    ((schemeDerivedQCohProperty Y).fullyFaithfulι.homEquiv.symm.trans
                      (adj.homEquiv E K)))))))))
  have he : ∀ q : E ⟶ S, e q = q ≫ (adj.homEquiv S K)
      (ObjectProperty.homMk (pfK.hom ≫
        K.obj ◁ (adj.counit.app O).hom ≫ (ρ_ K.obj).hom)) := by
    intro q
    have hh := perfect_rightAdjoint_tensor_hom_comparison f hRf hO hTensor a c adj
      K D E pfK rfl (pf D E) (hpf D E) q
    dsimp only at hh
    simp only [e, O, T, S, Equiv.trans_apply, Iso.homCongr,
      Functor.FullyFaithful.homEquiv, ObjectProperty.ι_map,
      Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp, Category.comp_id]
    convert hh using 1
  have hf : (fun q : E ⟶ S ↦ q ≫ (adj.homEquiv S K)
      (ObjectProperty.homMk (pfK.hom ≫
        K.obj ◁ (adj.counit.app O).hom ≫ (ρ_ K.obj).hom))) = e := by
    funext q
    exact (he q).symm
  rw [hf]
  exact e.bijective
end AlgebraicGeometry
