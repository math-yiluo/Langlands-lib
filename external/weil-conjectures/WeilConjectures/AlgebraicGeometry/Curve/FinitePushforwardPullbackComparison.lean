/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import WeilConjectures.AlgebraicGeometry.EtaleEdgeMapBaseChange
import WeilConjectures.SixFunctors.Finite.BaseChange
import Mathlib.CategoryTheory.Whiskering

/-! # Finite pushforward comparison for curve assertions

Source: Stacks Project, Lemma 0A5D (lemma-finite-pushforward-statements).
(blueprint: g1-finite-pushforward-pullback-comparison)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private noncomputable def coefficientRoundTrip (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      AddCommGrpCat.{u + 1})).obj ((sheafCompose _ E).obj F) ≅ F := by
  dsimp only
  apply ObjectProperty.isoMk
  exact Functor.isoWhiskerLeft F.obj (forget₂ (ModuleCat.{u + 1} ℤ)
    AddCommGrpCat.{u + 1}).asEquivalence.counitIso

private theorem comparison_properties {A B C D : Type*}
    (l : A → B) (r : C → D) (w : A → C) (v : B → D)
    (hl : Function.Bijective l) (hr : Function.Bijective r)
    (comm : v ∘ l = r ∘ w) :
    (Function.Bijective w ↔ Function.Bijective v) ∧
    (Function.Surjective w ↔ Function.Surjective v) := by
  constructor
  · rw [← hr.of_comp_iff' w, ← comm, hl.of_comp_iff v]
  · constructor
    · intro hw
      exact Function.Surjective.of_comp (comm.symm ▸ hr.surjective.comp hw)
    · intro hv
      exact (Function.Surjective.of_comp_iff' hr w).mp (comm ▸ hv.comp hl.surjective)

private theorem bijective_H_map_iso {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    Function.Bijective (Sheaf.H.map e.hom q) := by
  constructor
  · intro x y h
    have hh := congrArg (Sheaf.H.map e.inv q) h
    simpa only [← Sheaf.H.map_comp_apply, Iso.hom_inv_id, Sheaf.H.map_id_apply] using hh
  · intro y
    refine ⟨Sheaf.H.map e.inv q y, ?_⟩
    rw [← Sheaf.H.map_comp_apply, Iso.inv_hom_id, Sheaf.H.map_id_apply]

private theorem pullback_properties_iso {X Y : Scheme.{u}} (a : X ⟶ Y)
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    (Function.Bijective (Etale.cohomologyMap a F q) ↔
      Function.Bijective (Etale.cohomologyMap a G q)) ∧
    (Function.Surjective (Etale.cohomologyMap a F q) ↔
      Function.Surjective (Etale.cohomologyMap a G q)) := by
  apply comparison_properties (Sheaf.H.map e.hom q)
    (Sheaf.H.map ((Etale.upperStar AddCommGrpCat.{u + 1} a).mapIso e).hom q)
    (Etale.cohomologyMap a F q) (Etale.cohomologyMap a G q)
    (bijective_H_map_iso e q)
    (bijective_H_map_iso ((Etale.upperStar AddCommGrpCat.{u + 1} a).mapIso e) q)
  funext x
  exact Etale.cohomologyMap_map a q e.hom x

private theorem finite_pullback_properties
    {X' X Y' Y : Scheme.{u}} {b : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {a : Y' ⟶ Y} [IsFinite f] (sq : IsPullback b f' f a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    (Function.Bijective (Etale.cohomologyMap a
        ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F) q) ↔
      Function.Bijective (Etale.cohomologyMap b F q)) ∧
    (Function.Surjective (Etale.cohomologyMap a
        ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj F) q) ↔
      Function.Surjective (Etale.cohomologyMap b F q)) := by
  have : IsIso ((Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app F) := by
    have := Etale.isIso_baseChangeMap_of_isFinite AddCommGrpCat.{u + 1} sq
    infer_instance
  obtain ⟨hl, hr⟩ := Etale.bijective_edgeMap_baseChange sq F q inferInstance
  apply comparison_properties _ _ _ _ hl hr
  exact congrArg DFunLike.coe (Etale.cohomology_edgeMap_baseChange sq F q)

/-- Source: Stacks Project, Lemma 0A5D, base-change and restriction steps
(blueprint: g1-finite-pushforward-pullback-comparison).
Proof: the finite edge maps for f and its base change are bijective. Finite exchange is
an isomorphism, hence induces a bijection on cohomology. The edge-map base-change identity
identifies the two pullback maps through these bijections. Conjugation by bijections
preserves bijectivity and surjectivity. The equivalence of coefficient categories induces
isomorphisms of underlying abelian sheaves and commutes with pullback, so it gives the
same identity for the converted coefficient sheaves. No curve condition on the scheme
pulled back to is needed, so this applies to opens as well as field extensions. -/
theorem IsCurve.finite_pushforward_pullback_comparison {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (f : P.C ⟶ Y) [IsFinite f]
    (_hf : f ≫ g = P.toSpec) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
    let FY := (sheafCompose Y.smallEtaleTopology E).obj G
    ∀ {X' Y' : Scheme.{u}} {b : X' ⟶ P.C} {f' : X' ⟶ Y'} {a : Y' ⟶ Y},
      IsPullback b f' f a → ∀ q : ℕ,
      (Function.Bijective (Etale.cohomologyMap a
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
            AddCommGrpCat.{u + 1})).obj FY) q) ↔
        Function.Bijective (Etale.cohomologyMap b
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
            AddCommGrpCat.{u + 1})).obj FX) q)) ∧
      (Function.Surjective (Etale.cohomologyMap a
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
            AddCommGrpCat.{u + 1})).obj FY) q) ↔
        Function.Surjective (Etale.cohomologyMap b
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
            AddCommGrpCat.{u + 1})).obj FX) q)) := by
  dsimp only
  intro X' Y' b f' a sq q
  have hy := pullback_properties_iso a
    (coefficientRoundTrip Y ((Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F)) q
  have hx := pullback_properties_iso b (coefficientRoundTrip P.C P.F) q
  have h := finite_pullback_properties sq P.F q
  exact ⟨hy.1.trans (h.1.trans hx.1.symm), hy.2.trans (h.2.trans hx.2.symm)⟩

end AlgebraicGeometry
