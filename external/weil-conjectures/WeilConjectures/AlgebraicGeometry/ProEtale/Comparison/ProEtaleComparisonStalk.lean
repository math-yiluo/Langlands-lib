/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic

set_option linter.privateModule false

/-!
# Etale-to-pro-etale comparison on geometric stalks

## References

* Stacks Project, Pro-etale Cohomology, Tags 0GLZ and 0993
* Sites, Tag 05V1
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem comparison_cover_lift
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {V : T.ProEt} (R : Sieve V) (hR : R ∈ ProEt.topology T V)
    (v : Spec (.of Ω) ⟶ V.left) :
    ∃ (W : T.ProEt) (g : W ⟶ V) (_ : R g) (w : Spec (.of Ω) ⟶ W.left),
      w ≫ g.left = v := by
  obtain ⟨S, hS, hSR⟩ := ProEt.mem_topology_iff.1 hR
  obtain ⟨ι, Z, f, rfl⟩ := S.exists_eq_ofArrows
  have hS' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage V.left := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst] using hS
  have hb := Precoverage.mem_coverings_of_isPullback (fun i ↦ (f i).left) hS' v
    (fun i ↦ pullback.snd (f i).left v) (fun i ↦ pullback.fst (f i).left v)
    (fun i ↦ (IsPullback.of_hasPullback (f i).left v).flip)
  obtain ⟨i, z, hz⟩ :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hb)).1
      (IsLocalRing.closedPoint Ω)
  have : WeaklyEtale (f i).left :=
    ((ofArrows_mem_precoverage_iff _).1 (propQCPrecoverage_le_precoverage _ hS')).2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale
    (pullback.snd (f i).left v) z
  refine ⟨Z i, f i, hSR _ _ ⟨i⟩, σ ≫ pullback.fst (f i).left v, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]

private noncomputable def comparisonPoint
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) : (ProEt.topology T).Point.{u + 1} where
  fiber := (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))) ⋙ uliftFunctor.{u + 1}
  isCofiltered := by
    have : IsCofiltered (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t))).Elements :=
      Functor.isCofiltered_elements _
    exact .of_equivalence
      (Functor.Elements.uliftEquivalence.{u + 1}
        (ProEt.forget T ⋙ coyoneda.obj (op (Over.mk t)))).symm
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨W, g, hg, w, hw⟩ := comparison_cover_lift R hR x.down.left
    refine ⟨W, g, hg, ULift.up (Over.homMk w ?_), ?_⟩
    · change w ≫ W.hom = t
      rw [← MorphismProperty.Over.w g, ← Category.assoc, hw]
      exact Over.w x.down
    · apply ULift.ext
      apply Over.OverMorphism.ext
      exact hw

end AlgebraicGeometry.Scheme
