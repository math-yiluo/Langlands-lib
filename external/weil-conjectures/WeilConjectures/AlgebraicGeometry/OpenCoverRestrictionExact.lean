/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Exactness of complexes of module sheaves on a union of opens

Source: Stacks Project, Modules, Tag 01AG.
(blueprint: lem-r4-open-cover-restriction-exact).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

private theorem isZero_over_of_open_cover
    (X : Scheme.{u}) (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (ι : Type v) (V : ι → X.Opens) (U : X.Opens) (hU : U = ⨆ i, V i)
    (h : ∀ i, IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (V i)).obj M)) :
    IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).obj M) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext W x
  change x = 0
  let W' : X.Opens := W.unop.left
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.val.presheaf, M.isSheaf⟩
    (fun i ↦ W' ⊓ V i) W' (fun i ↦ homOfLE inf_le_left) ?_ x 0 ?_
  · intro y hy
    have hyU : y ∈ U := (leOfHom W.unop.hom) hy
    rw [hU] at hyU
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hyU
    exact Opens.mem_iSup.mpr ⟨i, hy, hi⟩
  · intro i
    let T : Over (V i) := Over.mk (homOfLE (inf_le_right : W' ⊓ V i ≤ V i))
    let : (SheafOfModules.evaluation ((moduleRings X.toRingedSpace).over (V i))
        (Opposite.op T)).Additive :=
      inferInstanceAs (SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (Opposite.op T)).Additive
    have hz := (SheafOfModules.evaluation _ (Opposite.op T)).map_isZero (h i)
    have : Subsingleton (M.val.obj (Opposite.op (W' ⊓ V i))) :=
      ModuleCat.subsingleton_of_isZero hz
    exact @Subsingleton.elim (M.val.obj (Opposite.op (W' ⊓ V i))) this _ _

/-- Exactness of a complex after open restriction is local on an open cover.
Source: Stacks Project, Modules, Tag 01AG (lemma-abelian), applied to the
short complex of consecutive differentials in a fixed degree.
(blueprint: lem-r4-open-cover-restriction-exact).

Proof: Fix a point x of U and choose an index i with x in V_i using hU.
Restriction to an open containing x does not change stalks. The exactness
hypothesis on V_i therefore gives exactness of the original complex at
its stalk at x in degree n. This holds for every x of U. The stalkwise
exactness criterion for module sheaves gives exactness of the restricted
short complex of consecutive differentials, hence ExactAt n. Equivalently,
a section killed by the outgoing differential admits local lifts on the
cover and thus near every point of its domain. This is sheaf exactness,
not surjectivity on global sections. The same proof includes the empty
cover: U is then empty and every module sheaf over U is zero. -/
theorem exactAt_over_of_open_cover
    (X : Scheme.{u}) (K : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (ι : Type v) (V : ι → X.Opens) (U : X.Opens) (hU : U = ⨆ i, V i)
    (n : ℤ)
    (h : ∀ i, (((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt n) :
    (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt n := by
  let S := K.sc n
  change (S.map (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)).Exact
  apply (S.leftHomologyData.exact_map_iff
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U)).mpr
  apply isZero_over_of_open_cover X S.leftHomologyData.H ι V U hU
  intro i
  exact (S.leftHomologyData.exact_map_iff
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (V i))).mp (h i)

end AlgebraicGeometry
