/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementStalkContraction
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Topology.Sheaves.Abelian

/-! # Exactness of Godement models -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private instance stalkAdditive (X : Scheme.{u}) (x : X) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace x).Additive where
  map_add := by
    intro M N f g
    ext m
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f + g).val) m = _
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f.val + g.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl

private theorem quasiIsoOfStalk {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (h : ∀ x : X, QuasiIso
      (((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (.up ℤ)).map f)) : QuasiIso f := by
  constructor
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_of_bijective_stalkLinearMap
  intro x
  let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let : T.Additive := inferInstance
  let : T.PreservesZeroMorphisms := inferInstance
  let : T.PreservesHomology := T.preservesHomology_of_map_exact (fun S hS ↦
    ((RingedSpace.module_stalk_exact X.toRingedSpace S.f).2.2.2.2
      S.X₃ S.f S.g S.zero).mp hS x)
  let : QuasiIso ((T.mapHomologicalComplex (.up ℤ)).map f) := h x
  let φ := (HomologicalComplex.shortComplexFunctor X.Modules (.up ℤ) n).map f
  have hm : ShortComplex.QuasiIso (T.mapShortComplex.map φ) :=
    (quasiIsoAt_iff ((T.mapHomologicalComplex (.up ℤ)).map f) n).mp inferInstance
  let := hm
  have hi : IsIso (ShortComplex.homologyMap (T.mapShortComplex.map φ) ≫
      ((L.sc n).mapHomologyIso T).hom) := inferInstance
  rw [ShortComplex.mapHomologyIso_hom_naturality] at hi
  have hi' : IsIso (((K.sc n).mapHomologyIso T).hom ≫
      T.map (HomologicalComplex.homologyMap f n)) := hi
  let := hi'
  have hf : IsIso (T.map (HomologicalComplex.homologyMap f n)) :=
    IsIso.of_isIso_comp_left ((K.sc n).mapHomologyIso T).hom _
  let := hf
  change Function.Bijective (ConcreteCategory.hom
    (T.map (HomologicalComplex.homologyMap f n)))
  exact ConcreteCategory.bijective_of_isIso _

/-- The actual Godement cofaces and germ augmentation give a quasi-isomorphism.
Source: Stacks Project, Tag 0FKR, Lemma 20.30.1 (Tag 0FKS).
(blueprint: lem-sc-module-cup-godement-model-quasi-iso)
Proof: fix a point x and apply the module stalk functor. Evaluation on the
x-coordinate of T(H), followed by evaluation of the skyscraper stalk, defines
an extra codegeneracy from (T(H))_x to H_x. Its composite with the germ unit
is the identity. Evaluation is natural in H; hence it commutes with all the
inner unit-insertion cofaces. The outer coface followed by evaluation is the
identity, and the remaining cofaces commute with evaluation with their indices
shifted by one. The alternating sums therefore give a contracting homotopy
of the augmented stalk complex. The degree-zero augmentation identifies F_x
with its degree-zero cohomology, and positive cohomology vanishes. Both source
and target vanish in negative degrees. The term and coface equalities in
ModuleCupGodementModel transport these identities to A. Stalk functors are
exact and jointly detect zero objects, so the augmentation induces an
isomorphism on every sheaf homology object. This is QuasiIso a. On an empty
scheme the stalk criterion is vacuous and every sheaf is zero. -/
theorem moduleCup_godement_model_quasiIso (X : Scheme.{u}) (F : X.Modules)
    (A : CosimplicialObject X.Modules)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶
      (((alternatingCofaceMapComplex X.Modules).obj A).extend
          ComplexShape.embeddingUpNat))
    (h : ModuleCupGodementModel X F A a) : QuasiIso a  := by
  apply quasiIsoOfStalk a
  intro x
  have he := moduleCup_godement_stalk_contraction X F A a h x
  exact (HomologicalComplex.mem_quasiIso_iff _).mp
    (homotopyEquivalences_le_quasiIso _ _ _ he)


end
end AlgebraicGeometry.Scheme.Modules
