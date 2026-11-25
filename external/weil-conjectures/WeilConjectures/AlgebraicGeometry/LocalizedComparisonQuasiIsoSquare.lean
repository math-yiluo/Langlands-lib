/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension

/-! # The localized comparison square for a quasi-isomorphism

Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8.
(blueprint: lem-pc-localized-comparison-quasiiso-square).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  {X X' S S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

private theorem tensorStalkIso_naturality
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (s : P ⟶ G) (z : X') :
    let := leftAlgebra f g' z
    let := rightAlgebra f f' g g' sq z
    ((ModuleCat.extendScalars ((tensorMap f f' g g' sq z).comp
      (algebraMap (A g' z) (TensorProduct (R f g' z) (A g' z) (B f' z))))).mapHomologicalComplex
        (.up ℤ)).map
          (((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).mapHomologicalComplex
            (.up ℤ)).map s) ≫ (tensorStalkIso f f' g g' sq z G).hom =
    (tensorStalkIso f f' g g' sq z P).hom ≫
      (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
        (.up ℤ)).map
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).map s)) := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let e := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso g' z)
  apply HomologicalComplex.hom_ext
  intro j
  change (ModuleCat.extendScalars _).map
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).map (s.f j)) ≫
        (tensorStalkIso f f' g g' sq z G).hom.f j =
    (tensorStalkIso f f' g g' sq z P).hom.f j ≫
      (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).map
        ((Scheme.Modules.tensorPullback g').map (s.f j))
  rw [show (tensorStalkIso f f' g g' sq z G).hom.f j = _ from
    (Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z G)) j,
    show (tensorStalkIso f f' g g' sq z P).hom.f j = _ from
    (Classical.choose_spec (exists_tensorStalkIso f f' g g' sq z P)) j]
  have h (a : A g' z →+* C z) (ha : a = (g'.stalkMap z).hom) :
      (ModuleCat.extendScalars a).map
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).map (s.f j)) ≫
          eqToHom (congrArg (fun b : A g' z →+* C z =>
            (ModuleCat.extendScalars b).obj
              ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).obj (G.X j))) ha) ≫
            e.inv.app (G.X j) =
      (eqToHom (congrArg (fun b : A g' z →+* C z =>
        (ModuleCat.extendScalars b).obj
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).obj (P.X j))) ha) ≫
        e.inv.app (P.X j)) ≫
          (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).map
            ((Scheme.Modules.tensorPullback g').map (s.f j)) := by
    subst a
    simpa using e.inv.naturality (s.f j)
  exact h _ (Classical.choose_spec (exists_tensorMap f f' g g' sq z)).1

/-- A quasi-isomorphism induces an isomorphism on the source of the localized
comparison, and the counit comparison square commutes.

Proof: stalks and restriction of scalars are exact, so the stalk of s gives an
isomorphism in D(R). The unique isomorphism between the two universal left-derived
scalar-extension functors identifies their values on this isomorphism. Taking
cohomology and conjugating by each model's cohomologyIso gives a B-linear
isomorphism. Naturality for multiplication by a in A, expressed by
cohomologyIso_smul, makes this isomorphism A-tensor-R-B-linear. Extend this
isomorphism to C to obtain e. Naturality of the universal counits gives the square
for comparison by comparison_eq. The pure-tensor specification of
ordinaryToLocalized and localized_eq give the square for localizedComparison
by the extension/restriction adjunction. Finally the specified components of
tensorStalkIso commute with s, by naturality of the pullback-stalk isomorphism.
Taking homology and composing these squares gives the displayed identity.
Neither ordinary pullback of s nor its homology is asserted to be invertible.
Source: Stacks Project, perfect.tex, equation-bc preceding Tag 0DJ8;
More on Algebra, Tags 06Y6 and 08IB.
(blueprint: lem-pc-localized-comparison-quasiiso-square). -/
theorem exists_localizedComparison_quasiIso_square
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (s : P ⟶ G) (hs : QuasiIso s) (z : X') (i : ℤ) :
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    ∃ e : (Arrow.mk ((cohomologyModel f f' g g' sq z P).localizedComparison i)).left ≅
        (Arrow.mk ((cohomologyModel f f' g g' sq z G).localizedComparison i)).left,
      (cohomologyModel f f' g g' sq z P).localizedComparison i ≫
          HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i ≫
          HomologicalComplex.homologyMap
            (((RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
              (.up ℤ)).map
                (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).map s)) i =
        e.hom ≫ (cohomologyModel f f' g g' sq z G).localizedComparison i ≫
          HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z G).hom i := by
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  have : QuasiIso s := hs
  have : (RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).PreservesHomology := by
    apply Functor.preservesHomology_of_map_exact
    intro T hT
    exact ((RingedSpace.module_stalk_exact X.toRingedSpace T.f).2.2.2.2
      T.X₃ T.f T.g T.zero).mp hT (g' z)
  let t := ((RingedSpace.moduleStalkFunctor X.toRingedSpace (g' z)).mapHomologicalComplex
    (.up ℤ)).map s
  have ht : QuasiIso t := inferInstance
  obtain ⟨e, he⟩ := ModuleCat.exists_baseDerivedTensorModel_quasiIso_comparison
    (R f g' z) (A g' z) (B f' z) (C z) t ht
    (cohomologyModel f f' g g' sq z P) (cohomologyModel f f' g g' sq z G) i
  refine ⟨(ModuleCat.extendScalars (algebraMap (TensorProduct (R f g' z) (A g' z) (B f' z))
    (C z))).mapIso e, ?_⟩
  have hn := congrArg (fun a => HomologicalComplex.homologyMap a i)
    (tensorStalkIso_naturality f f' g g' sq P G s z)
  simp only [HomologicalComplex.homologyMap_comp] at hn
  rw [← hn]
  simpa only [Category.assoc, Functor.mapIso_hom, t, RingHom.algebraMap_toAlgebra] using
    congrArg (fun a => a ≫ HomologicalComplex.homologyMap
      (tensorStalkIso f f' g g' sq z G).hom i) he

end AlgebraicGeometry.SingleComplexBaseChange
