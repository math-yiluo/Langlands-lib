/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.Restrict
import all WeilConjectures.AlgebraicGeometry.CoherentKernelConditionRestriction

/-! # Finite type of a kernel restricted to one open intersection

Source: Stacks Project, Modules, Definitions 01BV and 01B5 and Section 01AF.
(blueprint: lem-weil-pbc-coherent-kernel-intersection-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The kernel condition on a single open `U` controls the restriction to `W ∩ U`
of a kernel initially defined on `W`. This comparison requires neither an open
cover nor a finite-type hypothesis on `F`.
Source: Stacks Project, Modules, Definition 01BV (definition-coherent),
Definition 01B5 (definition-finite-type), and Section 01AF (section-kernels).
(blueprint: lem-weil-pbc-coherent-kernel-intersection-finite-type).

Proof: Put `Z = W ∩ U`, regarded as an open of `U`. Restrict `f` to `Z`.
Restriction sends the structure module to the structure module and preserves
finite coproducts; its source is therefore the free module of rank `n` on `Z`.
Transitivity identifies its target with `(F|_U)|_Z`. Precompose with the free-module
comparison isomorphism to obtain a map of precisely the kind in `hK`, and apply
`hK` to that map. Its kernel is finite type. By the sectionwise description of
kernels in 01AF, this kernel identifies with the restriction of `kernel f` to `Z`.
The equivalence between opens of `Z` and the corresponding slice category sends
a local finite generating family to the same sections on the corresponding open:
it preserves the free module, epimorphisms, and the covering family. Consequently
the finite local generating data transfer to `(kernel f).over (Z ⟶ W)`, giving
its finite type by 01B5. Empty intersections and rank zero require no changes. -/
theorem coherent_kernel_intersection_finiteType
    (X : Scheme.{u}) (F : X.Modules) (U : X.Opens) (n : ℕ)
    (hK : ∀ (V : U.toScheme.Opens)
      (g : SheafOfModules.free (R := U.toScheme.ringCatSheaf.over V)
        (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor U.ι).obj F).over V),
      (kernel g).IsFiniteType)
    (W : X.Opens)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over W) (ULift.{u} (Fin n)) ⟶
      F.over W) :
    ((kernel f).over (Over.mk (homOfLE (inf_le_left : W ⊓ U ≤ W)))).IsFiniteType := by
  let V : U.toScheme.Opens := U.ι ⁻¹ᵁ W
  let Z : X.Opens := U.ι ''ᵁ V
  have hZ : Z = W ⊓ U := by
    simp [Z, V, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]
  -- Reuse sheafification instances throughout the over-site comparisons.
  have : HasSheafify ((Opens.grothendieckTopology X).over W) AddCommGrpCat.{u} :=
    inferInstance
  have : ((Opens.grothendieckTopology X).over W).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasSheafify ((Opens.grothendieckTopology X).over Z) AddCommGrpCat.{u} :=
    inferInstance
  have : ((Opens.grothendieckTopology X).over Z).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have : HasSheafify ((Opens.grothendieckTopology U).over V) AddCommGrpCat.{u} :=
    inferInstance
  have : ((Opens.grothendieckTopology U).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u} := inferInstance
  have hSheafZ : ∀ B : Over Z,
      HasSheafify (((Opens.grothendieckTopology X).over Z).over B) AddCommGrpCat.{u} :=
    inferInstance
  have hLocalZ : ∀ B : Over Z,
      (((Opens.grothendieckTopology X).over Z).over B).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  let i : Z ⟶ W := homOfLE (by rw [hZ]; exact inf_le_left)
  let A : SheafOfModules.{u} (X.ringCatSheaf.over W) ⥤
      SheafOfModules.{u} (X.ringCatSheaf.over Z) :=
    SheafOfModules.overMap X.ringCatSheaf i
  let s : V.toScheme ≅ Z.toScheme := U.ι.isoImage V
  let E := ((Scheme.Modules.overEquiv Z).trans (restrictionEquivalence s)).trans
    (Scheme.Modules.overEquiv V).symm
  let T := A ⋙ E.functor
  let eF : T.obj (F.over W) ≅ ((Scheme.Modules.restrictFunctor U.ι).obj F).over V :=
    E.functor.mapIso ((SheafOfModules.overFunctorMap X.ringCatSheaf i).app F) ≪≫
    (Scheme.Modules.overEquiv V).inverse.mapIso
      ((Scheme.Modules.restrictFunctor s.hom).mapIso ((Scheme.Modules.overFunctorEquiv Z).app F) ≪≫
        ((Scheme.Modules.restrictFunctorComp s.hom Z.ι).app F).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (U.ι.isoImage_hom_ι V)).app F ≪≫
        (Scheme.Modules.restrictFunctorComp V.ι U.ι).app F ≪≫
        ((Scheme.Modules.overFunctorEquiv V).app
          ((Scheme.Modules.restrictFunctor U.ι).obj F)).symm) ≪≫
      ((Scheme.Modules.overEquiv V).unitIso.app
        (((Scheme.Modules.restrictFunctor U.ι).obj F).over V)).symm
  let eunit : SheafOfModules.unit (U.toScheme.ringCatSheaf.over V) ≅
      T.obj (SheafOfModules.unit (X.ringCatSheaf.over W)) :=
    (V.sheafOfModulesEquivOverInverseUnit U.toScheme.ringCatSheaf).symm ≪≫
      (Scheme.Modules.overEquiv V).inverse.mapIso
        ((Scheme.Modules.restrictUnitIso s.hom).symm ≪≫
          (Scheme.Modules.restrictFunctor s.hom).mapIso
            (Z.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm) ≪≫
      E.functor.mapIso (SheafOfModules.overMapUnitIso i).symm
  let efree := SheafOfModules.mapFreeIso T (ULift.{u} (Fin n)) eunit
  let g : SheafOfModules.free (R := U.toScheme.ringCatSheaf.over V)
      (ULift.{u} (Fin n)) ⟶ ((Scheme.Modules.restrictFunctor U.ι).obj F).over V :=
    efree.hom ≫ T.map f ≫ eF.hom
  -- Supply the category-level limit instance before elaborating the composite map kernel.
  have : HasFiniteLimits (SheafOfModules.{u} (U.toScheme.ringCatSheaf.over V)) :=
    inferInstance
  have : HasLimit (parallelPair g 0) := HasLimitsOfShape.has_limit _
  have := hK V g
  have := finiteType_equivOver V (kernel g)
  have := finiteType_restrict s.inv ((Scheme.Modules.overEquiv V).functor.obj (kernel g))
  have : (E.inverse.obj (kernel g)).IsFiniteType :=
    finiteType_equivOverInverse Z
      ((Scheme.Modules.restrictFunctor s.inv).obj
        ((Scheme.Modules.overEquiv V).functor.obj (kernel g)))
  have hA : PreservesLimit (parallelPair f 0) A := by
    change PreservesLimit (parallelPair f 0)
      (SheafOfModules.pushforward (F := Over.map i)
        (Sheaf.pushforwardOverMapIso X.ringCatSheaf i).inv)
    infer_instance
  let ek : T.obj (kernel f) ≅ kernel g :=
    PreservesKernel.iso T f ≪≫
      kernel.mapIso (T.map f) g efree.symm eF (by simp [g])
  let ek' : E.inverse.obj (kernel g) ≅ A.obj (kernel f) :=
    E.inverse.mapIso ek.symm ≪≫ E.unitIso.symm.app (A.obj (kernel f))
  have : (A.obj (kernel f)).IsFiniteType := finiteType_of_iso (R := X.ringCatSheaf.over Z) ek'
  let D : Over W := Over.mk i
  -- Match the slice equivalence's presentation when reusing the instances over Z.
  have : ∀ B : Over D.left,
      HasSheafify (((Opens.grothendieckTopology X).over D.left).over B) AddCommGrpCat.{u} :=
    hSheafZ
  have : ∀ B : Over D.left,
      (((Opens.grothendieckTopology X).over D.left).over B).WEqualsLocallyBijective
        AddCommGrpCat.{u} := hLocalZ
  have : ∀ B : Over D,
      HasSheafify ((((Opens.grothendieckTopology X).over W).over D).over B)
        AddCommGrpCat.{u} := inferInstance
  have : ∀ B : Over D,
      ((((Opens.grothendieckTopology X).over W).over D).over B).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  let H := SheafOfModules.pushforwardPushforwardEquivalence.{u}
    (Over.iteratedSliceEquiv D)
    (S := (X.ringCatSheaf.over W).over D) (R := X.ringCatSheaf.over D.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact X.ringCatSheaf.1.map_id _)
    (by ext : 2; exact X.ringCatSheaf.1.map_id _)
  have (B : Over D) : (Over.post (Over.iteratedSliceEquiv D).functor).IsContinuous
      ((((Opens.grothendieckTopology X).over W).over D).over B)
      (((Opens.grothendieckTopology X).over D.left).over
        ((Over.iteratedSliceEquiv D).functor.obj B)) :=
    Functor.IsCoverDense.isContinuous _ _ _
      ((Functor.IsDenseSubsite.coverPreserving _ _
        (Over.iteratedSliceEquiv D).functor).overPost B)
  have : (H.functor.obj (A.obj (kernel f))).IsFiniteType :=
    finiteType_pushforward_leftAdjoint
      (R := X.ringCatSheaf.over D.left) (S := (X.ringCatSheaf.over W).over D)
      (M := A.obj (kernel f)) (Over.iteratedSliceEquiv D).functor (𝟙 _) (Iso.refl _)
  let eover : H.functor.obj (A.obj (kernel f)) ≅ (kernel f).over D :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun B ↦ Iso.refl _))
  have hfinal : ((kernel f).over D).IsFiniteType :=
    finiteType_of_iso (R := (X.ringCatSheaf.over W).over D) eover
  have mk_eq : ∀ (Z' : X.Opens) (h : Z' = W ⊓ U) (i' : Z' ⟶ W),
      Over.mk i' = Over.mk (homOfLE (inf_le_left : W ⊓ U ≤ W)) := by
    intro Z' h i'
    subst Z'
    congr 1
  have hD : D = Over.mk (homOfLE (inf_le_left : W ⊓ U ≤ W)) := mk_eq Z hZ i
  exact hD ▸ hfinal

end AlgebraicGeometry
