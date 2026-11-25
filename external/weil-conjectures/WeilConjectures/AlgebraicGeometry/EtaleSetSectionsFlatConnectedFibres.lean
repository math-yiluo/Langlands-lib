/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.AlgebraicGeometry.EtaleConnectedFibresSectionCompatible
import WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcDescent

/-!
# Sections of etale sheaves under flat maps with connected geometric fibres

Source: Stacks Project, Etale Cohomology, Lemma 59.39.3 (Tag 0A3H)
(blueprint: lem-weil-pbc-etale-sections-flat-qc-connected-fibres).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Pullback induces a bijection on sections of every etale sheaf of sets under a flat,
quasi-compact morphism with connected geometric fibres. Sections upstairs are evaluated
at the base change of the terminal etale object of `S`, which is terminal over `T`.
The map is the unit of the same inverse-image adjunction used in
`etaleSetInverseImageCompositionUnits`.
Source: Stacks Project, Etale Cohomology, Lemma 59.39.3 (Tag 0A3H)
(blueprint: lem-weil-pbc-etale-sections-flat-qc-connected-fibres).

Proof:
1. Choose a point of each nonempty geometric fibre. Applying the pullback condition
   to that point and using `fromSpecResidueField_apply` gives a point of T above s.
   Thus f is surjective. Mathlib's `singleton_mem_fpqcPrecoverage` gives the fpqc cover.
2. Every section upstairs is compatible by
   `etaleSet_section_compatible_of_connected_geometricFibres`, the connected-fibre
   part of the argument split off as its own statement.
3. Apply `existsUnique_etaleSection_of_fpqc_cover` to the PUnit-indexed singleton.
   The canonical map from the identity etale object of T to the base change of the
   identity etale object of S has inverse the second pullback projection, as checked
   by the two pullback projection equations. Restriction along this isomorphism is
   bijective. Unique descent therefore makes the original adjunction unit bijective,
   by `Function.bijective_iff_existsUnique` and cancellation of that restriction. -/
theorem etaleSet_sections_bijective_of_flat_qc_connected_geometricFibres
    {S T : Scheme.{u}} (f : T ⟶ S) [Flat f] [QuasiCompact f]
    (hconn : ∀ s : S, ConnectedSpace
      (pullback f
        (Spec.map (CommRingCat.ofHom
          (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
            S.fromSpecResidueField s) : Scheme.{u}))
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) :
    Function.Bijective
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
        (S.smallGrothendieckTopology @Etale)
        (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app
          (op (Scheme.Etale.mk (𝟙 S)))) := by
  classical
  have hsurj : Surjective f := by
    constructor
    intro s
    let g : Spec (.of (AlgebraicClosure (S.residueField s))) ⟶ S :=
      Spec.map (CommRingCat.ofHom
        (algebraMap (S.residueField s) (AlgebraicClosure (S.residueField s)))) ≫
        S.fromSpecResidueField s
    have : ConnectedSpace (pullback f g : Scheme.{u}) := hconn s
    obtain ⟨x⟩ := (inferInstance : Nonempty (pullback f g : Scheme.{u}))
    refine ⟨(pullback.fst f g) x, ?_⟩
    have hx := congrArg (fun k : pullback f g ⟶ S => k x)
      (pullback.condition (f := f) (g := g))
    change f ((pullback.fst f g) x) = g ((pullback.snd f g) x) at hx
    exact hx.trans (S.fromSpecResidueField_apply s _)
  have hcover : Presieve.ofArrows (fun _ : PUnit.{1} => T) (fun _ => f) ∈
      Scheme.fpqcPrecoverage S := by
    rw [Presieve.ofArrows_pUnit]
    exact f.singleton_mem_fpqcPrecoverage
  let j : Scheme.Etale.mk (𝟙 T) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ f).obj (Scheme.Etale.mk (𝟙 S)) :=
    MorphismProperty.Over.homMk (pullback.lift f (𝟙 T)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp)
  let k : (MorphismProperty.Over.pullback @Etale ⊤ f).obj
      (Scheme.Etale.mk (𝟙 S)) ⟶ Scheme.Etale.mk (𝟙 T) :=
    MorphismProperty.Over.homMk (pullback.snd (𝟙 S) f) (by exact Category.comp_id _)
  have hjk : j ≫ k = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.lift f (𝟙 T) _ ≫ pullback.snd (𝟙 S) f = 𝟙 T
    exact pullback.lift_snd _ _ _
  have hkj : k ≫ j = 𝟙 _ := by
    apply MorphismProperty.Over.Hom.ext
    change pullback.snd (𝟙 S) f ≫ pullback.lift f (𝟙 T) _ = 𝟙 _
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
      simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 S) (g := f)).symm
    · simp
  have : IsIso j := ⟨k, hjk, hkj⟩
  have hr := ConcreteCategory.bijective_of_isIso
    (((Scheme.etaleSetPullback f).obj F).obj.map j.op)
  have hdesc : ∀ a : ((Scheme.etaleSetPullback f).obj F).obj.obj
      (op (Scheme.Etale.mk (𝟙 T))), ∃! t : F.obj.obj (op (Scheme.Etale.mk (𝟙 S))),
      ((Scheme.etaleSetPullback f).obj F).obj.map j.op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
          (S.smallGrothendieckTopology @Etale)
          (T.smallGrothendieckTopology @Etale)).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 S))) t) = a := by
    intro a
    have hd := existsUnique_etaleSection_of_fpqc_cover (fun _ : PUnit.{1} => T)
      (fun _ => f) hcover F (fun _ => a)
      (fun _ _ => etaleSet_section_compatible_of_connected_geometricFibres f hconn F a)
    obtain ⟨t, ht, hu⟩ := hd
    exact ⟨t, ht PUnit.unit, fun t' ht' => hu t' (fun _ => ht')⟩
  apply (Function.Bijective.of_comp_iff' hr _).1
  exact (Function.bijective_iff_existsUnique _).2 hdesc

end AlgebraicGeometry
