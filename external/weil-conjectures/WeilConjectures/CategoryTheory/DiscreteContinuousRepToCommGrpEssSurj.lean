/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DiscreteContinuousRepToCommGrp
import Mathlib.CategoryTheory.Monoidal.Internal.Types.CommGrp_

/-!
# Reconstruction of a representation from an internal group object

Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
-/

@[expose] public section

universe u w
open CategoryTheory
namespace Rep

attribute [local instance] AlgebraicGeometry.etaleFieldDiscreteForget₂
  AlgebraicGeometry.etaleFieldActionForget₂

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 04JQ, proof of lemma-equivalence-abelian-sheaves-point.
(blueprint: lem-exc-discrete-continuous-rep-to-commgrp-ess-surj)

Proof: The forgetful functor from discrete continuous actions to types preserves
finite products: the terminal carrier is a singleton and binary products carry the
diagonal action, which is continuous in the discrete topology because stabilizers
are intersections of two open stabilizers. Thus transport the internal unit, product
and inverse along the unique Cartesian comparison maps. The internal group diagrams
become the commutative group identities on the carrier. Use additive notation and its
canonical integer module structure. Equivariance of the operations makes every action
map additive, hence integer-linear. Continuity and discreteness give open stabilizers,
so this is a discrete continuous representation. Its represented group law on every
set of equivariant functions is pointwise addition, by the product comparison and
Yoneda. Consequently the reverse functor recovers the original internal group object
up to the identity carrier isomorphism. This establishes essential surjectivity.
The construction works for the zero group, arbitrary carrier universes, and
non-Hausdorff topological groups. -/
theorem discreteContinuousRepToCommGrp_essSurj
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CartesianMonoidalCategory (DiscreteContAction (Type w) G)]
    [BraidedCategory (DiscreteContAction (Type w) G)] :
    (discreteContinuousRepToCommGrp (G := G)).EssSurj :=
    open MonoidalCategory CartesianMonoidalCategory Limits in
    open scoped CategoryTheory.MonObj in by
  classical
  let F := forget (DiscreteContAction (Type w) G)
  have : Limits.PreservesFiniteProducts F := by
    have hprod (A B : DiscreteContAction (Type w) G) :
        IsIso (CartesianMonoidalCategory.prodComparison F A B) := by
      let P₀ : Action (Type w) G :=
        { V := A.obj.obj.V × B.obj.obj.V
          ρ :=
            { toFun g := .of <| ↾fun x ↦ (A.obj.obj.ρ g x.1, B.obj.obj.ρ g x.2)
              map_one' := by
                apply End.ext
                apply ConcreteCategory.hom_ext
                intro x
                exact Prod.ext (ConcreteCategory.congr_hom congr($(A.obj.obj.ρ.map_one).asHom) x.1)
                  (ConcreteCategory.congr_hom congr($(B.obj.obj.ρ.map_one).asHom) x.2)
              map_mul' g h := by
                apply End.ext
                apply ConcreteCategory.hom_ext
                intro x
                exact Prod.ext
                  (ConcreteCategory.congr_hom congr($(A.obj.obj.ρ.map_mul g h).asHom) x.1)
                  (ConcreteCategory.congr_hom congr($(B.obj.obj.ρ.map_mul g h).asHom) x.2) } }
      let P : DiscreteContAction (Type w) G := ⟨⟨P₀, by
        let : DiscreteTopology ((forget₂ _ TopCat).obj P₀) := discreteTopology_bot _
        apply continuousSMul_iff_stabilizer_isOpen.mpr
        intro x
        let : DiscreteTopology ((forget₂ _ TopCat).obj A.obj.obj) := A.property
        let : DiscreteTopology ((forget₂ _ TopCat).obj B.obj.obj) := B.property
        have ha : IsOpen {g : G | A.obj.obj.ρ g x.1 = x.1} :=
          (continuousSMul_iff_stabilizer_isOpen.mp A.obj.property) x.1
        have hb : IsOpen {g : G | B.obj.obj.ρ g x.2 = x.2} :=
          (continuousSMul_iff_stabilizer_isOpen.mp B.obj.property) x.2
        change IsOpen {g : G | (A.obj.obj.ρ g x.1, B.obj.obj.ρ g x.2) = x}
        convert ha.inter hb using 1
        ext g
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Prod.ext_iff]⟩, discreteTopology_bot _⟩
      let p : P ⟶ A := ObjectProperty.homMk (ObjectProperty.homMk
        { hom := ↾Prod.fst, comm _ := rfl })
      let q : P ⟶ B := ObjectProperty.homMk (ObjectProperty.homMk
        { hom := ↾Prod.snd, comm _ := rfl })
      let i : tensorObj A B ⟶ P := ObjectProperty.homMk (ObjectProperty.homMk
        { hom := ↾fun x ↦ ((fst A B).hom.hom.hom x, (snd A B).hom.hom.hom x)
          comm g := by
            apply ConcreteCategory.hom_ext
            intro x
            apply Prod.ext
            · exact ConcreteCategory.congr_hom ((fst A B).hom.hom.comm g) x
            · exact ConcreteCategory.congr_hom ((snd A B).hom.hom.comm g) x })
      have hi : i ≫ lift p q = 𝟙 (tensorObj A B) := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [Category.assoc, lift_fst, Category.id_comp]
          rfl
        · rw [Category.assoc, lift_snd, Category.id_comp]
          rfl
      have hj : lift p q ≫ i = 𝟙 P := by
        apply ObjectProperty.hom_ext
        apply ObjectProperty.hom_ext
        apply Action.Hom.ext
        apply ConcreteCategory.hom_ext
        intro x
        exact Prod.ext
          (congrArg (fun k : P ⟶ A ↦ k.hom.hom.hom x) (lift_fst p q))
          (congrArg (fun k : P ⟶ B ↦ k.hom.hom.hom x) (lift_snd p q))
      apply (isIso_iff_bijective _).mpr
      change Function.Bijective (fun x ↦ ((fst A B).hom.hom.hom x,
        (snd A B).hom.hom.hom x))
      exact ⟨fun x y h ↦ by
        have hh := congrArg (fun k : tensorObj A B ⟶ tensorObj A B ↦ k.hom.hom.hom x) hi
        have hh' := congrArg (fun k : tensorObj A B ⟶ tensorObj A B ↦ k.hom.hom.hom y) hi
        exact hh.symm.trans ((congrArg (fun z ↦ (lift p q).hom.hom.hom z) h).trans hh'),
        fun x ↦ ⟨(lift p q).hom.hom.hom x,
          congrArg (fun k : P ⟶ P ↦ k.hom.hom.hom x) hj⟩⟩
    have hterm : IsIso (CartesianMonoidalCategory.terminalComparison F) := by
      let T₀ : Action (Type w) G := { V := PUnit, ρ := 1 }
      let T : DiscreteContAction (Type w) G := ⟨⟨T₀, by
        let : Subsingleton ((forget₂ _ TopCat).obj T₀) := inferInstanceAs (Subsingleton PUnit)
        constructor
        have he : (fun p : G × ((forget₂ _ TopCat).obj T₀) ↦ p.1 • p.2) =
            (fun _ ↦ (PUnit.unit : ((forget₂ _ TopCat).obj T₀))) := by
          funext p
          exact Subsingleton.elim _ _
        rw [he]
        exact continuous_const⟩, discreteTopology_bot _⟩
      let j : T ⟶ tensorUnit (DiscreteContAction (Type w) G) := toUnit T
      let i : tensorUnit (DiscreteContAction (Type w) G) ⟶ T :=
        ObjectProperty.homMk (ObjectProperty.homMk
          { hom := ↾fun _ ↦ PUnit.unit
            comm _ := by apply ConcreteCategory.hom_ext; intro x; rfl })
      let e : T ≅ tensorUnit (DiscreteContAction (Type w) G) :=
        { hom := j
          inv := i
          hom_inv_id := by
            apply ObjectProperty.hom_ext
            apply ObjectProperty.hom_ext
            apply Action.Hom.ext
            apply ConcreteCategory.hom_ext
            intro x
            exact Subsingleton.elim _ _
          inv_hom_id := toUnit_unique _ _ }
      let d : F.obj (tensorUnit (DiscreteContAction (Type w) G)) ≅ tensorUnit (Type w) :=
        (F.mapIso e).symm
      have hd : d.hom = CartesianMonoidalCategory.terminalComparison F := toUnit_unique _ _
      rw [← hd]
      infer_instance
    let := hprod
    let := hterm
    have := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison F
    have := preservesLimit_empty_of_isIso_terminalComparison F
    have := preservesLimitsOfShape_pempty_of_preservesTerminal F
    exact .of_preserves_binary_and_terminal F
  let : F.Monoidal := Functor.Monoidal.ofChosenFiniteProducts F
  let : F.Braided := Functor.Braided.ofChosenFiniteProducts F
  constructor
  intro A
  let B := F.mapCommGrp.obj A
  let : CommGroup (F.obj A.X) := CommGrpTypeEquivalenceCommGrp.commGrpCommGroup B.X
  let V := Additive (F.obj A.X)
  let : AddCommGroup V := inferInstance
  let : Module ℤ V := inferInstance
  let t (g : G) : F ⟶ F :=
    { app X := (X.obj.obj.ρ g).asHom
      naturality {X Y} f := (f.hom.hom.comm g).symm }
  let a (g : G) : V →+ V :=
    ((CommGrpTypeEquivalenceCommGrp.functor.map
      ((Functor.mapCommGrpNatTrans (t g)).app A)).hom).toAdditive
  let ρ : Representation ℤ G V :=
    { toFun g := (a g).toIntLinearMap
      map_one' := by
        ext x
        exact ConcreteCategory.congr_hom congr($(A.X.obj.obj.ρ.map_one).asHom) x
      map_mul' g h := by
        ext x
        exact ConcreteCategory.congr_hom congr($(A.X.obj.obj.ρ.map_mul g h).asHom) x }
  let M : DiscreteContinuousRep.{0, u, w} ℤ G := ⟨Rep.of ρ, by
    intro x
    let : DiscreteTopology ((forget₂ _ TopCat).obj A.X.obj.obj) := A.X.property
    have hc : ContinuousSMul G ((forget₂ _ TopCat).obj A.X.obj.obj) := A.X.obj.property
    exact (continuousSMul_iff_stabilizer_isOpen.mp hc) x⟩
  let e : (discreteRepCommGrpObject M).X ≅ A.X :=
    ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Action.mkIso (Iso.refl _) (by
      intro g
      rfl)))
  refine ⟨M, ⟨CommGrp.mkIso e ?_ ?_⟩⟩
  · apply F.map_injective
    ext x
    have he := congrArg (fun f : F.obj (tensorUnit _) ⟶ F.obj A.X ↦ f x)
      (F.map_one (X := tensorUnit _) (M := A.X))
    simp only [Hom.one_def, toUnit_unique (toUnit (tensorUnit _)) (𝟙 _), Category.id_comp] at he
    change (1 : F.obj A.X) = (F.map (MonObj.one (X := A.X))) x
    exact he.symm
  · apply F.map_injective
    ext x
    let z := (tensorHom e.hom e.hom).hom.hom.hom x
    have he := congrArg (fun f : F.obj (tensorObj A.X A.X) ⟶ F.obj A.X ↦ f z)
      (F.map_mul (fst A.X A.X) (snd A.X A.X))
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at he
    change ((MonObj.mul (X := A.X))).hom.hom.hom z =
      (fst A.X A.X).hom.hom.hom z * (snd A.X A.X).hom.hom.hom z at he
    change (Additive.toMul ((fst (discreteRepCommGrpObject M).X
      (discreteRepCommGrpObject M).X).hom.hom.hom x) : F.obj A.X) *
      (Additive.toMul ((snd (discreteRepCommGrpObject M).X
      (discreteRepCommGrpObject M).X).hom.hom.hom x) : F.obj A.X) =
      ((MonObj.mul (X := A.X))).hom.hom.hom z
    rw [he]
    have hf := congrArg (fun k ↦ k.hom.hom.hom x) (tensorHom_fst e.hom e.hom)
    have hs := congrArg (fun k ↦ k.hom.hom.hom x) (tensorHom_snd e.hom e.hom)
    exact congrArg₂ (· * ·) hf.symm hs.symm

end Rep
