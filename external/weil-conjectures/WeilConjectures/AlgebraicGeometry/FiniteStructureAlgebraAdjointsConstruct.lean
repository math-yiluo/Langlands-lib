/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.FiniteStructureAdjointTransitions
import WeilConjectures.AlgebraicGeometry.FiniteStructureMultiplicationLift
import WeilConjectures.AlgebraicGeometry.FiniteStructureUnitLift
import Mathlib.Algebra.Category.Ring.Limits

/-! # Algebra structures on algebraized finite direct images

Source: Stacks Project, Tags 09ZT, 088E and 088F.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

open MonoidalCategory TopologicalSpace Scheme.Modules in
private noncomputable abbrev unitMap {X : Scheme.{u}}
    {G : X.Modules} (η : SheafOfModules.unit X.ringCatSheaf ⟶ G) (U : X.Opens) :
    Γ(X, U) →ₗ[Γ(X, U)] Γ(G, U) :=
  (η.val.app (op U)).hom

open MonoidalCategory TopologicalSpace Scheme.Modules in
@[instance_reducible]
private noncomputable def sectionRing {X : Scheme.{u}} (G : X.Modules)
    (μ : G ⊗ G ⟶ G) (η : SheafOfModules.unit X.ringCatSheaf ⟶ G)
    (ha : ∀ (U : X.Opens) (x y z : Γ(G, U)),
      μ.app U (tmulSection (μ.app U (tmulSection x y)) z) =
        μ.app U (tmulSection x (μ.app U (tmulSection y z))))
    (hc : ∀ (U : X.Opens) (x y : Γ(G, U)),
      μ.app U (tmulSection x y) = μ.app U (tmulSection y x))
    (hu : ∀ (U : X.Opens) (x : Γ(G, U)),
      μ.app U (tmulSection (unitMap η U 1) x) = x)
    (U : X.Opens) : CommRing Γ(G, U) :=
  letI : Mul Γ(G, U) := ⟨fun x y ↦ μ.app U (tmulSection x y)⟩
  letI : One Γ(G, U) := ⟨unitMap η U 1⟩
  letI : NatCast Γ(G, U) := ⟨fun n ↦ n • unitMap η U 1⟩
  letI : IntCast Γ(G, U) := ⟨fun z ↦ z • unitMap η U 1⟩
  { (inferInstance : AddCommGroup Γ(G, U)) with
    mul := fun x y ↦ μ.app U (tmulSection x y)
    one := unitMap η U 1
    mul_assoc := ha U
    mul_comm := hc U
    one_mul := hu U
    mul_one := fun x ↦ (hc U x (unitMap η U 1)).trans (hu U x)
    left_distrib := fun x y z ↦ by
      change μ.app U (tmulSection x (y + z)) = _
      exact (congrArg (μ.app U) (tmulSection_add x y z)).trans (map_add _ _ _)
    right_distrib := fun x y z ↦ by
      change μ.app U (tmulSection (x + y) z) = _
      exact (congrArg (μ.app U) (add_tmulSection x y z)).trans (map_add _ _ _)
    zero_mul := fun x ↦ by
      change μ.app U (tmulSection 0 x) = 0
      rw [zero_tmulSection, map_zero]
    mul_zero := fun x ↦ by
      change μ.app U (tmulSection x 0) = 0
      rw [tmulSection_zero, map_zero]
    natCast := fun n ↦ n • unitMap η U 1
    natCast_zero := by simp
    natCast_succ := fun n ↦ by
      change (n + 1) • unitMap η U 1 = n • unitMap η U 1 + unitMap η U 1
      exact succ_nsmul _ _
    intCast := fun z ↦ z • unitMap η U 1
    intCast_ofNat := fun n ↦ by change (n : ℤ) • unitMap η U 1 = n • unitMap η U 1; simp
    intCast_negSucc := fun n ↦ by
      change Int.negSucc n • unitMap η U 1 = -((n + 1) • unitMap η U 1)
      simp }

open MonoidalCategory TopologicalSpace Scheme.Modules in
private theorem packageOperations {X : Scheme.{u}} (G : X.Modules)
    (Y : ℕ → Scheme.{u}) (q : ∀ n, Y n ⟶ X)
    (a : ∀ n, G ⟶ (pushforward (q n)).obj (SheafOfModules.unit (Y n).ringCatSheaf))
    (μ : G ⊗ G ⟶ G) (η : SheafOfModules.unit X.ringCatSheaf ⟶ G)
    (ha : ∀ (U : X.Opens) (x y z : Γ(G, U)),
      μ.app U (tmulSection (μ.app U (tmulSection x y)) z) =
        μ.app U (tmulSection x (μ.app U (tmulSection y z))))
    (hc : ∀ (U : X.Opens) (x y : Γ(G, U)),
      μ.app U (tmulSection x y) = μ.app U (tmulSection y x))
    (hu : ∀ (U : X.Opens) (x : Γ(G, U)),
      μ.app U (tmulSection (unitMap η U 1) x) = x)
    (hm : ∀ (n : ℕ) (U : X.Opens),
      let α : Γ(G, U) → Γ(Y n, (q n) ⁻¹ᵁ U) := fun x ↦ (a n).app U x
      ∀ x y, α (μ.app U (tmulSection x y)) = α x * α y)
    (hη : ∀ (n : ℕ) (U : X.Opens) (r : Γ(X, U)),
      (a n).app U (unitMap η U r) = (q n).app U r) :
    ∃ B : X.CommAlgebraSheaf, ∃ e : B.toModule ≅ G,
      ∃ b : ∀ n, B ⟶ Under.mk (⟨(q n).c⟩ : X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} (q n).base).obj (Y n).sheaf),
        ∀ (n : ℕ) (U : X.Opens) (x : B.right.obj.obj (op U)),
          ((b n).right.hom.app (op U)).hom x = (a n).app U ((Hom.app e.hom U) x) := by
  let (U : X.Opens) : CommRing Γ(G, U) := sectionRing G μ η ha hc hu U
  have hs (U : X.Opens) (r : Γ(X, U)) : unitMap η U r = r • unitMap η U 1 := by
    rw [← (unitMap η U).map_smul]; congr 1; exact (mul_one r).symm
  let P : X.Opensᵒᵖ ⥤ CommRingCat.{u} :=
    { obj := fun U ↦ .of Γ(G, U.unop)
      map := fun k ↦ CommRingCat.ofHom
        { toFun := G.presheaf.map k
          map_zero' := map_zero _
          map_add' := map_add _
          map_one' := by
            exact (Hom.app_presheaf_map η k.unop (unitSectionsEquiv _ 1)).symm.trans
              (congrArg (unitMap η _) ((X.presheaf.map k).hom.map_one))
          map_mul' := fun x y ↦ by
            exact (Hom.app_presheaf_map μ k.unop (tmulSection x y)).symm.trans
              (congrArg (μ.app _) (tmulSection_map (leOfHom k.unop) x y)) }
      map_id := fun U ↦ by ext x; exact G.presheaf.map_id_apply U x
      map_comp := fun k l ↦ by ext x; exact G.presheaf.map_comp_apply k l x }
  have hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P := by
    apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat)).mpr
    exact Presheaf.isSheaf_comp_of_isSheaf _ G.presheaf (forget AddCommGrpCat) G.isSheaf
  let ηRing (U : X.Opens) : Γ(X, U) →+* Γ(G, U) :=
    { toFun := unitMap η U
      map_zero' := map_zero _
      map_add' := map_add _
      map_one' := rfl
      map_mul' := fun r s ↦ by
        change unitMap η U (r * s) =
          μ.app U (tmulSection (unitMap η U r) (unitMap η U s))
        calc
          _ = r • unitMap η U s := (unitMap η U).map_smul r s
          _ = μ.app U (tmulSection (r • unitMap η U 1) (unitMap η U s)) := by
            exact (congrArg (r • ·) (hu _ _)).symm.trans
              (Hom.app_smul μ r _).symm |>.trans
                (congrArg (μ.app _) (smul_tmulSection r _ _).symm)
          _ = _ := congrArg
            (fun z ↦ μ.app U (tmulSection z (unitMap η U s))) (hs _ r).symm }
  let B : X.CommAlgebraSheaf := Under.mk
    (show X.sheaf ⟶ (⟨P, hP⟩ : Sheaf _ CommRingCat.{u}) from
      { hom :=
          { app := fun U ↦ CommRingCat.ofHom (ηRing U.unop)
            naturality := by
              intro U V k
              ext r
              exact Hom.app_presheaf_map η k.unop (unitSectionsEquiv _ r) } })
  let e : B.toModule ≅ G := by
    dsimp only [Scheme.CommAlgebraSheaf.toModule]
    exact
    { hom := ⟨
        { app := fun U ↦ @ModuleCat.ofHom Γ(X, U.unop) _
            Γ(B.toModule, U.unop) Γ(G, U.unop) _ inferInstance _ inferInstance
            (show Γ(B.toModule, U.unop) →ₗ[Γ(X, U.unop)] Γ(G, U.unop) from
            { toFun := id
              map_add' := fun x y ↦ rfl
              map_smul' := fun r x ↦ by
                change μ.app U.unop (tmulSection (unitMap η U.unop r)
                  (show Γ(G, U.unop) from x)) =
                  r • (show Γ(G, U.unop) from x)
                rw [hs _ r, smul_tmulSection, Hom.app_smul, hu] })
          naturality := by
              intro U V k
              ext x
              rfl }⟩
      inv := ⟨
        { app := fun U ↦ @ModuleCat.ofHom Γ(X, U.unop) _
            Γ(G, U.unop) Γ(B.toModule, U.unop) _ inferInstance _ inferInstance
            (show Γ(G, U.unop) →ₗ[Γ(X, U.unop)] Γ(B.toModule, U.unop) from
            { toFun := id
              map_add' := fun x y ↦ rfl
              map_smul' := fun r x ↦ by
                change r • (show Γ(G, U.unop) from x) =
                  μ.app U.unop (tmulSection (unitMap η U.unop r) x)
                rw [hs _ r, smul_tmulSection, Hom.app_smul, hu] })
          naturality := by
              intro U V k
              ext x
              rfl }⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }
  let aRing (n : ℕ) (U : X.Opens) : Γ(G, U) →+* Γ(Y n, (q n) ⁻¹ᵁ U) :=
    { toFun := fun x ↦ (a n).app U x
      map_zero' := ((a n).app U).hom.map_zero
      map_add' := ((a n).app U).hom.map_add
      map_one' := (hη n U 1).trans ((q n).app U).hom.map_one
      map_mul' := hm n U }
  let b : ∀ n, B ⟶ Under.mk (⟨(q n).c⟩ : X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} (q n).base).obj (Y n).sheaf) :=
    fun n ↦ Under.homMk
      { hom :=
          { app := fun U ↦ CommRingCat.ofHom (aRing n U.unop)
            naturality := by
              intro U V k
              ext x
              exact Hom.app_presheaf_map (a n) k.unop x } }
      (by
        apply ObjectProperty.hom_ext
        apply NatTrans.ext
        funext U
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro r
        exact hη n U.unop r)
  refine ⟨B, e, b, ?_⟩
  intro n U x
  rfl
open MonoidalCategory TopologicalSpace Scheme.Modules in
private theorem adjoint_naturality {X S Y : Scheme.{u}}
    (j : S ⟶ X) (p : Y ⟶ S) {G H : X.Modules} (e : H ⟶ G)
    (a : (tensorPullback j).obj G ⟶ (pushforward p).obj
      (SheafOfModules.unit Y.ringCatSheaf)) :
    e ≫ finiteStructureAdjoint j p G a =
      finiteStructureAdjoint j p H ((tensorPullback j).map e ≫ a) := by
  unfold finiteStructureAdjoint
  rw [Functor.map_comp]
  simpa only [Category.assoc, Functor.comp_map, Functor.id_map] using congrArg
    (fun z ↦ z ≫ (pushforward j).map a ≫
      (pushforwardComp p j).hom.app (SheafOfModules.unit Y.ringCatSheaf))
    ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.naturality e)

/-- Construct the algebra structure and its adjoint algebra maps, without the transition equation.
Source: Stacks Project, Tag 09ZT, multiplication paragraph, using 088E, 088F and 0CYS.

Proof: Choose a proper closed subscheme annihilating G by 0CYS. Its ideal also annihilates
G's tensor square and cube. Quasi-coherence and finite type make these tensor powers coherent.
Conjugate the finite direct-image multiplications by psi and the tensor comparison. The
canonical composition comparison is built from the same pinned adjunctions, so it preserves
pulled-back sections and hence tensor products; the base-change algebra formula and hpsi
make the conjugated products compatible. Full faithfulness in 088E lifts the products
uniquely. The supporting structure-sheaf quotient is coherent with proper support. The
reduced units factor through it because its ideal annihilates each reduced algebra; full
faithfulness lifts this unit uniquely. Faithfulness on the tensor cube, square and G gives
associativity, symmetry and both unit laws. These operations equip the additive sheaf of G
with commutative ring structures preserved by restriction. Its additive sheaf condition
implies the ring sheaf condition. The unit defines the structure morphism, producing B and
the underlying-module isomorphism e. The adjoints of psi composed with pullback of e preserve
multiplication and unit by the same comparisons. They are therefore algebra maps b. The
adjunction unit and pushforward-composition comparison give the displayed section formula.
This lemma does not claim that the b commute with transitions; that is a separate adjunction
calculation. Empty opens, zero modules and empty schemes obey the same construction.
(blueprint: lem-weil-pbc-finite-structure-algebra-adjoints-construct). -/
theorem finite_structure_algebra_adjoints_construct
    (A : Type u) [CommRing A] (I : Ideal A)
    [IsNoetherianRing A] [IsAdicComplete I A]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : ∀ n : ℕ, pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) ⟶
      pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
    (hi : ∀ n : ℕ, i n ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))))
    (hp : ∀ n : ℕ, i n ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n
      + 1 + 1))))) = pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n +
      1))))) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I :=
      I) (Nat.le_succ (n + 1))))))
    (c : ∀ n : ℕ, Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) ⋙ Scheme.Modules.tensorPullback (i n) ≅
      Scheme.Modules.tensorPullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (I ^ (n + 1)))))))
    (hc : ∀ n : ℕ, c n = (Scheme.Modules.tensorPullbackCompositionIso (i n)
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1 + 1))))))
      (pullback.fst f (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (I ^ (n + 1)))))) (hi n)).symm)
    (Yn : ℕ → Scheme.{u})
    (fnY : ∀ n, Yn n ⟶ pullback f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    [∀ n, IsFinite (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hcart : ∀ n, IsPullback (fnY n) (gn n) (i n) (fnY (n + 1)))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1 + 1)))))) =
      fnY n ≫ pullback.fst f
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))
    (G : X.Modules) (hG : RingedSpace.IsCoherent X.toRingedSpace G)
    (hproper : Scheme.Modules.HasSupportProperOver f G)
    (ψ : ∀ n, (Scheme.Modules.tensorPullback (pullback.fst f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).obj G ≅
        (Scheme.Modules.pushforward (fnY n)).obj
          (SheafOfModules.unit (Yn n).ringCatSheaf))
    (hψ : ∀ n,
      (Scheme.Modules.tensorPullback (i n)).map (ψ (n + 1)).hom ≫
        (Scheme.Modules.moduleBaseChangeMap (fnY (n + 1)) (fnY n) (i n) (gn n)
          (hcart n).flip.w (SheafOfModules.unit (Yn (n + 1)).ringCatSheaf) ≫
          (Scheme.Modules.pushforward (fnY n)).map
            (Scheme.Modules.tensorPullbackObjUnitToUnit (gn n))) =
        (c n).hom.app G ≫ (ψ n).hom) :
    ∃ B : X.CommAlgebraSheaf, ∃ e : B.toModule ≅ G,
      ∃ b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ pullback.fst f
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))),
        ∀ (n : ℕ) (U : X.Opens) (x : B.right.obj.obj (op U)),
          ((b n).right.hom.app (op U)).hom x =
            (Scheme.Modules.finiteStructureAdjoint
              (pullback.fst f (Spec.map (CommRingCat.ofHom
                (Ideal.Quotient.mk (I ^ (n + 1)))))) (fnY n) B.toModule
              ((Scheme.Modules.tensorPullback (pullback.fst f
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))))).map
                  e.hom ≫ (ψ n).hom)).app U x  := by
  obtain ⟨μ, ⟨hassoc, hcomm, hmul⟩, _⟩ :=
    finite_structure_multiplication_lift A I X f i hi hp c hc
      Yn fnY gn hcart hw G hG hproper ψ hψ
  obtain ⟨η, ⟨hunit, hη⟩, _⟩ :=
    finite_structure_unit_lift A I X f i hi hp c hc
      Yn fnY gn hcart hw G hG hproper ψ hψ μ hcomm hmul
  let j := fun n ↦ pullback.fst f
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
  let q := fun n ↦ fnY n ≫ j n
  let a := fun n ↦ Scheme.Modules.finiteStructureAdjoint (j n) (fnY n) G (ψ n).hom
  obtain ⟨B, e, b, hb⟩ :=
    packageOperations G Yn q a μ η hassoc hcomm hunit hmul hη
  refine ⟨B, e, b, ?_⟩
  intro n U x
  rw [hb n U x]
  simpa only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] using
    congrArg (fun z : B.toModule ⟶
      (Scheme.Modules.pushforward (fnY n ≫ j n)).obj
        (SheafOfModules.unit (Yn n).ringCatSheaf) ↦
          (Scheme.Modules.Hom.app z U) x)
      (adjoint_naturality (j n) (fnY n) e.hom (ψ n).hom)


end AlgebraicGeometry
