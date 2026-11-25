/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.HypercohomologyLeftEdgeTruncation
import WeilConjectures.CategoryTheory.RightDerivedUnitSingleDegree

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, derived.tex, Tag 015J.
(blueprint: lem-pc-hypercohomology-left-edge-single-aux)

Proof: For the single complex, the cycle inclusion identifies its degree-n cycles
with the sole term. The canonical lift of the mapped inclusion is characterized by
its composite with the mapped cycle inclusion. The definition of the hypercohomology
left edge and its truncation maps then gives the mapped homology projection; this is
the single-complex edge calculation from Tag 015J. The displayed equality follows
by cancellation through that canonical characterization. -/
theorem cochainHypercohomologyLeftEdge_single_aux (A : B) (n : ℕ) :
    let S := (HomologicalComplex.single B (ComplexShape.up ℕ) n).obj A
    let T := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj S
    let a := T.liftCycles (G.map (S.iCycles n)) (n + 1) (by simp) (by
      change G.map (S.iCycles n) ≫ G.map (S.d n (n + 1)) = 0
      rw [← G.map_comp, S.iCycles_d, G.map_zero])
    a ≫ T.homologyπ n ≫ G.cochainHypercohomologyLeftEdge S n =
      G.map (S.homologyπ n) := by
  -- Keep the original Grothendieck hypothesis on the target category in the interface.
  have : IsGrothendieckAbelian.{vC} C := inferInstance
  let S := (HomologicalComplex.single B (ComplexShape.up ℕ) n).obj A
  let T := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj S
  let a := T.liftCycles (G.map (S.iCycles n)) (n + 1) (by simp) (by
    change G.map (S.iCycles n) ≫ G.map (S.d n (n + 1)) = 0
    rw [← G.map_comp, S.iCycles_d, G.map_zero])
  let L : CochainComplex.Plus B :=
    ⟨S.extend ComplexShape.embeddingUpNat, 0, inferInstance⟩
  let K := DerivedCategory.Plus.Q.obj L
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let H := DerivedCategory.Plus.homologyFunctor B n
  have h₀ : t.IsGE K 0 := by
    apply (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsGE 0)
  have hL : L.obj.IsStrictlyLE (n : ℤ) := by
    exact CochainComplex.isStrictlyLE_of_iso
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat A n (n : ℤ) rfl).symm n
  have hLE : t.IsLE K n := by
    apply (DerivedCategory.Plus.isLE_ι_obj_iff _ n).mp
    exact inferInstanceAs ((DerivedCategory.Q.obj L.obj).IsLE n)
  have hi : IsIso ((t.truncLTι (n + 1)).app K) :=
    (t.isLE_iff_isIso_truncLTι_app (n : ℤ) (n + 1) rfl K).mp hLE
  let i := (t.truncLTι (n + 1)).app K
  let p := (t.truncGEπ n).app ((t.truncLT (n + 1)).obj K)
  let f := CategoryTheory.inv i ≫ p ≫
    (DerivedCategory.Plus.eTruncLTCompETruncGEIso (n : ℤ)).hom.app K
  have hp : IsIso (H.map p) :=
    DerivedCategory.Plus.isIso_homologyFunctor_map_truncGEπ_app _ n n le_rfl
  have hf : H.map f ≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := B) n).hom.app
        (H.obj K) = 𝟙 (H.obj K) := by
    dsimp only [f]
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      DerivedCategory.Plus.homologyFunctor_map_eTruncLTCompETruncGEIso_hom_app]
    change H.map (CategoryTheory.inv i) ≫ H.map p ≫
      CategoryTheory.inv (H.map p) ≫ H.map i = _
    simp only [IsIso.hom_inv_id_assoc, ← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id]
    rfl
  have he := G.hypercohomologyLeftEdge_truncation K n
  change a ≫ T.homologyπ n ≫ G.cochainHypercohomologyLeftEdge S n = _
  simp only [cochainHypercohomologyLeftEdge]
  rw [reassoc_of% he]
  let e := ComplexShape.embeddingUpNat
  let GL := G.mapCochainComplexPlus.obj L
  let m := S.mapExtendIso e G
  let aL := GL.obj.liftCycles (G.map (L.obj.iCycles (n : ℤ))) (n + 1) (by simp) (by
    change G.map (L.obj.iCycles (n : ℤ)) ≫ G.map (L.obj.d n (n + 1)) = 0
    rw [← G.map_comp, L.obj.iCycles_d, G.map_zero])
  have hm : (T.extendXIso e (rfl : (n : ℤ) = n)).inv ≫ m.inv.f n =
      G.map (S.extendXIso e (rfl : (n : ℤ) = n)).inv := by
    dsimp [m, T, HomologicalComplex.mapExtendIso, HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso]
    dsimp only [HomologicalComplex.Hom.isoOfComponents, e]
    erw [HomologicalComplex.mapExtendX_hom_eq S G
      (ComplexShape.embeddingUpNat.r_f n)]
    simp [eqToHom_map]
  have hc : a ≫ (T.extendCyclesIso e (rfl : (n : ℤ) = n)).inv ≫
      HomologicalComplex.cyclesMap m.inv (n : ℤ) =
      G.map (S.extendCyclesIso e (rfl : (n : ℤ) = n)).inv ≫ aL := by
    apply (cancel_mono (GL.obj.iCycles (n : ℤ))).mp
    simp only [Category.assoc]
    erw [HomologicalComplex.cyclesMap_i,
      HomologicalComplex.extendCyclesIso_inv_iCycles_assoc]
    dsimp only [a]
    erw [← Category.assoc, T.liftCycles_i]
    change G.map (S.iCycles n) ≫
      (T.extendXIso e (rfl : (n : ℤ) = n)).inv ≫ m.inv.f n = _
    erw [hm]
    dsimp only [aL]
    erw [HomologicalComplex.liftCycles_i]
    change G.map (S.iCycles n) ≫ G.map (S.extendXIso e rfl).inv =
      G.map (S.extendCyclesIso e rfl).inv ≫ G.map ((S.extend e).iCycles (n : ℤ))
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    exact (S.extendCyclesIso_inv_iCycles e (rfl : (n : ℤ) = n)).symm
  have hex : a ≫ T.homologyπ n ≫
      (T.extendHomologyIso e (rfl : (n : ℤ) = n)).inv ≫
      HomologicalComplex.homologyMap m.inv (n : ℤ) =
      G.map (S.extendCyclesIso e (rfl : (n : ℤ) = n)).inv ≫ aL ≫ GL.obj.homologyπ n := by
    erw [HomologicalComplex.homologyπ_extendHomologyIso_inv_assoc,
      HomologicalComplex.homologyπ_naturality m.inv (n : ℤ)]
    dsimp [GL, L, e, mapCochainComplexPlus] at hc ⊢
    simpa only [Category.assoc] using
      congrArg (fun g ↦ g ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (S.extend ComplexShape.embeddingUpNat)).homologyπ n) hc
  have hsupport : ∀ j : ℤ, j ≠ (n : ℤ) → IsZero (L.obj.X j) := by
    intro j hj
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n A j hj).of_iso
      ((HomologicalComplex.eval B (ComplexShape.up ℤ) j).mapIso
        (HomologicalComplex.extendSingleIso e A n (n : ℤ) rfl))
  have hu := G.rightDerivedFunctorPlusUnit_single_degree L n hsupport f hf aL
    (GL.obj.liftCycles_i _ _ _ _)
  rw [reassoc_of% hex]
  erw [reassoc_of% hu]
  simp only [← G.map_comp, Category.assoc]
  congr 1
  change (S.extendCyclesIso e (rfl : (n : ℤ) = n)).inv ≫ L.obj.homologyπ n ≫
    (DerivedCategory.Plus.homologyFunctorObjQIso L n).inv ≫
    (DerivedCategory.Plus.homologyFunctorObjQIso L n).hom ≫
    (S.extendHomologyIso e (rfl : (n : ℤ) = n)).hom = S.homologyπ n
  simp only [Iso.inv_hom_id_assoc]
  erw [HomologicalComplex.homologyπ_extendHomologyIso_hom]
  dsimp only [e]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.Functor
