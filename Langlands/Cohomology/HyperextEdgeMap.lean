import Langlands.Cohomology.HyperextHomComplex
import Langlands.Cohomology.HyperextDegeneration.Statement

/-!
# The edge map of the hyperext spectral sequence on a K-projective complex

Let `P` be a cochain complex in an abelian category `C`, let `W` be an object of `C` and let
`W₀` be `W` placed in degree `0`. The edge map `HyperextDegeneration.edgeMap (Q.obj P) W n` of
`Langlands.Cohomology.HyperextDegeneration.Statement` sends a morphism `Q.obj P ⟶ W₀⟦n⟧` of the
derived category to the morphism `H^{-n}(Q.obj P) ⟶ W` it induces on cohomology. When `P` is
K-projective, `HyperextHomComplex.homObjHomologyAddEquiv` identifies its source with the
cohomology in degree `n` of the complex `Hom(P^{-•}, W)` (`homObjComplex P W`). This module
computes the edge map in these terms.

A cocycle of degree `n` of `Hom(P^{-•}, W)` is a morphism `f : P.X (-n) ⟶ W` with
`P.d (-(n + 1)) (-n) ≫ f = 0`, so its restriction to the cycles of `P` in degree `-n` factors
through `P.homology (-n)` (`homologyDesc`). This gives a morphism of abelian groups
`restriction P W n` from the cohomology of `Hom(P^{-•}, W)` in degree `n` to
`P.homology (-n) ⟶ W`. After identifying `H^{-n}(Q.obj P)` with `P.homology (-n)` by
`DerivedCategory.homologyFunctorFactors`, the edge map is `restriction P W n` multiplied by the
sign `sign n = (-1)^{n(n+1)/2}` of `HyperextHomComplex.homComplexSingleIso`
(`comp_edgeMap_homObjHomologyAddEquiv`). Hence the edge map is bijective if and only if
`restriction P W n` is (`bijective_edgeMap_iff`).

This module does not prove `HyperextDegenerationStatement`: it only treats objects of the form
`Q.obj P` with `P` K-projective, and it makes no assumption on `Ext` groups.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

namespace HyperextEdgeMap

universe w v u

open CochainComplex HomComplex HyperextHomComplex

section Restriction

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism `f : P.X (-n) ⟶ W` that vanishes on the image of the differential
`P.d (-(n + 1)) (-n)` induces a morphism `P.homology (-n) ⟶ W`: the restriction of `f` to the
cycles of `P` in degree `-n`, which factors through the cokernel `P.homology (-n)`. -/
noncomputable def homologyDesc (P : CochainComplex C ℤ) (W : C) (n : ℤ) (f : P.X (-n) ⟶ W)
    (hf : P.d (-(n + 1)) (-n) ≫ f = 0) : P.homology (-n) ⟶ W :=
  (P.homologyIsCokernel (-(n + 1)) (-n) (by simp only [CochainComplex.prev]; lia)).desc
    (CokernelCofork.ofπ (P.iCycles (-n) ≫ f) (by rw [HomologicalComplex.toCycles_i_assoc, hf]))

/-- `homologyDesc P W n f hf` composed with the projection from the cycles of `P` in degree
`-n` is the restriction of `f` to these cycles. -/
@[reassoc (attr := simp)]
lemma homologyπ_homologyDesc (P : CochainComplex C ℤ) (W : C) (n : ℤ) (f : P.X (-n) ⟶ W)
    (hf : P.d (-(n + 1)) (-n) ≫ f = 0) :
    P.homologyπ (-n) ≫ homologyDesc P W n f hf = P.iCycles (-n) ≫ f :=
  (P.homologyIsCokernel _ _ _).fac _ WalkingParallelPair.one

/-- A cocycle of degree `n` of `Hom(P^{-•}, W)` vanishes on the image of the differential
`P.d (-(n + 1)) (-n)`. -/
lemma d_comp_iCycles_apply (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    (c : (homObjComplex P W).cycles n) :
    P.d (-(n + 1)) (-n) ≫ ((homObjComplex P W).iCycles n c : P.X (-n) ⟶ W) = 0 :=
  ConcreteCategory.congr_hom ((homObjComplex P W).iCycles_d n (n + 1)) c

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of abelian groups from the cocycles of degree `n` of `Hom(P^{-•}, W)` to
`P.homology (-n) ⟶ W` sending a cocycle `f : P.X (-n) ⟶ W` to `homologyDesc P W n f _`. -/
noncomputable def cyclesRestriction (P : CochainComplex C ℤ) (W : C) (n : ℤ) :
    (homObjComplex P W).cycles n ⟶ AddCommGrpCat.of (P.homology (-n) ⟶ W) :=
  AddCommGrpCat.ofHom
    { toFun := fun c => homologyDesc P W n _ (d_comp_iCycles_apply P W n c)
      map_zero' := (cancel_epi (P.homologyπ (-n))).1 (by
        rw [homologyπ_homologyDesc, map_zero, comp_zero, comp_zero])
      map_add' := fun a b => (cancel_epi (P.homologyπ (-n))).1 (by
        rw [homologyπ_homologyDesc, map_add, Preadditive.comp_add, Preadditive.comp_add,
          homologyπ_homologyDesc, homologyπ_homologyDesc]) }

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of abelian groups from the cohomology in degree `n` of `Hom(P^{-•}, W)` to
`P.homology (-n) ⟶ W` induced by `cyclesRestriction`: the class of a cocycle
`f : P.X (-n) ⟶ W` goes to the morphism induced by `f` on `P.homology (-n)`. It is well defined
because a coboundary `P.d (-n) (-(n - 1)) ≫ g` vanishes on the cycles of `P`. -/
noncomputable def restriction (P : CochainComplex C ℤ) (W : C) (n : ℤ) :
    (homObjComplex P W).homology n ⟶ AddCommGrpCat.of (P.homology (-n) ⟶ W) :=
  ((homObjComplex P W).homologyIsCokernel (n - 1) n (by simp)).desc
    (CokernelCofork.ofπ (cyclesRestriction P W n) (by
      ext x
      refine (cancel_epi (P.homologyπ (-n))).1 ?_
      change P.homologyπ (-n) ≫ homologyDesc P W n ((homObjComplex P W).iCycles n
        ((homObjComplex P W).toCycles (n - 1) n x))
          (d_comp_iCycles_apply P W n _) = P.homologyπ (-n) ≫ 0
      have h : ((homObjComplex P W).iCycles n ((homObjComplex P W).toCycles (n - 1) n x) :
          P.X (-n) ⟶ W) = P.d (-n) (-(n - 1)) ≫ (x : P.X (-(n - 1)) ⟶ W) :=
        ConcreteCategory.congr_hom ((homObjComplex P W).toCycles_i (n - 1) n) x
      rw [comp_zero]
      refine (homologyπ_homologyDesc P W n _ (d_comp_iCycles_apply P W n _)).trans ?_
      rw [h, HomologicalComplex.iCycles_d_assoc, zero_comp]))

/-- The value of `restriction P W n` on the class of a cocycle `c`, composed with the projection
from the cycles of `P` in degree `-n`, is the restriction of `c` to these cycles. -/
lemma homologyπ_restriction (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    (c : (homObjComplex P W).cycles n) :
    P.homologyπ (-n) ≫ (restriction P W n ((homObjComplex P W).homologyπ n c) :
      P.homology (-n) ⟶ W) =
      P.iCycles (-n) ≫ ((homObjComplex P W).iCycles n c : P.X (-n) ⟶ W) := by
  have h : (restriction P W n ((homObjComplex P W).homologyπ n c) : P.homology (-n) ⟶ W) =
      cyclesRestriction P W n c :=
    ConcreteCategory.congr_hom (((homObjComplex P W).homologyIsCokernel (n - 1) n
      (by simp)).fac _ WalkingParallelPair.one) c
  rw [h]
  exact homologyπ_homologyDesc P W n _ (d_comp_iCycles_apply P W n c)

/-- The component from degree `-n` to degree `0` of the cochain corresponding to
`f : P.X (-n) ⟶ W` under `cochainAddEquiv P W n` is `sign n • f`. -/
lemma toSingleEquiv_cochainAddEquiv_symm (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    (f : P.X (-n) ⟶ W) :
    Cochain.toSingleEquiv (neg_add_cancel n) ((cochainAddEquiv P W n).symm f) = sign n • f := by
  calc _ = sign n • sign n •
        Cochain.toSingleEquiv (neg_add_cancel n) ((cochainAddEquiv P W n).symm f) := by
          rw [smul_smul, Int.units_mul_self, one_smul]
    _ = sign n • cochainAddEquiv P W n ((cochainAddEquiv P W n).symm f) := rfl
    _ = sign n • f := by rw [AddEquiv.apply_symm_apply]

/-- The map induced on cycles by a morphism of cochain complexes `φ`, written with
`liftCycles`. -/
lemma cyclesMap_eq_liftCycles {K L : CochainComplex C ℤ} (φ : K ⟶ L) (i j : ℤ)
    (hj : (ComplexShape.up ℤ).next i = j) :
    HomologicalComplex.cyclesMap φ i =
      L.liftCycles (K.iCycles i ≫ φ.f i) j hj (by simp) := by
  rw [← cancel_mono (L.iCycles i), HomologicalComplex.cyclesMap_i,
    HomologicalComplex.liftCycles_i]

end Restriction

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory

set_option backward.isDefEq.respectTransparency false in
/-- `cohomologyClassAddEquiv P L n` written as a composite of morphisms of the derived
category. -/
lemma cohomologyClassAddEquiv_apply (P L : CochainComplex C ℤ) (n : ℤ) [P.IsKProjective]
    (x : CohomologyClass P L n) :
    cohomologyClassAddEquiv P L n x = ((quotientCompQhIso C).inv.app P ≫
      Qh.map (CohomologyClass.toHom x)) ≫ ((quotientCompQhIso C).hom.app (L⟦n⟧) ≫
        (Q.commShiftIso n).hom.app L) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- `cohomologyClassAddEquiv` sends the class of a cocycle `z` to the image under `Q` of the
morphism of complexes `P ⟶ L⟦n⟧` corresponding to `z` (Mathlib's `Cocycle.equivHomShift`). -/
lemma cohomologyClassAddEquiv_mk (P L : CochainComplex C ℤ) (n : ℤ) [P.IsKProjective]
    (z : Cocycle P L n) :
    cohomologyClassAddEquiv P L n (CohomologyClass.mk z) =
      ShiftedHom.map (Cocycle.equivHomShift.symm z) Q := by
  rw [cohomologyClassAddEquiv_apply, CohomologyClass.toHom_mk, Category.assoc,
    quotientCompQhIso_hom_naturality_assoc, Iso.inv_hom_id_app_assoc]
  rfl

/-- The identification `H^0(W₀) ≅ W` of `DerivedCategory.singleFunctorCompHomologyFunctorIso`,
transported along `homologyFunctorFactors` to the cohomology of the complex `W₀`, is Mathlib's
`HomologicalComplex.singleObjHomologySelfIso`. -/
lemma homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso (W : C) :
    (homologyFunctorFactors C 0).inv.app ((CochainComplex.singleFunctor C 0).obj W) ≫
      (singleFunctorCompHomologyFunctorIso C 0).hom.app W =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 W).hom := by
  simp only [singleFunctorCompHomologyFunctorIso, Iso.trans_hom, NatTrans.comp_app]
  simp
  exact Iso.inv_hom_id_app_assoc (homologyFunctorFactors C 0) _ _

set_option backward.isDefEq.respectTransparency false in
/-- The edge map applied to the image in the derived category of a morphism of complexes
`φ : P ⟶ W₀⟦n⟧`, where `W₀` is `W` placed in degree `0`, restricted to the cycles of `P` in
degree `-n`: it is the restriction of the component of `φ` in degree `-n`, followed by the
identifications `(W₀⟦n⟧)^{-n} ≅ W₀^0 ≅ W`. -/
lemma homologyπ_comp_edgeMap_map (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    (φ : P ⟶ ((CochainComplex.singleFunctor C 0).obj W)⟦n⟧) :
    P.homologyπ (-n) ≫ (homologyFunctorFactors C (-n)).inv.app P ≫
      HyperextDegeneration.edgeMap (Q.obj P) W n (ShiftedHom.map φ Q) =
      P.iCycles (-n) ≫ φ.f (-n) ≫
        (((CochainComplex.singleFunctor C 0).obj W).shiftFunctorObjXIso n (-n) 0
          (by lia)).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 W).hom := by
  dsimp only [HyperextDegeneration.edgeMap]
  rw [shiftMap_homologyFunctor_map_Q_assoc φ (-n) 0, Iso.inv_hom_id_app_assoc,
    homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso]
  change P.homologyπ (-n) ≫ (HomologicalComplex.homologyMap φ (-n) ≫
    ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n (-n) 0
      (by lia)).hom.app _) ≫ _ = _
  have h₁ : P.homologyπ (-n) ≫ HomologicalComplex.homologyMap φ (-n) =
      (((CochainComplex.singleFunctor C 0).obj W)⟦n⟧).liftCycles (P.iCycles (-n) ≫ φ.f (-n))
        (-n + 1) (by simp) (by simp) ≫
        (((CochainComplex.singleFunctor C 0).obj W)⟦n⟧).homologyπ (-n) := by
    rw [HomologicalComplex.homologyπ_naturality, cyclesMap_eq_liftCycles φ (-n) (-n + 1) (by simp)]
  have h₂ := liftCycles_shift_homologyπ ((CochainComplex.singleFunctor C 0).obj W)
    (P.iCycles (-n) ≫ φ.f (-n)) (-n + 1) (by simp) (by simp) 0 (by lia) 1 (by simp)
  calc _ = ((P.homologyπ (-n) ≫ HomologicalComplex.homologyMap φ (-n)) ≫
        ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso n (-n) 0
          (by lia)).hom.app _) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 W).hom := by
          simp only [Category.assoc]
    _ = _ := by
      rw [h₁, h₂]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
      rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
        HomologicalComplex.singleObjCyclesSelfIso_hom, HomologicalComplex.liftCycles_i_assoc]
      simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- For a K-projective complex `P` and a cocycle `z` of degree `n` of Mathlib's Hom complex from
`P` to `W₀`, the edge map applied to the class of `z`, restricted to the cycles of `P` in degree
`-n`, is the restriction of the component of `z` from degree `-n` to degree `0`. No sign
appears. -/
lemma homologyπ_comp_edgeMap_mk (P : CochainComplex C ℤ) (W : C) (n : ℤ) [P.IsKProjective]
    (z : Cocycle P ((CochainComplex.singleFunctor C 0).obj W) n) :
    P.homologyπ (-n) ≫ (homologyFunctorFactors C (-n)).inv.app P ≫
      HyperextDegeneration.edgeMap (Q.obj P) W n
        (cohomologyClassAddEquiv P _ n (CohomologyClass.mk z)) =
      P.iCycles (-n) ≫ Cochain.toSingleEquiv (neg_add_cancel n) (z : Cochain _ _ n) := by
  rw [cohomologyClassAddEquiv_mk, homologyπ_comp_edgeMap_map]
  have key : (Cocycle.equivHomShift.symm z).f (-n) =
      (z : Cochain _ _ n).v (-n) 0 (neg_add_cancel n) ≫
        (((CochainComplex.singleFunctor C 0).obj W).shiftFunctorObjXIso n (-n) 0 (by lia)).inv :=
    Cochain.rightShift_v _ n 0 (zero_add n) (-n) (-n) (add_zero _) 0 (neg_add_cancel n)
  rw [key, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `homObjHomologyAddEquiv` sends the class of a cocycle `c` of `Hom(P^{-•}, W)` to the image
under `cohomologyClassAddEquiv` of the class of the corresponding cocycle of Mathlib's Hom
complex. -/
lemma homObjHomologyAddEquiv_homologyπ (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    [P.IsKProjective] (c : (homObjComplex P W).cycles n) :
    homObjHomologyAddEquiv P W n ((homObjComplex P W).homologyπ n c) =
      cohomologyClassAddEquiv P _ n (CohomologyClass.mk
        ((HomComplex.leftHomologyData P ((CochainComplex.singleFunctor C 0).obj W) n).cyclesIso.hom
          (HomologicalComplex.cyclesMap (homComplexSingleIso P W).inv n c))) := by
  have h₁ : HomologicalComplex.homologyMap (homComplexSingleIso P W).inv n
      ((homObjComplex P W).homologyπ n c) =
      (HomComplex P ((CochainComplex.singleFunctor C 0).obj W)).homologyπ n
        (HomologicalComplex.cyclesMap (homComplexSingleIso P W).inv n c) :=
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality _ n) c
  change homComplexHomologyAddEquiv P _ n (HomologicalComplex.homologyMap
    (homComplexSingleIso P W).inv n ((homObjComplex P W).homologyπ n c)) = _
  rw [h₁]
  exact congrArg (cohomologyClassAddEquiv P _ n) (ConcreteCategory.congr_hom
    (HomComplex.leftHomologyData P _ n).homologyπ_comp_homologyIso_hom _)

omit [HasDerivedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- The cocycle of Mathlib's Hom complex corresponding to a cocycle `c` of `Hom(P^{-•}, W)` is
the cochain corresponding to `c` under `cochainAddEquiv P W n`. -/
lemma coe_cyclesIso_hom_cyclesMap (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    (c : (homObjComplex P W).cycles n) :
    ((HomComplex.leftHomologyData P ((CochainComplex.singleFunctor C 0).obj W) n).cyclesIso.hom
      (HomologicalComplex.cyclesMap (homComplexSingleIso P W).inv n c)).1 =
      (cochainAddEquiv P W n).symm ((homObjComplex P W).iCycles n c) :=
  (ConcreteCategory.congr_hom (HomComplex.leftHomologyData P _ n).cyclesIso_hom_comp_i _).trans
    (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (homComplexSingleIso P W).inv n) c)

set_option backward.isDefEq.respectTransparency false in
/-- For a K-projective complex `P` and a cocycle `c : P.X (-n) ⟶ W` of degree `n` of
`Hom(P^{-•}, W)`, the edge map applied to the class of `c` (under `homObjHomologyAddEquiv`),
restricted to the cycles of `P` in degree `-n`, is `sign n` times the restriction of `c`. -/
lemma homologyπ_comp_edgeMap (P : CochainComplex C ℤ) (W : C) (n : ℤ) [P.IsKProjective]
    (c : (homObjComplex P W).cycles n) :
    P.homologyπ (-n) ≫ (homologyFunctorFactors C (-n)).inv.app P ≫
      HyperextDegeneration.edgeMap (Q.obj P) W n
        (homObjHomologyAddEquiv P W n ((homObjComplex P W).homologyπ n c)) =
      sign n • (P.iCycles (-n) ≫ ((homObjComplex P W).iCycles n c : P.X (-n) ⟶ W)) := by
  rw [homObjHomologyAddEquiv_homologyπ, homologyπ_comp_edgeMap_mk, coe_cyclesIso_hom_cyclesMap,
    toSingleEquiv_cochainAddEquiv_symm, Units.smul_def, Units.smul_def, Preadditive.comp_zsmul]

set_option backward.isDefEq.respectTransparency false in
/-- For a K-projective complex `P`, the edge map on `homObjHomologyAddEquiv P W n x`, after
identifying `H^{-n}(Q.obj P)` with `P.homology (-n)`, is `sign n • restriction P W n x`. -/
lemma comp_edgeMap_homObjHomologyAddEquiv (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    [P.IsKProjective] (x : (homObjComplex P W).homology n) :
    (homologyFunctorFactors C (-n)).inv.app P ≫
      HyperextDegeneration.edgeMap (Q.obj P) W n (homObjHomologyAddEquiv P W n x) =
      sign n • (restriction P W n x : P.homology (-n) ⟶ W) := by
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    ((homObjComplex P W).homologyπ n)).1 inferInstance x
  refine (cancel_epi (P.homologyπ (-n))).1 ?_
  rw [homologyπ_comp_edgeMap, Units.smul_def, Units.smul_def, Preadditive.comp_zsmul,
    homologyπ_restriction]

set_option backward.isDefEq.respectTransparency false in
/-- For a K-projective complex `P`, the edge map `Hom(Q.obj P, W₀⟦n⟧) → Hom(H^{-n}(Q.obj P), W)`
is bijective if and only if `restriction P W n` is. -/
lemma bijective_edgeMap_iff (P : CochainComplex C ℤ) (W : C) (n : ℤ) [P.IsKProjective] :
    Function.Bijective (HyperextDegeneration.edgeMap (Q.obj P) W n) ↔
      Function.Bijective (restriction P W n) := by
  let g : ((DerivedCategory.homologyFunctor C (-n)).obj (Q.obj P) ⟶ W) ≃
      (P.homology (-n) ⟶ W) :=
    { toFun := fun φ => sign n • ((homologyFunctorFactors C (-n)).inv.app P ≫ φ)
      invFun := fun ψ => sign n • ((homologyFunctorFactors C (-n)).hom.app P ≫ ψ)
      left_inv := fun φ => by
        dsimp only
        rw [Units.smul_def, Units.smul_def, Preadditive.comp_zsmul, smul_smul,
          Iso.hom_inv_id_app_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
      right_inv := fun ψ => by
        dsimp only
        rw [Units.smul_def, Units.smul_def, Preadditive.comp_zsmul, smul_smul,
          Iso.inv_hom_id_app_assoc, ← Units.val_mul, Int.units_mul_self, Units.val_one,
          one_smul] }
  have hfun : (⇑(restriction P W n) : (homObjComplex P W).homology n → (P.homology (-n) ⟶ W)) =
      g ∘ HyperextDegeneration.edgeMap (Q.obj P) W n ∘ homObjHomologyAddEquiv P W n := by
    funext x
    change _ = sign n • ((homologyFunctorFactors C (-n)).inv.app P ≫
      HyperextDegeneration.edgeMap (Q.obj P) W n (homObjHomologyAddEquiv P W n x))
    rw [comp_edgeMap_homObjHomologyAddEquiv, smul_smul, Int.units_mul_self, one_smul]
  rw [hfun, Function.Bijective.of_comp_iff' g.bijective,
    Function.Bijective.of_comp_iff _ (homObjHomologyAddEquiv P W n).bijective]

end Derived

end HyperextEdgeMap

end Langlands.Cohomology
