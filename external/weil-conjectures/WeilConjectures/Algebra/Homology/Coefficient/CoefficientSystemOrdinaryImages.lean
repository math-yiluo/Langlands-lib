/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CoefficientSystemDerivedImage.CoefficientSystemImageData
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientLevelOrdinaryImages
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Ordinary geometric images of strict coefficient systems

Source: Zheng, Construction 4.1; Stacks Project, Tags 03DA and 03DB.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w d a b c e av bv cv ev
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules

private theorem transition_transpose_iff
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    {C : Type c} [Category.{cv} C] {D : Type e} [Category.{ev} D]
    {Fm : A ⥤ C} {Gm : C ⥤ A} {Fn : B ⥤ D} {Gn : D ⥤ B}
    {RY : B ⥤ A} {RX : D ⥤ C} (am : Fm ⊣ Gm) (an : Fn ⊣ Gn)
    (β : RY ⋙ Fm ≅ Fn ⋙ RX) (δ : RX ⋙ Gm ≅ Gn ⋙ RY)
    (ht : ∀ M N (f : Fn.obj M ⟶ N),
      am.homEquiv _ _ (β.hom.app M ≫ RX.map f) =
        RY.map (an.homEquiv _ _ f) ≫ δ.inv.app N)
    {Mm : A} {Mn : B} {Nm : C} {Nn : D}
    (tM : Mm ⟶ RY.obj Mn) (tN : Nm ⟶ RX.obj Nn)
    (fm : Fm.obj Mm ⟶ Nm) (fn : Fn.obj Mn ⟶ Nn) :
    (fm ≫ tN = Fm.map tM ≫ β.hom.app Mn ≫ RX.map fn) ↔
      am.homEquiv _ _ fm ≫ Gm.map tN ≫ δ.hom.app Nn =
        tM ≫ RY.map (an.homEquiv _ _ fn) := by
  have he : am.homEquiv _ _ (Fm.map tM ≫ β.hom.app Mn ≫ RX.map fn) =
      tM ≫ RY.map (an.homEquiv _ _ fn) ≫ δ.inv.app Nn := by
    rw [am.homEquiv_naturality_left, ht]
  constructor
  · intro h
    have h' := congrArg (am.homEquiv _ _) h
    rw [am.homEquiv_naturality_right, he] at h'
    apply (cancel_mono (δ.inv.app Nn)).mp
    simpa [Category.assoc] using h'
  · intro h
    apply (am.homEquiv _ _).injective
    rw [am.homEquiv_naturality_right, he]
    have h' := congrArg (· ≫ δ.inv.app Nn) h
    simpa [Category.assoc] using h'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (O : Type w) [CommRing O] (ell : O)

variable {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} C]
  [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasWeakSheafify K CommRingCat.{w}] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
  (V : Sheaf K (Type w) ⥤ Sheaf J (Type w)) (adj : L ⊣ V)

omit [HasWeakSheafify J (Type w)]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [EssentiallySmall.{w} C] in
private theorem system_hom_ext {M N : CoefficientSystem (J := J) O ell}
    (f g : M ⟶ N) (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

private def systemInverse
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    CoefficientSystem (J := J) O ell ⥤ CoefficientSystem (J := K) O ell where
  obj M := {
    level := fun n ↦ (S.lift n).modules.obj (M.level n)
    transition := fun n ↦ (S.lift (n + 1)).modules.map (M.transition n) ≫
      (S.restrictInverse (Nat.le_succ n)).hom.app (M.level n) }
  map {M N} f := {
    app := fun n ↦ (S.lift n).modules.map (f.app n)
    comm := by
      intro n
      dsimp
      rw [← Category.assoc, ← Functor.map_comp, f.comm, Functor.map_comp, Category.assoc]
      exact congrArg ((S.lift (n + 1)).modules.map (M.transition n) ≫ ·)
        ((S.restrictInverse (Nat.le_succ n)).hom.naturality (f.app n)) }
  map_id M := by
    apply system_hom_ext O ell
    funext n
    exact (S.lift n).modules.map_id _
  map_comp f g := by
    apply system_hom_ext O ell
    funext n
    exact (S.lift n).modules.map_comp _ _

private def systemDirect
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    CoefficientSystem (J := K) O ell ⥤ CoefficientSystem (J := J) O ell where
  obj M := {
    level := fun n ↦ (S.right n).obj (M.level n)
    transition := fun n ↦ (S.right (n + 1)).map (M.transition n) ≫
      (S.restrictRight (Nat.le_succ n)).hom.app (M.level n) }
  map {M N} f := {
    app := fun n ↦ (S.right n).map (f.app n)
    comm := by
      intro n
      dsimp
      rw [← Category.assoc, ← Functor.map_comp, f.comm, Functor.map_comp, Category.assoc]
      exact congrArg ((S.right (n + 1)).map (M.transition n) ≫ ·)
        ((S.restrictRight (Nat.le_succ n)).hom.naturality (f.app n)) }
  map_id M := by
    apply system_hom_ext O ell
    funext n
    exact (S.right n).map_id _
  map_comp f g := by
    apply system_hom_ext O ell
    funext n
    exact (S.right n).map_comp _ _

private def systemHomEquiv
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj)
    (M : CoefficientSystem (J := J) O ell) (N : CoefficientSystem (J := K) O ell) :
    ((systemInverse O ell L V adj S).obj M ⟶ N) ≃
      (M ⟶ (systemDirect O ell L V adj S).obj N) where
  toFun f := {
    app := fun n ↦ (S.levelAdj n).homEquiv _ _ (f.app n)
    comm := by
      intro n
      exact (transition_transpose_iff (S.levelAdj (n + 1)) (S.levelAdj n)
        (S.restrictInverse (Nat.le_succ n)) (S.restrictRight (Nat.le_succ n))
        (S.restrictTranspose (Nat.le_succ n)) (M.transition n) (N.transition n)
        (f.app (n + 1)) (f.app n)).1 (f.comm n) }
  invFun f := {
    app := fun n ↦ ((S.levelAdj n).homEquiv _ _).symm (f.app n)
    comm := by
      intro n
      dsimp only [systemDirect] at f
      apply (transition_transpose_iff (S.levelAdj (n + 1)) (S.levelAdj n)
        (S.restrictInverse (Nat.le_succ n)) (S.restrictRight (Nat.le_succ n))
        (S.restrictTranspose (Nat.le_succ n)) (M.transition n) (N.transition n)
        (((S.levelAdj (n + 1)).homEquiv _ _).symm (f.app (n + 1)))
        (((S.levelAdj n).homEquiv _ _).symm (f.app n))).2
      simpa only [Equiv.apply_symm_apply] using f.comm n }
  left_inv f := by
    apply system_hom_ext O ell
    funext n
    exact Equiv.symm_apply_apply _ _
  right_inv f := by
    apply system_hom_ext O ell
    funext n
    exact Equiv.apply_symm_apply _ _

private def systemAdjunction
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    systemInverse O ell L V adj S ⊣ systemDirect O ell L V adj S :=
  Adjunction.mkOfHomEquiv {
    homEquiv := systemHomEquiv O ell L V adj S
    homEquiv_naturality_left_symm := by
      intro M M' N f g
      apply system_hom_ext O ell
      funext n
      exact (S.levelAdj n).homEquiv_naturality_left_symm _ _
    homEquiv_naturality_right := by
      intro M N N' f g
      apply system_hom_ext O ell
      funext n
      exact (S.levelAdj n).homEquiv_naturality_right _ _ }

private instance systemInverse_additive
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    (systemInverse O ell L V adj S).Additive where
  map_add {M N} f g := by
    apply system_hom_ext O ell
    funext n
    change (S.lift n).modules.map
      ((coefficientEvaluation (J := J) n).map (f + g)) =
      (coefficientEvaluation (J := K) n).map
        ((systemInverse O ell L V adj S).map f + (systemInverse O ell L V adj S).map g)
    simp only [Functor.map_add]
    rfl

private instance systemDirect_additive
    (S : CoefficientLevelOrdinaryImage (J := J) (K := K) O ell L V adj) :
    (systemDirect O ell L V adj S).Additive :=
  (systemAdjunction O ell L V adj S).right_adjoint_additive

omit [EssentiallySmall.{w} D] [HasWeakSheafify K (Type w)]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{w})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})] in
private theorem evaluations_jointlyReflect :
    JointlyReflectIsomorphisms (coefficientEvaluation (J := K) (O := O) (ell := ell)) where
  isIso {M N} f hf := by
    have hi (n : ℕ) : IsIso (f.app n) := hf n
    let g : N ⟶ M := {
      app := fun n ↦ inv (f.app n)
      comm := by
        intro n
        apply (cancel_epi (f.app (n + 1))).mp
        simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        rw [f.comm, Category.assoc]
        simp only [← Functor.map_comp, IsIso.hom_inv_id]
        rw [(coefficientRestriction (J := K) O ell (Nat.le_succ n)).map_id]
        exact (Category.comp_id _).symm }
    refine ⟨g, ?_, ?_⟩
    · apply system_hom_ext O ell
      funext n
      change f.app n ≫ inv (f.app n) = 𝟙 _
      exact IsIso.hom_inv_id _
    · apply system_hom_ext O ell
      funext n
      change inv (f.app n) ≫ f.app n = 𝟙 _
      exact IsIso.inv_hom_id _

/-- The geometric morphism acts on strict systems with the ordinary level adjunctions.
Source: Zheng, Construction 4.1, printed p. 21; Stacks 03DA, 03DB and 03D7.

Proof: A constant set sheaf is the coproduct of one terminal sheaf for each element.
The left adjoint L preserves this coproduct and, by left exactness, the terminal sheaf.
The resulting constant-sheaf isomorphism carries each scalar generator to itself.
Transport ring operations and module operations through the finite-product comparison
of L. The scalar-generator equation identifies the transported quotient ring with the
specified constant quotient ring. The underlying-sheaf adjunction restricts to module
maps, since the equations for addition and scalar action transpose to the same equations.
This gives the level right adjoints and their displayed transpose formulas. Kernels
are preserved by left exactness and cokernels by the lifted adjunction, proving exactness.
Restricting a coefficient action before or after this transport gives the same action;
the identity on the underlying sheaf is the restriction comparison. It is compatible
with all quotient maps. Apply these level functors to a system's components and successive
transitions, using that comparison for inverse image and its adjoint mate for direct image.
Transposing the component maps identifies their transition compatibility equations, so
the component adjunctions restrict to the system adjunction with the stated formula.
Kernels and cokernels of strict systems are componentwise, proving system exactness.
Neither regularity nor completeness of the coefficient ring is needed here.
(blueprint: lem-pur-coefficient-system-ordinary-images). -/
theorem coefficientSystemOrdinaryImage_exists [PreservesFiniteLimits L] :
    Nonempty (CoefficientSystemOrdinaryImage (J := J) (K := K) O ell L V adj) := by
  obtain ⟨S⟩ := coefficientLevelOrdinaryImage_exists O ell L V adj
  have hjlim (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := J) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).1
  have hjcolim (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := J) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).2
  have hklim (n : ℕ) : PreservesFiniteLimits
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).1
  have hkcolim (n : ℕ) : PreservesFiniteColimits
      (coefficientEvaluation (J := K) (O := O) (ell := ell) n) :=
    (coefficientEvaluation_exact n).2
  let e (n : ℕ) : systemInverse O ell L V adj S ⋙ coefficientEvaluation (J := K) n ≅
      coefficientEvaluation (J := J) n ⋙ (S.lift n).modules := Iso.refl _
  have he := (evaluations_jointlyReflect O ell (K := K)).exactFunctor_of_iso
    (F := coefficientEvaluation (J := J)) (systemInverse O ell L V adj S)
    (fun n ↦ (S.lift n).modules) (fun n ↦ S.inverseExact n) e
  refine ⟨{
    singleton := S.singleton
    lift := S.lift
    constants := S.constants
    inverseExact := S.inverseExact
    right := S.right
    rightUnderlying := S.rightUnderlying
    levelAdj := S.levelAdj
    levelTranspose := S.levelTranspose
    restrictInverse := S.restrictInverse
    restrictInverseUnderlying := S.restrictInverseUnderlying
    inverse := systemInverse O ell L V adj S
    rightSystem := systemDirect O ell L V adj S
    systemExact := he
    inverseEvaluation := e
    rightEvaluation := fun _ ↦ Iso.refl _
    inverseTransition := ?_
    systemAdj := systemAdjunction O ell L V adj S
    systemTranspose := ?_ }⟩
  · intro n M
    simp only [e, Iso.refl_hom, NatTrans.id_app]
    dsimp only [Functor.comp_obj, coefficientEvaluation, systemInverse]
    simp only [Category.id_comp]
    rfl
  · intro M N f n
    dsimp [systemAdjunction]
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    simp only [systemHomEquiv, Equiv.coe_fn_mk, coefficientEvaluation, e,
      Iso.refl_inv, NatTrans.id_app]
    dsimp only [Functor.comp_obj, systemInverse, systemDirect]
    rw [Category.comp_id, Category.id_comp]

end SheafOfModules
