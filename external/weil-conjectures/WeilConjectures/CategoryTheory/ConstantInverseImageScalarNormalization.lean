/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import WeilConjectures.CategoryTheory.ConstantRingSectionRigidity

/-! # Constant scalars in an algebraic inverse-image lift

Source: Stacks Project, Tags 00YV and 03D2; the constant-coefficient calculation
in Step 2 of lem-sf-constant-open-restriction-model-comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantCompletion

private noncomputable abbrev ringSets {C : Type u} [SmallCategory C] (J : GrothendieckTopology C) :=
  sheafCompose J (forget CommRingCat.{u})

private noncomputable def constantEnd {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (A : Type u) [CommRing A] (a : A) :
    (ringSets J).obj (constant J A) ⟶ (ringSets J).obj (constant J A) where
  hom :=
    { app := fun U ↦ ↾fun _ ↦
        (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a
      naturality := by
        intro U V f
        ext x
        exact ConcreteCategory.congr_hom
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).naturality f) a }

private noncomputable abbrev scalar {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)}
    (F : InverseImageData L) (A : Type u) [CommRing A] :=
  (F.algebra (constant J A)).ringUnderlying.hom ≫ (ringSets K).map (constantMap F A)

private theorem constantAdjunct_eval
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ G.sheafPushforwardContinuous (Type u) J K)
    (F : InverseImageData L) (A : Type u) [CommRing A] (U : Cᵒᵖ) (a : A) :
    (adj.homEquiv _ _ (scalar F A)).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a) =
      (constantMap F A).hom.app (G.op.obj U)
        ((F.algebra (constant J A)).ringUnderlying.hom.hom.app (G.op.obj U)
          ((L.map (constantEnd J A a)).hom.app (G.op.obj U)
            ((adj.unit.app ((ringSets J).obj (constant J A))).hom.app U
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U 0)))) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.hom.app U) (adj.unit.naturality (constantEnd J A a)))
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U 0)
  rw [adj.homEquiv_unit]
  change (constantMap F A).hom.app (G.op.obj U)
      ((F.algebra (constant J A)).ringUnderlying.hom.hom.app (G.op.obj U)
        ((adj.unit.app ((ringSets J).obj (constant J A))).hom.app U
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a))) = _
  exact congrArg (fun x ↦ (constantMap F A).hom.app (G.op.obj U)
    ((F.algebra (constant J A)).ringUnderlying.hom.hom.app (G.op.obj U) x)) h

private noncomputable def constantAdjunctRingHom
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ G.sheafPushforwardContinuous (Type u) J K)
    (F : InverseImageData L) (U : Cᵒᵖ) (A : CommRingCat.{u}) :
    A ⟶ (constant K A).obj.obj (G.op.obj U) := by
  let T := (ringSets J).obj (constant J A)
  let x : (L.obj T).obj.obj (G.op.obj U) :=
    ((adj.unit.app T).hom.app U)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U 0)
  let t (a : A) : (F.rings.obj (constant J A)).obj.obj (G.op.obj U) :=
    (F.algebra (constant J A)).ringUnderlying.hom.hom.app (G.op.obj U)
      ((L.map (constantEnd J A a)).hom.app (G.op.obj U) x)
  have hzero : t 0 = 0 :=
    (F.algebra (constant J A)).ringZero T (constantEnd J A 0)
      (by
        intro V y
        exact map_zero
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app V).hom) (G.op.obj U) x
  have hone : t 1 = 1 :=
    (F.algebra (constant J A)).ringOne T (constantEnd J A 1)
      (by
        intro V y
        exact map_one
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app V).hom) (G.op.obj U) x
  have hadd (a b : A) : t (a + b) = t a + t b :=
    (F.algebra (constant J A)).ringAdd T (constantEnd J A a)
      (constantEnd J A b) (constantEnd J A (a + b))
      (by
        intro V y
        exact map_add
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app V).hom
          a b) (G.op.obj U) x
  have hmul (a b : A) : t (a * b) = t a * t b :=
    (F.algebra (constant J A)).ringMul T (constantEnd J A a)
      (constantEnd J A b) (constantEnd J A (a * b))
      (by
        intro V y
        exact map_mul
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app V).hom
          a b) (G.op.obj U) x
  exact CommRingCat.ofHom
    { toFun := fun a ↦ (adj.homEquiv _ _ (scalar F A)).hom.app U
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).app U a)
      map_zero' := by
        rw [constantAdjunct_eval J K G L adj F A U 0]
        change (constantMap F A).hom.app (G.op.obj U) (t 0) = 0
        rw [hzero, map_zero]
      map_one' := by
        rw [constantAdjunct_eval J K G L adj F A U 1]
        change (constantMap F A).hom.app (G.op.obj U) (t 1) = 1
        rw [hone, map_one]
      map_add' := by
        intro a b
        rw [constantAdjunct_eval J K G L adj F A U (a + b),
          constantAdjunct_eval J K G L adj F A U a,
          constantAdjunct_eval J K G L adj F A U b]
        change (constantMap F A).hom.app (G.op.obj U) (t (a + b)) =
          (constantMap F A).hom.app (G.op.obj U) (t a) +
            (constantMap F A).hom.app (G.op.obj U) (t b)
        rw [hadd, map_add]
      map_mul' := by
        intro a b
        rw [constantAdjunct_eval J K G L adj F A U (a * b),
          constantAdjunct_eval J K G L adj F A U a,
          constantAdjunct_eval J K G L adj F A U b]
        change (constantMap F A).hom.app (G.op.obj U) (t (a * b)) =
          (constantMap F A).hom.app (G.op.obj U) (t a) *
            (constantMap F A).hom.app (G.op.obj U) (t b)
        rw [hmul, map_mul] }

private theorem scalar_naturality
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type u) ⥤ Sheaf K (Type u)} (F : InverseImageData L)
    {A B : CommRingCat.{u}} (f : A ⟶ B) :
    L.map ((ringSets J).map ((constantSheaf J CommRingCat.{u}).map f)) ≫ scalar F B =
      scalar F A ≫ (ringSets K).map ((constantSheaf K CommRingCat.{u}).map f) := by
  have hr :
      L.map ((ringSets J).map ((constantSheaf J CommRingCat.{u}).map f)) ≫
          (F.algebra (constant J B)).ringUnderlying.hom =
        (F.algebra (constant J A)).ringUnderlying.hom ≫
          (ringSets K).map (F.rings.map ((constantSheaf J CommRingCat.{u}).map f)) :=
    F.ring_naturality ((constantSheaf J CommRingCat.{u}).map f)
  dsimp only [scalar]
  rw [← Category.assoc, hr]
  simp only [Category.assoc, ← Functor.map_comp]
  exact congrArg (fun t ↦ (F.algebra (constant J A)).ringUnderlying.hom ≫
    (ringSets K).map t) (F.constants.hom.naturality f)

private theorem constantAdjunctRingHom_naturality
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ G.sheafPushforwardContinuous (Type u) J K)
    (F : InverseImageData L) (U : Cᵒᵖ)
    {A B : CommRingCat.{u}} (f : A ⟶ B) :
    f ≫ constantAdjunctRingHom J K G L adj F U B =
      constantAdjunctRingHom J K G L adj F U A ≫
        ((constantSheaf K CommRingCat.{u}).map f).hom.app (G.op.obj U) := by
  have hn :
      (ringSets J).map ((constantSheaf J CommRingCat.{u}).map f) ≫
          adj.homEquiv _ _ (scalar F B) =
        adj.homEquiv _ _ (scalar F A) ≫
          (G.sheafPushforwardContinuous (Type u) J K).map
            ((ringSets K).map ((constantSheaf K CommRingCat.{u}).map f)) := by
    rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
    exact congrArg (adj.homEquiv _ _) (scalar_naturality F f)
  apply CommRingCat.hom_ext
  ext a
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f)) U) a
  have h := ConcreteCategory.congr_hom (congrArg (fun f ↦ f.hom.app U) hn)
    ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U a)
  change (adj.homEquiv _ _ (scalar F B)).hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U (f a)) = _
  exact (congrArg ((adj.homEquiv _ _ (scalar F B)).hom.app U) hu).trans h

/-- The scalar map of an algebraic inverse-image lift on constant rings is the
transpose of the constant-section map. This concerns only the coefficient ring,
not modules, site equivalences, open immersions or extension by zero.

Source: Stacks Project, Tags 00YV and 03D2; Step 2 of
lem-sf-constant-open-restriction-model-comparison.
(auxiliary; not a blueprint node).

Proof: the finite-product graph equations identify the algebraic ring lift with
transport of ring objects through L. A left exact left adjoint preserves the
terminal sheaf and its coproducts, so its canonical comparison on constant sets
preserves every constant section. The induced comparison of constant ring
objects is natural in the coefficient ring. The composite of any other natural
constant-ring comparison with the inverse canonical comparison is the identity:
locally on the target, its value at the universal element of Z[X] is a
polynomial p. Its component at Z is the identity because the constant Z ring
sheaf is initial. If p differs from X, choose an integer n with p(n) different
from n. Naturality under evaluation at n equates these distinct constant
integer sections. Local injectivity of sheafification forces this piece to
have an empty covering sieve, where all sections already agree. Hence p is X
on every relevant piece. Naturality under Z[X] to A, X to a, fixes every a.
Thus F.constants is this canonical
comparison, including when the topos is empty. Precompose the asserted
transpose equality with the constant-presheaf sheafification unit. Both sides
send a to that constant section in the target. The sheafification adjunction
and the geometric adjunction give the displayed equality. -/
theorem constantInverseImageScalarNormalization
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ G.sheafPushforwardContinuous (Type u) J K)
    [PreservesFiniteLimits L] (F : InverseImageData L) (A : Type u) [CommRing A] :
    (F.algebra (constant J A)).ringUnderlying.hom ≫
        (sheafCompose K (forget CommRingCat.{u})).map (constantMap F A) =
      (adj.homEquiv _ _).symm
        ((sheafCompose J (forget CommRingCat.{u})).map
          (((sheafificationAdjunction J CommRingCat.{u}).homEquiv
            ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))
            ((G.sheafPushforwardContinuous CommRingCat.{u} J K).obj
              (constant K A))).symm
            (Functor.whiskerLeft G.op
              (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A)))))) := by
  let ρ : constant J A ⟶
      (G.sheafPushforwardContinuous CommRingCat.{u} J K).obj (constant K A) :=
    ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).symm
      (Functor.whiskerLeft G.op
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))))
  have hρ : toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of A)) ≫ ρ.hom =
      Functor.whiskerLeft G.op
        (toSheafify K ((Functor.const Dᵒᵖ).obj (CommRingCat.of A))) :=
    ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).apply_symm_apply _
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  change adj.homEquiv _ _ (scalar F A) = (ringSets J).map ρ
  apply Sheaf.hom_ext
  apply (cancel_epi
    (sheafifyComposeIso J (forget CommRingCat.{u})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of A))).hom).mp
  apply sheafify_hom_ext J _ _
    ((G.sheafPushforwardContinuous (Type u) J K).obj
      ((ringSets K).obj (constant K A))).property
  simp only [← Category.assoc, sheafComposeIso_hom_fac]
  apply NatTrans.ext
  funext U
  ext a
  have h := constantRingSectionRigidity K (G.op.obj U)
    (constantAdjunctRingHom J K G L adj F U)
    (fun f ↦ constantAdjunctRingHom_naturality J K G L adj F U f)
    (CommRingCat.of A)
  have ha := ConcreteCategory.congr_hom h a
  have hb := ConcreteCategory.congr_hom (NatTrans.congr_app hρ U) a
  exact ha.trans hb.symm

end CategoryTheory.ConstantCompletion
