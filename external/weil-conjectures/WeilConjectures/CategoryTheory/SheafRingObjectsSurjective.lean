/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

private theorem ring_ext {D : Type u} [Category.{v} D]
    [CartesianMonoidalCategory D] [BraidedCategory D]
    (X : D) (r s : CommRingObj X)
    (ha : @AddMonObj.add _ _ _ X r.toRingObj.toAddGrpObj.toAddMonObj =
      @AddMonObj.add _ _ _ X s.toRingObj.toAddGrpObj.toAddMonObj)
    (hz : @AddMonObj.zero _ _ _ X r.toRingObj.toAddGrpObj.toAddMonObj =
      @AddMonObj.zero _ _ _ X s.toRingObj.toAddGrpObj.toAddMonObj)
    (hn : @AddGrpObj.neg _ _ _ X r.toRingObj.toAddGrpObj =
      @AddGrpObj.neg _ _ _ X s.toRingObj.toAddGrpObj)
    (hm : @MonObj.mul _ _ _ X r.toRingObj.toMonObj =
      @MonObj.mul _ _ _ X s.toRingObj.toMonObj)
    (ho : @MonObj.one _ _ _ X r.toRingObj.toMonObj =
      @MonObj.one _ _ _ X s.toRingObj.toMonObj) : r = s := by
  cases r with
  | @mk r rc =>
    cases s with
    | @mk s sc =>
      cases r with
      | @mk rg ra rm rma ram =>
        cases s with
        | @mk sg sa sm sma sam =>
          cases rg with
          | @mk rag rn rnl rnr =>
            cases sg with
            | @mk sag sn snl snr =>
              cases rag
              cases sag
              cases rm
              cases sm
              cases ha
              cases hz
              cases hn
              cases hm
              cases ho
              rfl

private theorem reconstructedRingObjects_eq
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{max u v w})
    (R S : CommRingObjCat (Sheaf J (Type (max u v w))))
    (h : R.X = (sheafCompose J (forget CommRingCat.{max u v w})).obj A)
    (k : S.X = (sheafCompose J (forget CommRingCat.{max u v w})).obj A)
    (hr : ∀ (U : Cᵒᵖ),
        (∀ a b : R.X.obj.obj U,
          (eqToIso h).hom.hom.app U ((AddMonObj.add (X := R.X)).hom.app U (a, b)) =
            (show A.obj.obj U from (eqToIso h).hom.hom.app U a) +
              (show A.obj.obj U from (eqToIso h).hom.hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          (eqToIso h).hom.hom.app U ((AddMonObj.zero (X := R.X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : R.X.obj.obj U,
          (eqToIso h).hom.hom.app U ((AddGrpObj.neg (X := R.X)).hom.app U a) =
            -(show A.obj.obj U from (eqToIso h).hom.hom.app U a)) ∧
        (∀ a b : R.X.obj.obj U,
          (eqToIso h).hom.hom.app U ((MonObj.mul (X := R.X)).hom.app U (a, b)) =
            (show A.obj.obj U from (eqToIso h).hom.hom.app U a) *
              (show A.obj.obj U from (eqToIso h).hom.hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          (eqToIso h).hom.hom.app U ((MonObj.one (X := R.X)).hom.app U t) =
            (1 : A.obj.obj U)))
    (hs : ∀ (U : Cᵒᵖ),
        (∀ a b : S.X.obj.obj U,
          (eqToIso k).hom.hom.app U ((AddMonObj.add (X := S.X)).hom.app U (a, b)) =
            (show A.obj.obj U from (eqToIso k).hom.hom.app U a) +
              (show A.obj.obj U from (eqToIso k).hom.hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          (eqToIso k).hom.hom.app U ((AddMonObj.zero (X := S.X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : S.X.obj.obj U,
          (eqToIso k).hom.hom.app U ((AddGrpObj.neg (X := S.X)).hom.app U a) =
            -(show A.obj.obj U from (eqToIso k).hom.hom.app U a)) ∧
        (∀ a b : S.X.obj.obj U,
          (eqToIso k).hom.hom.app U ((MonObj.mul (X := S.X)).hom.app U (a, b)) =
            (show A.obj.obj U from (eqToIso k).hom.hom.app U a) *
              (show A.obj.obj U from (eqToIso k).hom.hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          (eqToIso k).hom.hom.app U ((MonObj.one (X := S.X)).hom.app U t) =
            (1 : A.obj.obj U))) : R = S := by
  cases R with
  | @mk X r =>
    cases S with
    | @mk Y s =>
      dsimp at h k
      subst X Y
      congr 1
      apply ring_ext
      all_goals
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        apply ConcreteCategory.hom_ext
        intro x
        have hrU := hr U
        have hsU := hs U
        dsimp at hrU hsU
        first
        | exact (hrU.1 x.1 x.2).trans (hsU.1 x.1 x.2).symm
        | exact (hrU.2.1 x).trans (hsU.2.1 x).symm
        | exact (hrU.2.2.1 x).trans (hsU.2.2.1 x).symm
        | exact (hrU.2.2.2.1 x.1 x.2).trans (hsU.2.2.2.1 x.1 x.2).symm
        | exact (hrU.2.2.2.2 x).trans (hsU.2.2.2.2 x).symm


/-- Surjectivity component of internal ring-object reconstruction.
(blueprint: lem-weil-pbc-sheaf-ring-objects-surjective)
Proof in words: Evaluate the internal operations on each section set. The
internal ring diagrams give commutative ring structures, and naturality gives
ring-homomorphic restrictions. The underlying set sheaf therefore carries a
sheaf of commutative rings whose transported operations agree with the given
object by `hops`; extensionality and proof irrelevance identify the resulting
object with the original one, giving a preimage under `F.obj`. -/
theorem sheafRingObjects_surjective
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Sheaf J CommRingCat.{max u v w} ⥤
      CommRingObjCat (Sheaf J (Type (max u v w))))
    (hF : F ⋙ CommRingObjCat.forget _ =
      sheafCompose J (forget CommRingCat.{max u v w}))
    (hops : ∀ (A : Sheaf J CommRingCat.{max u v w}) (U : Cᵒᵖ),
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.add (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) +
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddMonObj.zero (X := (F.obj A).X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((AddGrpObj.neg (X := (F.obj A).X)).hom.app U a) =
            -(show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a)) ∧
        (∀ a b : (F.obj A).X.obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.mul (X := (F.obj A).X)).hom.app U (a, b)) =
            (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U a) *
              (show A.obj.obj U from ((eqToIso hF).hom.app A).hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          ((eqToIso hF).hom.app A).hom.app U ((MonObj.one (X := (F.obj A).X)).hom.app U t) =
            (1 : A.obj.obj U))) :
    Function.Surjective F.obj := by
  intro R
  obtain ⟨A, h, hr⟩ := sheafRingObject_sectionwise_reconstruction J R
  have k : (F.obj A).X = (sheafCompose J (forget CommRingCat.{max u v w})).obj A :=
    congrArg (fun G => G.obj A) hF
  have hk : (eqToIso k).hom = ((eqToIso hF).hom.app A) := by
    exact (eqToHom_app hF A).symm
  refine ⟨A, reconstructedRingObjects_eq J A (F.obj A) R k h ?_ hr⟩
  rw [hk]
  exact hops A

end CategoryTheory
