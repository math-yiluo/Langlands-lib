/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageTensorHom

import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels
import all WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Tate twists with finite coefficients are locally free of rank one

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3) for finite coefficients
(blueprint: definition-tate-twists).

The finite part of `WeilConjectures.AlgebraicGeometry.Tate.TateTwistLocallyFree`, in its own module
so that the finite twists do not depend on the integral, rational and algebraically closed
coefficient clauses.
All positive root levels are indexed by `n + 1`.

## Main definitions

* `tateFiniteLine` is the recorded roots module tensored with a finite coefficient ring.
* `TateSignedLine` states rank one, same-cover triviality and the tensor inverse.
* `TateInverseTwists` fixes the actual functor and negative inverse of an equivalence.

## Main statements

* `tateTwist_finite_locallyFree` states the common cover, the compatible root generators and
  the finite coefficient clauses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u v d c h

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

/-- The constant commutative coefficient sheaf in clause (2).
Source: blueprint clause (2) (blueprint: definition-tate-twists). -/
abbrev tateFiniteCoefficient (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of A)

/-- Apply the canonical quotient coefficient homomorphism to constant sheaves.
Source: blueprint clause (2) (blueprint: definition-tate-twists). -/
def tateFiniteScalar (X : Scheme.{u}) (ℓ : ℕ) (A : Type (u + 1)) [CommRing A]
    (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :
    purTwistFiniteRing X ℓ n ⟶ tateFiniteCoefficient X A :=
  (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (a.comp ULift.ringEquiv.toRingHom))

/-- The finite A-line is exactly the recorded roots module tensored with A_X.
Source: blueprint clauses (2)--(3) (blueprint: definition-tate-twists). -/
def tateFiniteLine (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
    (tateFiniteScalar X ℓ A n a) (purTwistRootsModule X ℓ n)

/-- The normalized pure tensor used to specify the Kummer-induced morphism.
Source: blueprint clause (2) (blueprint: definition-tate-twists). -/
def tateFiniteTensor (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (a : ZMod (ℓ ^ (n + 1)) →+* A)
    (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
    (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)) :
    (tateFiniteLine X ℓ A n a).val.obj (op V) :=
  purScalarSection (purTwistFiniteRing X ℓ n) (tateFiniteCoefficient X A)
    (tateFiniteScalar X ℓ A n a) (purTwistRootsModule X ℓ n) V b x

/-- Signed line clauses on a specified cover: rank one, the same-cover trivializations,
and the positive/negative tensor pairing. All powers and duals are the recorded ones.
Source: blueprint clause (3) (blueprint: definition-tate-twists). -/
def TateSignedLine (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    {I : Type (u + 1)} (U : I → X.ProEt) : Prop :=
  (∀ m : ℤ, (coefficientTwistLine X (R := R) L m).IsFiniteLocallyFreeOfRank 1 ∧
    ∀ i : I, Nonempty ((coefficientTwistLine X (R := R) L m).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X R)).over (U i))) ∧
  ∀ n : ℕ, Nonempty
    ((SheafOfModules.siteSheafTensorRight (A := R)
      (coefficientTwistLine X L (-(n : ℤ)))).obj (coefficientTwistLine X L n) ≅
        SheafOfModules.unit (purTwistRing X R))

/-- The recorded exact tensor model of K(m), now also for an arbitrary finite A-line.
Source: blueprint clause (3), final paragraph
(blueprint: definition-tate-twists). -/
def tateComplexTwist (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    (hL : L.IsFiniteLocallyFreeOfRank 1) (m : ℤ) :
    DerivedCategory (SheafOfModules.{u + 1} (purTwistRing X R)) ⥤
      DerivedCategory (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  letI := hL
  letI := (coefficientTwistLine_exact X L m).1
  letI := (coefficientTwistLine_exact X L m).2.1
  letI := (coefficientTwistLine_exact X L m).2.2
  (SheafOfModules.siteSheafTensorRight (A := R) (coefficientTwistLine X L m)).mapDerivedCategory

/-- Fixing the right input of a published tensor bifunctor retains its full arrow action.
Source: blueprint K(m) formula (blueprint: definition-tate-twists). -/
def tateTensorRight {C : Type c} [Category.{h} C] (T : C × C ⥤ C) (L : C) : C ⥤ C :=
  (𝟭 C).prod' ((Functor.const C).obj L) ⋙ T

/-- An equivalence whose actual functor and inverse are the two prescribed twists.
Source: blueprint clause (3), final sentence
(blueprint: definition-tate-twists). -/
def TateInverseTwists {C : Type c} [Category.{h} C] (F G : C ⥤ C) : Prop :=
  ∃ e : C ≌ C, e.functor = F ∧ e.inverse = G

set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] HasDerivedCategory.standard

private theorem tateAbSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X
attribute [local instance 20000] tateAbSheafify
private theorem tateAbBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X
attribute [local instance 20000] tateAbBijective

private theorem tateWeakSheafify (X : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (tateAbSheafify X).isRightAdjoint
attribute [local instance 20000] tateWeakSheafify

private theorem tateSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance 20000] tateSiteSmall

@[instance_reducible] private def tateDerived (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (SheafOfModules.{u + 1} (purTwistRing X R)) :=
  HasDerivedCategory.standard _
attribute [local instance 20000] tateDerived

private theorem tateLineDerivedInverse (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    (hL : L.IsFiniteLocallyFreeOfRank 1) (m : ℤ) :
    TateInverseTwists.{u + 2, u + 2} (tateComplexTwist.{u} X R L hL m)
      (tateComplexTwist.{u} X R L hL (-m)) := by
  let := hL
  let F : SheafOfModules.{u + 1} (purTwistRing X R) ⥤
      SheafOfModules.{u + 1} (purTwistRing X R) :=
    SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := R) (coefficientTwistLine.{u} X L m)
  let G : SheafOfModules.{u + 1} (purTwistRing X R) ⥤
      SheafOfModules.{u + 1} (purTwistRing X R) :=
    SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := R) (coefficientTwistLine.{u} X L (-m))
  let := (coefficientTwistLine_exact X L m).1
  let := (coefficientTwistLine_exact X L m).2.1
  let := (coefficientTwistLine_exact X L m).2.2
  let := (coefficientTwistLine_exact X L (-m)).1
  let := (coefficientTwistLine_exact X L (-m)).2.1
  let := (coefficientTwistLine_exact X L (-m)).2.2
  have a : F ⋙ G ≅ 𝟭 _ := (signedLineTensor_equivalence.{u} X R L m).2.some
  have b : G ⋙ F ≅ 𝟭 _ := by
    simpa only [neg_neg] using (signedLineTensor_equivalence.{u} X R L (-m)).2.some
  have da : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso _
  have db : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 _ :=
    Functor.mapDerivedCategoryCompIso G F ≪≫
      Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryIdIso _
  exact ⟨CategoryTheory.Equivalence.mk F.mapDerivedCategory G.mapDerivedCategory
    da.symm db, rfl, rfl⟩

private theorem tateSignedLine_of_trivial (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (L : SheafOfModules.{u + 1} (purTwistRing X R))
    [L.IsFiniteLocallyFreeOfRank 1] {I : Type (u + 1)} (U : I → X.ProEt)
    (h : ∀ i, Nonempty (L.over (U i) ≅ (SheafOfModules.unit.{u, u + 1, u + 1} _).over (U i))) :
    TateSignedLine X R L U := by
  constructor
  · intro m
    refine ⟨(signedLineTensor_equivalence.{u} X R L m).1, fun i ↦ ?_⟩
    exact ⟨lineSignedOverUnit X R L (U i) (h i).some m⟩
  · intro n
    let C := SheafOfModules.{u + 1} (purTwistRing X R)
    let P := coefficientTwistLine.{u} X (R := R) L (n : ℤ)
    let Q := coefficientTwistLine.{u} X (R := R) L (-(n : ℤ))
    have a := (signedLineTensor_equivalence.{u} X R L (n : ℤ)).2.some
    have e : (SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) P).obj
        (SheafOfModules.unit.{u, u + 1, u + 1} _) ≅ P := by
      let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
      let := SheafOfModules.isMonoidal_W_independentCoefficients.{u + 1, u, u + 1} R
      let := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
      exact (SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1} R P).app _ ≪≫
        MonoidalCategory.leftUnitor P
    exact ⟨(SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1}
      (A := R) Q).mapIso e.symm ≪≫
      a.app (SheafOfModules.unit.{u, u + 1, u + 1} _)⟩

private noncomputable def tateResidueLinearLift (X : Scheme.{u}) (ℓ n : ℕ)
    (M P : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n)))
    (f : (SheafOfModules.toSheaf _).obj M ⟶ (SheafOfModules.toSheaf _).obj P) : M ⟶ P := by
  let a := Functor.whiskerRight (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  have : Presheaf.IsLocallySurjective (ProEt.topology X) a := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology X)
      (Functor.whiskerRight (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (n + 1)))))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  let g : (PresheafOfModules.restrictScalars a).obj M.val ⟶
      (PresheafOfModules.restrictScalars a).obj P.val :=
    PresheafOfModules.homMk f.hom (by
      intro V b x
      obtain ⟨b⟩ := b
      obtain ⟨z, rfl⟩ := ZMod.intCast_surjective b
      change f.hom.app V
          (@SMul.smul _ _ (M.val.obj V).isModule.toSMul
            (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) x) =
        @SMul.smul _ _ (P.val.obj V).isModule.toSMul
          (a.app V (z : ULift.{u + 1} (ZMod (ℓ ^ (n + 1))))) (f.hom.app V x)
      rw [map_intCast]
      calc
        _ = f.hom.app V (z • (x : M.val.obj V)) := congrArg (f.hom.app V)
          (@Int.cast_smul_eq_zsmul ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
            (M.val.obj V) _ _ (M.val.obj V).isModule z x)
        _ = z • f.hom.app V x := (f.hom.app V).hom.map_zsmul z x
        _ = _ := (@Int.cast_smul_eq_zsmul
          ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj V)
          (P.val.obj V) _ _ (P.val.obj V).isModule z (f.hom.app V x)).symm)
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a P.isSheaf).symm g⟩

private theorem tateRootTransition_comp (X : Scheme.{u}) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ∣ b) (hbc : b ∣ c) :
    proEtaleRootsOfUnityTransition X b c hb hc hbc ≫
        proEtaleRootsOfUnityTransition X a b ha hb hab =
      proEtaleRootsOfUnityTransition X a c ha hc (hab.trans hbc) := by
  have : Mono (proEtaleRootsOfUnityInclusion X a) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  apply (cancel_mono (proEtaleRootsOfUnityInclusion X a)).mp
  simp only [proEtaleRootsOfUnityInclusion, proEtaleRootsOfUnityTransition,
    Category.assoc, kernel.lift_ι, Preadditive.comp_nsmul,
    Category.comp_id, smul_smul]
  change (b / a * (c / b)) • kernel.ι (proEtaleUnitsPower X c) =
    (c / a) • kernel.ι (proEtaleUnitsPower X c)
  exact congrArg (fun q : ℕ ↦ q • kernel.ι (proEtaleUnitsPower X c))
    ((Nat.mul_comm _ _).trans (Nat.div_mul_div hbc hab))

private theorem tateRootTransition_self (X : Scheme.{u}) (a : ℕ) (ha : 0 < a) :
    proEtaleRootsOfUnityTransition X a a ha ha (dvd_refl a) = 𝟙 _ := by
  have : Mono (proEtaleRootsOfUnityInclusion X a) := by
    dsimp [proEtaleRootsOfUnityInclusion]
    infer_instance
  apply (cancel_mono (proEtaleRootsOfUnityInclusion X a)).mp
  simp only [proEtaleRootsOfUnityInclusion, proEtaleRootsOfUnityTransition,
    kernel.lift_ι, Nat.div_self ha, one_smul, Category.comp_id, Category.id_comp]

private theorem tateRootTransition_generator (X : Scheme.{u}) (ℓ : ℕ)
    [Fact ℓ.Prime] (V : X.ProEt)
    (ζ : ∀ n : ℕ, (purTwistRootsModule X ℓ n).val.obj (op V))
    (hζ : ∀ n : ℕ,
      (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op V) (ζ (n + 1)) = ζ n)
    (r n : ℕ) (hrn : r ≤ n) :
    (proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) (ζ n) = ζ r := by
  induction n, hrn using Nat.le_induction with
  | base =>
    rw [tateRootTransition_self]
    rfl
  | succ n hn ih =>
    have h := tateRootTransition_comp X (ℓ ^ (r + 1))
      (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hn))
      (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))
    let t := proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hn))
    have hh := congrArg (fun f ↦ f.hom.app (op V) (ζ (n + 1))) h
    change t.hom.app (op V)
      ((proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op V) (ζ (n + 1))) =
        (proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op V) (ζ (n + 1)) at hh
    exact hh.symm.trans ((congrArg (t.hom.app (op V)) (hζ n)).trans ih)

private noncomputable def tateKummerMap (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    tateFiniteLine X ℓ A n
      (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
        (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a := by
  let an := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
    (ZMod (ℓ ^ (r + 1))))
  let α := tateFiniteScalar X ℓ A n an
  let β := tateFiniteScalar X ℓ A r a
  let H : SheafOfModules.{u + 1} (purTwistRing X (tateFiniteCoefficient X A)) :=
    tateFiniteLine X ℓ A r a
  let P : SheafOfModules.{u + 1} (purTwistRing X (purTwistFiniteRing X ℓ n)) :=
    (SheafOfModules.restrictScalars
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map α)).obj H
  let φ := proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
    (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
    (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
  let η := (PurScalar.tensorAdjunction.{u + 1, u + 1, u}
    (K := ProEt.topology X) β).unit.app (purTwistRootsModule X ℓ r)
  let q : (SheafOfModules.toSheaf _).obj (purTwistRootsModule X ℓ n) ⟶
      (SheafOfModules.toSheaf _).obj P :=
    φ ≫ (SheafOfModules.toSheaf _).map η
  exact SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} α (purTwistRootsModule X ℓ n) H
    (tateResidueLinearLift X ℓ n _ P q)

private theorem tateKummerMap_tmul (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) (V : X.ProEt)
    (b : (tateFiniteCoefficient X A).obj.obj (op V))
    (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)) :
    (tateKummerMap X ℓ A r n hrn a).val.app (op V)
      (tateFiniteTensor X ℓ A n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
          (ZMod (ℓ ^ (r + 1))))) V b x) =
      tateFiniteTensor X ℓ A r a V b
        ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x) := by
  unfold tateKummerMap
  erw [SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}]
  change b • (show (tateFiniteLine X ℓ A r a).val.obj (op V) from
    (((PurScalar.tensorAdjunction.{u + 1, u + 1, u}
    (K := ProEt.topology X) (tateFiniteScalar X ℓ A r a)).unit.app
      (purTwistRootsModule X ℓ r)).val.app (op V)
        ((proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op V) x))) = _
  rw [PurScalar.tensorUnit_section]
  change b • SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
    (tateFiniteScalar X ℓ A r a) (purTwistRootsModule X ℓ r) (op V) 1 _ =
      SheafOfModules.scalarExtensionSection.{u + 1, u, u + 1, u + 1}
        (tateFiniteScalar X ℓ A r a) (purTwistRootsModule X ℓ r) (op V) b _
  rw [SheafOfModules.scalarExtensionSection_smul.{u + 1, u, u + 1, u + 1}, mul_one]

private theorem tateKummerMap_localIso (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (V : X.ProEt)
    (ζ : ∀ n : ℕ, (purTwistRootsModule X ℓ n).val.obj (op V))
    (e : ∀ n : ℕ,
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over V ≅
        (purTwistRootsModule X ℓ n).over V)
    (he : ∀ (n : ℕ) (W : (Over V)ᵒᵖ)
      (b : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over V).obj.obj W),
      (e n).hom.val.app W b =
        b • (purTwistRootsModule X ℓ n).val.map W.unop.hom.op (ζ n))
    (r n : ℕ) (hrn : r ≤ n) (a : ZMod (ℓ ^ (r + 1)) →+* A)
    (hζ : (proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) (ζ n) = ζ r) :
    IsIso ((tateKummerMap X ℓ A r n hrn a).over V) := by
  let an := a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
    (ZMod (ℓ ^ (r + 1))))
  let en := SheafOfModules.extendedBasisIso.{u + 1, u, u + 1}
    (tateFiniteScalar X ℓ A n an) (purTwistRootsModule X ℓ n) (e n).symm
  let er := SheafOfModules.extendedBasisIso.{u + 1, u, u + 1}
    (tateFiniteScalar X ℓ A r a) (purTwistRootsModule X ℓ r) (e r).symm
  have h : en.inv ≫ (tateKummerMap X ℓ A r n hrn a).over V = er.inv := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (tateKummerMap X ℓ A r n hrn a).val.app (op W.unop.left)
        (tateFiniteTensor X ℓ A n an W.unop.left b
          ((e n).hom.val.app W
            (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over V).obj.obj W))) =
      tateFiniteTensor X ℓ A r a W.unop.left b ((e r).hom.val.app W
        (1 : ((purTwistRing X (purTwistFiniteRing X ℓ r)).over V).obj.obj W))
    rw [he n W 1, he r W 1, one_smul, one_smul, tateKummerMap_tmul]
    have hn := NatTrans.naturality_apply
      (proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom W.unop.hom.op (ζ n)
    rw [hζ] at hn
    exact congrArg (tateFiniteTensor X ℓ A r a W.unop.left b) hn
  have hk : (tateKummerMap X ℓ A r n hrn a).over V = en.hom ≫ er.inv := by
    rw [← cancel_epi en.inv, h, ← Category.assoc, en.inv_hom_id, Category.id_comp]
  rw [hk]
  infer_instance

private theorem tateFiniteTrivial (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (he : ∀ i, Nonempty ((purTwistRootsModule X ℓ r).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ r))).over (U i))) :
    ∀ i, Nonempty ((tateFiniteLine X ℓ A r a).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X (tateFiniteCoefficient X A))).over (U i)) := by
  intro i
  exact ⟨SheafOfModules.extendedBasisIso.{u + 1, u, u + 1} (tateFiniteScalar X ℓ A r a)
    (purTwistRootsModule X ℓ r) (he i).some⟩

private theorem tateFiniteSigned (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A)
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (he : ∀ i, Nonempty ((purTwistRootsModule X ℓ r).over (U i) ≅
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ r))).over (U i))) :
    ∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
      TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
      ∀ n : ℕ, TateInverseTwists
        (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
        (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
          (-(n : ℤ))) := by
  have ht := tateFiniteTrivial X ℓ A r a U he
  let hL := rank_one_of_cover (tateFiniteLine X ℓ A r a) ⟨I, U, f, hc, ht⟩
  let := hL
  exact ⟨hL, tateSignedLine_of_trivial X _ _ U ht,
    fun n ↦ tateLineDerivedInverse X _ _ hL n⟩

private theorem tateFiniteClause (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {I : Type (u + 1)} (U : I → X.ProEt)
    (f : ∀ i, U i ⟶ ProEt.mk (𝟙 X))
    (hc : Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _)
    (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
    (e : ∀ (n : ℕ) (i : I),
      (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
        (purTwistRootsModule X ℓ n).over (U i))
    (hζ : ∀ (n : ℕ) (i : I),
      (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
        (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
        (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i)) (ζ (n + 1) i) = ζ n i)
    (he : ∀ (n : ℕ) (i : I) (W : (Over (U i))ᵒᵖ)
      (b : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj W),
      (e n i).hom.val.app W b =
        b • (purTwistRootsModule X ℓ n).val.map W.unop.hom.op (ζ n i)) :
    ∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ)))) := by
  intro A _ _ r hA
  have hz : (ℓ ^ (r + 1) : A) = 0 := by
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_pow] using hA 1
  let a : ZMod (ℓ ^ (r + 1)) →+* A :=
    ZMod.castHom (ringChar.dvd (show ((ℓ ^ (r + 1) : ℕ) : A) = 0 by
      simpa only [Nat.cast_pow] using hz)) A
  refine ⟨a, ?_, tateFiniteSigned X ℓ A r a U f hc (fun i ↦ ⟨(e r i).symm⟩)⟩
  intro n hrn
  refine ⟨tateKummerMap X ℓ A r n hrn a, ?_, tateKummerMap_tmul X ℓ A r n hrn a⟩
  have hU : (ProEt.topology X).CoversTop U := by
    let hT : IsTerminal (ProEt.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  let k := tateKummerMap X ℓ A r n hrn a
  have hk (i : I) : IsIso (k.over (U i)) :=
    tateKummerMap_localIso X ℓ A (U i) (fun m ↦ ζ m i) (fun m ↦ e m i)
      (fun m ↦ he m i) r n hrn a
      (tateRootTransition_generator X ℓ (U i) (fun m ↦ ζ m i) (fun m ↦ hζ m i) r n hrn)
  have hg : IsIso ((SheafOfModules.toSheaf _).map k) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    have := hk i
    exact inferInstanceAs (IsIso ((SheafOfModules.toSheaf _).map (k.over (U i))))
  exact isIso_of_reflects_iso k (SheafOfModules.toSheaf _)

private theorem tateRootCover (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ i, Nonempty ((purTwistZlModule X ℓ).over (U i) ≅
        (SheafOfModules.unit (purTwistRing X (purTwistZlCompletion X ℓ))).over (U i))) := by
  classical
  obtain ⟨I, U, f, hc, hq⟩ := localTowerCover X ℓ
  let e (n : ℕ) (i : I) := (finiteIsoOfAbIso X ℓ n (U i)
    ((hq i).some.app (op n))).symm
  let ζ (n : ℕ) (i : I) :=
    (e n i).hom.val.app (op (Over.mk (𝟙 (U i))))
      (1 : (purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj (op (U i)))
  refine ⟨I, U, f, ζ, e, hc, ?_, ?_, fun i ↦ ⟨completedBasis X ℓ (U i) (hq i).some⟩⟩
  · intro n i
    have h := (hq i).some.inv.naturality (homOfLE (Nat.le_succ n)).op
    have hh := congrArg (fun t ↦ t.hom.app (op (Over.mk (𝟙 (U i))))
      (1 : (purTwistRing X (purTwistFiniteRing X ℓ (n + 1))).obj.obj (op (U i)))) h
    change (proEtaleRootsOfUnityTransition X _ _ _ _ _).hom.app (op (U i))
      (((hq i).some.inv.app (op (n + 1))).hom.app
        (op (Over.mk (𝟙 (U i))))
        (1 : (purTwistRing X (purTwistFiniteRing X ℓ (n + 1))).obj.obj (op (U i)))) =
      ((hq i).some.inv.app (op n)).hom.app (op (Over.mk (𝟙 (U i))))
        (1 : (purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj (op (U i)))
    simp only [proEtaleRootsOfUnityTower, purTwistZlTower,
      Functor.comp_map,
      Functor.ofOpSequence_map_homOfLE_succ] at hh
    change ((hq i).some.inv.app (op n)).hom.app
      (op (Over.mk (𝟙 (U i))))
      ((purTwistFiniteTransition X ℓ n).hom.app (op (U i)) 1) = _ at hh
    rw [map_one] at hh
    exact hh.symm
  · intro n i V a
    have h := PresheafOfModules.naturality_apply (e n i).hom.val
      (Over.homMk V.unop.hom (Category.comp_id _) :
        V.unop ⟶ Over.mk (𝟙 (U i))).op
      (1 : (purTwistRing X (purTwistFiniteRing X ℓ n)).obj.obj (op (U i)))
    have h1 : (e n i).hom.val.app V
        (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V) =
        (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i) := by
      change (e n i).hom.val.app V
        ((purTwistRing X (purTwistFiniteRing X ℓ n)).obj.map V.unop.hom.op 1) = _ at h
      rw [map_one] at h
      exact h
    calc
      _ = (e n i).hom.val.app V
          (a • (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V)) :=
        by simp
      _ = a • (e n i).hom.val.app V
        (1 : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V) := map_smul _ _ _
      _ = _ := congrArg (a • ·) h1

/-- The finite part of `tateTwist_locallyFree`: one common covering with compatible root
generators and unit-to-root basis isomorphisms, and for every finite coefficient ring the
Kummer transitions and the signed finite lines. No integral, rational or algebraically
closed coefficient is involved.

Source: `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/
sk-def-sp-tate-twist-locally-free.md`, clauses (1)--(3) for finite coefficients
(blueprint: definition-tate-twists).

Proof: the compatible root-tower local model gives the cover, the generators and the
basis isomorphisms with their transition and slice formulas. For a finite ring A killed
by ℓ^(r+1), the unique quotient map, the Kummer maps (isomorphisms on the cover, hence
globally) and the signed finite lines are the finite clause. -/
theorem tateTwist_finite_locallyFree
    (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)] :
    ∃ (I : Type (u + 1)) (U : I → X.ProEt)
      (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 X))
      (ζ : ∀ (n : ℕ) (i : I), (purTwistRootsModule X ℓ n).val.obj (op (U i)))
      (e : ∀ (n : ℕ) (i : I),
        (SheafOfModules.unit (purTwistRing X (purTwistFiniteRing X ℓ n))).over (U i) ≅
          (purTwistRootsModule X ℓ n).over (U i)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _ ∧
      (∀ (n : ℕ) (i : I),
        (proEtaleRootsOfUnityTransition X (ℓ ^ (n + 1)) (ℓ ^ (n + 2))
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ (Nat.le_succ (n + 1)))).hom.app (op (U i))
            (ζ (n + 1) i) = ζ n i) ∧
      (∀ (n : ℕ) (i : I) (V : (Over (U i))ᵒᵖ)
        (a : ((purTwistRing X (purTwistFiniteRing X ℓ n)).over (U i)).obj.obj V),
        (e n i).hom.val.app V a =
          a • (purTwistRootsModule X ℓ n).val.map V.unop.hom.op (ζ n i)) ∧
      (∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
        (∀ a : A, (ℓ ^ (r + 1)) • a = 0) →
        ∃ a : ZMod (ℓ ^ (r + 1)) →+* A,
          (∀ (n : ℕ) (hrn : r ≤ n),
            ∃ k : tateFiniteLine X ℓ A n
                (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                  (ZMod (ℓ ^ (r + 1))))) ⟶ tateFiniteLine X ℓ A r a,
              IsIso k ∧
              ∀ (V : X.ProEt) (b : (tateFiniteCoefficient X A).obj.obj (op V))
                (x : (proEtaleRootsOfUnitySheaf X (ℓ ^ (n + 1))).obj.obj (op V)),
                k.val.app (op V)
                  (tateFiniteTensor X ℓ A n
                    (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
                      (ZMod (ℓ ^ (r + 1))))) V b x) =
                  tateFiniteTensor X ℓ A r a V b
                    ((proEtaleRootsOfUnityTransition X (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
                      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
                      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))).hom.app (op V) x)) ∧
          (∃ hL : (tateFiniteLine X ℓ A r a).IsFiniteLocallyFreeOfRank 1,
            TateSignedLine X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) U ∧
            ∀ n : ℕ, TateInverseTwists
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL n)
              (tateComplexTwist X (tateFiniteCoefficient X A) (tateFiniteLine X ℓ A r a) hL
                (-(n : ℤ))))) := by
  obtain ⟨I, U, f, ζ, e, hc, hζ, he, _⟩ := tateRootCover X ℓ
  exact ⟨I, U, f, ζ, e, hc, hζ, he, tateFiniteClause X ℓ U f hc ζ e hζ he⟩

end AlgebraicGeometry.Scheme
