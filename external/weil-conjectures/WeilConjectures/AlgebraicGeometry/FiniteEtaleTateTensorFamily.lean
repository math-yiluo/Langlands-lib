/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-! # Coherent signed finite Tate tensor powers
Source: Stacks Project, Tag 03PK. (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- The coefficient line has its internal dual as a tensor inverse. -/
def finiteEtaleTateLineInverse (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (hT : IsUnit (m : Γ(T, ⊤))) :
    TensorInverse (finiteEtaleTateLine T m A hA) := by
  let hInv : ∀ t : T, IsUnit (m : T.presheaf.stalk t) := fun t ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ t (by trivial)).hom
  let U := (finiteEtaleTateLine_localTrivial T m hm hInv A hA).choose
  let e := (finiteEtaleTateLine_localTrivial T m hm hInv A hA).choose_spec
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  exact Etale.tensorInverseOfUpperStarIso (ModuleCat.{u + 1} A) U.f U.iUnion_range
    (finiteEtaleTateLine T m A hA) (fun i ↦ (e i).some)

/-- The coherent tensor family on the exact published finite Tate objects. -/
def finiteEtaleTateTensorFamily (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (hT : IsUnit (m : Γ(T, ⊤))) :
    IntTensorFamily (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  NormalizedSignedPowers.signedFamily (finiteEtaleTateTwist T m A hA) rfl (fun _ ↦ rfl)
    (finiteEtaleTateLineInverse T m hm A hA hT)

variable (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (hT : IsUnit (m : Γ(T, ⊤)))

@[simp] theorem finiteEtaleTateTensorFamily_obj :
    (finiteEtaleTateTensorFamily T m hm A hA hT).obj = finiteEtaleTateSheaf A m T hA := rfl

@[simp] theorem finiteEtaleTateTensorFamily_zeroIso :
    (finiteEtaleTateTensorFamily T m hm A hA hT).zeroIso = Iso.refl _ := by
  exact NormalizedSignedPowers.signedFamily_zeroIso _ _ _ _

/-- Multiplication by degree zero is the specified left unitor. -/
theorem finiteEtaleTateTensorFamily_zero_left (a : ℤ) :
    (finiteEtaleTateTensorFamily T m hm A hA hT).addIso 0 a =
      λ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (zero_add a).symm) := by
  apply Iso.ext
  apply (cancel_mono (eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
    (zero_add a)))).1
  simpa only [finiteEtaleTateTensorFamily_obj, finiteEtaleTateTensorFamily_zeroIso,
    Iso.refl_hom, id_whiskerRight,
    Category.id_comp, Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id] using
      ((finiteEtaleTateTensorFamily T m hm A hA hT).zero_left a).symm

/-- Multiplication by degree zero is the specified right unitor. -/
theorem finiteEtaleTateTensorFamily_zero_right (a : ℤ) :
    (finiteEtaleTateTensorFamily T m hm A hA hT).addIso a 0 =
      ρ_ (finiteEtaleTateSheaf A m T hA a) ≪≫
        eqToIso (congrArg (finiteEtaleTateSheaf A m T hA) (add_zero a).symm) := by
  apply Iso.ext
  apply (cancel_mono (eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
    (add_zero a)))).1
  simpa only [finiteEtaleTateTensorFamily_obj, finiteEtaleTateTensorFamily_zeroIso, Iso.refl_hom,
    MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.trans_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
      ((finiteEtaleTateTensorFamily T m hm A hA hT).zero_right a).symm

/-- Adding the final positive factor is literally the identity. -/
theorem finiteEtaleTateTensorFamily_nat_one (n : ℕ) :
    (finiteEtaleTateTensorFamily T m hm A hA hT).addIso (.ofNat (n + 1)) 1 =
      Iso.refl _ := by
  exact NormalizedSignedPowers.signedFamily_positive_one _ _ _ _ n

/-- Pairing opposite positive and negative powers is internal evaluation. -/
theorem finiteEtaleTateTensorFamily_eval (n : ℕ) :
    ((finiteEtaleTateTensorFamily T m hm A hA hT).addIso
      (.ofNat (n + 1)) (.negSucc n)).hom ≫
        eqToHom (congrArg (finiteEtaleTateSheaf A m T hA)
          (add_neg_cancel (Int.ofNat (n + 1)))) =
      (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
        (finiteEtaleTateSheaf A m T hA 0) := by
  exact NormalizedSignedPowers.signedFamily_evaluation _ _ _ _ n

/-- Every signed power is trivial on the same primitive-root cover. -/
theorem finiteEtaleTateSheaf_localTrivial (hm : 0 < m) (hT : IsUnit (m : Γ(T, ⊤))) :
    ∃ U : Cover.{u} etalePrecoverage T, ∀ (i : U.I₀) (a : ℤ),
      Nonempty ((finiteEtaleTateSheaf A m T hA a).over (U.etalePrecoverageToEtale i) ≅
        (constantSheaf (T.smallEtaleTopology.over (U.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A)) := by
  let hInv : ∀ t : T, IsUnit (m : T.presheaf.stalk t) := fun t ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ t (by trivial)).hom
  obtain ⟨U, hU⟩ := finiteEtaleTateLine_localTrivial T m hm hInv A hA
  refine ⟨U, fun i a ↦ ?_⟩
  let P := finiteEtaleTateTensorFamily T m hm A hA hT
  let F := Etale.upperStar (ModuleCat.{u + 1} A) (U.f i)
  let e : F.obj (P.obj 1) ≅ 𝟙_ _ := (hU i).some
  let ei : F.obj (P.obj a) ≅ 𝟙_ _ := IntTensorFamily.iso (P.map F) .constant e a
  let V := U.etalePrecoverageToEtale i
  let E := Etale.overSheafEquiv V (ModuleCat.{u + 1} A)
  let c := (Etale.overEquiv V).constantSheafSheafCongrIso
    (T.smallEtaleTopology.over V) V.left.smallEtaleTopology (ModuleCat.{u + 1} A)
    Over.mkIdTerminal
  exact ⟨E.fullyFaithfulFunctor.preimageIso
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} A) V
      (finiteEtaleTateSheaf A m T hA a) ≪≫ ei ≪≫ (c.app (ModuleCat.of A A)).symm)⟩

/-- The tensor products of signed finite Tate lines are symmetric. -/
theorem finiteEtaleTateTensorFamily_comm (a b : ℤ) :
    (β_ (finiteEtaleTateSheaf A m T hA a) (finiteEtaleTateSheaf A m T hA b)).hom ≫
      ((finiteEtaleTateTensorFamily T m hm A hA hT).addIso b a).hom ≫
      eqToHom (congrArg (finiteEtaleTateSheaf A m T hA) (add_comm b a)) =
        ((finiteEtaleTateTensorFamily T m hm A hA hT).addIso a b).hom := by
  let hInv : ∀ t : T, IsUnit (m : T.presheaf.stalk t) := fun t ↦ by
    simpa only [map_natCast] using hT.map (T.presheaf.germ ⊤ t (by trivial)).hom
  obtain ⟨V, q, hqE, hq, ⟨e⟩⟩ :=
    finiteEtaleTateLine_surjectiveTrivialization T m hm hInv A hA
  have : Etale q := hqE
  have := Etale.faithful_upperStar_of_surjective A q hq
  let F := Etale.upperStar (ModuleCat.{u + 1} A) q
  have : F.Braided := { }
  exact IntTensorFamily.braiding_mul_of_map
    (finiteEtaleTateTensorFamily T m hm A hA hT) F e a b

end AlgebraicGeometry.Scheme
