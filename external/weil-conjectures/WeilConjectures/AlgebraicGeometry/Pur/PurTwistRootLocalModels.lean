/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

import all WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import all WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Point.Over
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso

/-! # Compatible local bases of the root tower

## References

* Stacks Project, Tags 03PK and 03RV
* Bhatt--Scholze, Sections 6.5 and 6.8
-/

@[expose] public section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def rootRawPresheafIso (S : Scheme.{u}) (N : ℕ) :
    (proEtaleRootsOfUnitySheaf S N).obj ≅ ProEtale.rootsOfUnityPresheaf S N := by
  let e (U : S.ProEtᵒᵖ) :=
    (proEtaleRootsOfUnitySections S N U).trans AddEquiv.ulift.symm
  exact (show (proEtaleRootsOfUnitySheaf S N).obj ≅ ProEtale.rootsOfUnityPresheaf S N from
    NatIso.ofComponents (fun U ↦ (e U).toAddCommGrpIso) (by
      intro U V f
      ext x
      apply ULift.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      have hU := (existsUnique_proEtaleRootsOfUnitySections S N U).exists.choose_spec x
      have hV := (existsUnique_proEtaleRootsOfUnitySections S N V).exists.choose_spec
        ((proEtaleRootsOfUnitySheaf S N).obj.map f x)
      have h := NatTrans.naturality_apply (proEtaleRootsOfUnityInclusion S N).hom f x
      change _ = _ at h
      rw [← hU, ← hV] at h
      exact congrArg (fun y ↦ y.down.toMul) h) )

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def rawRootIso (S : Scheme.{u}) (N : ℕ) :
    proEtaleRootsOfUnitySheaf S N ≅ ProEtale.rootsOfUnitySheaf S N :=
  sheafificationIso _ ≪≫ (presheafToSheaf _ _).mapIso (rootRawPresheafIso S N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def moduleIsoOfAddIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (N : ℕ) (R : Sheaf J RingCat.{u + 1})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1} (ZMod N))) ⟶ R.obj)
    [Presheaf.IsLocallySurjective J a]
    (M P : SheafOfModules.{u + 1} R)
    (e : (SheafOfModules.toSheaf R).obj M ≅ (SheafOfModules.toSheaf R).obj P) : M ≅ P := by
  let lift (M P : SheafOfModules.{u + 1} R)
      (f : (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj P) :
      M ⟶ P := by
    let g : (PresheafOfModules.restrictScalars a).obj M.val ⟶
        (PresheafOfModules.restrictScalars a).obj P.val :=
      PresheafOfModules.homMk f.hom (by
        intro U b x
        obtain ⟨b⟩ := b
        obtain ⟨z, rfl⟩ := ZMod.intCast_surjective b
        change f.hom.app U
            (@SMul.smul _ _ (M.val.obj U).isModule.toSMul
              (a.app U (z : ULift.{u + 1} (ZMod N))) x) =
          @SMul.smul _ _ (P.val.obj U).isModule.toSMul
            (a.app U (z : ULift.{u + 1} (ZMod N))) (f.hom.app U x)
        rw [map_intCast]
        calc
          _ = f.hom.app U (z • (x : M.val.obj U)) := congrArg (f.hom.app U)
            (@Int.cast_smul_eq_zsmul (R.obj.obj U) (M.val.obj U) _ _
              (M.val.obj U).isModule z x)
          _ = z • f.hom.app U x := (f.hom.app U).hom.map_zsmul z x
          _ = _ := (@Int.cast_smul_eq_zsmul (R.obj.obj U) (P.val.obj U) _ _
            (P.val.obj U).isModule z (f.hom.app U x)).symm)
    exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective a P.isSheaf).symm g⟩
  exact
    { hom := lift M P e.hom
      inv := lift P M e.inv
      hom_inv_id := by
        apply (SheafOfModules.toSheaf R).map_injective
        exact e.hom_inv_id
      inv_hom_id := by
        apply (SheafOfModules.toSheaf R).map_injective
        exact e.inv_hom_id }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def rootRestrictionIso (S : Scheme.{u}) (U : S.ProEt) (N : ℕ) :
    (ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom U.prop).obj
        (proEtaleRootsOfUnitySheaf S N) ≅ proEtaleRootsOfUnitySheaf U.left N := by
  let G := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  exact (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (Functor.isoWhiskerLeft G.op (rootRawPresheafIso S N) ≪≫
      (rootRawPresheafIso U.left N).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def unitAbIso (S : Scheme.{u}) (l : ℕ) [Fact l.Prime] (n : ℕ) :
    (SheafOfModules.toSheaf (purTwistRing S (purTwistFiniteRing S l n))).obj
      (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))) ≅
    (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))) := by
  have : (ProEt.topology S).PreservesSheafification
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
    constructor
    intro P Q f hf
    apply ((ProEt.topology S).W_iff_isLocallyBijective _).mpr
    have hi := hf.isLocallyInjective
    have hs := hf.isLocallySurjective
    constructor
    · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology S) f x y h⟩
    · exact ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology S) f x⟩
  exact (sheafCompose (ProEt.topology S)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).mapIso
        (purTwistFiniteRingIso S l n) ≪≫
    (constantCommuteCompose (ProEt.topology S)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteIsoOfAbIso (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (U : S.ProEt)
    (e : (proEtaleRootsOfUnitySheaf S (l ^ (n + 1))).over U ≅
      ((sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (purTwistFiniteRing S l n)).over U) :
    (purTwistRootsModule S l n).over U ≅
      (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over U := by
  let a := Functor.whiskerLeft (Over.forget U).op
    (Functor.whiskerRight (toSheafify (ProEt.topology S)
      ((Functor.const S.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  have : Presheaf.IsLocallySurjective (ProEt.topology S)
      (Functor.whiskerRight (toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective (ProEt.topology S)
      (Functor.whiskerRight (toSheafify (ProEt.topology S)
        ((Functor.const S.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))))
        (CategoryTheory.forget CommRingCat.{u + 1}))
    infer_instance
  have : Presheaf.IsLocallySurjective ((ProEt.topology S).over U) a :=
    Presheaf.isLocallySurjective_whisker ((ProEt.topology S).over U)
      (ProEt.topology S) (Over.forget U) _
  exact moduleIsoOfAddIso ((ProEt.topology S).over U) (l ^ (n + 1))
    ((purTwistRing S (purTwistFiniteRing S l n)).over U) a
    ((purTwistRootsModule S l n).over U)
    ((SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over U)
    e

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteRootBasis (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (U : S.ProEt) (z : Γ(U.left, ⊤)ˣ) (hz : z ^ (l ^ (n + 1)) = 1)
    (hd : ∀ i < l ^ (n + 1), ∀ j < l ^ (n + 1), i ≠ j →
      IsUnit ((z : Γ(U.left, ⊤)) ^ i - (z : Γ(U.left, ⊤)) ^ j)) :
    (purTwistRootsModule S l n).over U ≅
      (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over U := by
  let G := MorphismProperty.Over.map (f := U.hom) ⊤ U.prop
  have : G.IsContinuous (ProEt.topology U.left) (ProEt.topology S) :=
    ProEt.isContinuous_overMap U.prop
  have : G.IsCocontinuous (ProEt.topology U.left) (ProEt.topology S) :=
    ProEt.isCocontinuous_overMap U.prop
  let H := (ProEt.sliceEquiv S U).inverse
  letI := ProEt.sliceDense S U
  let E := H.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (ProEt.topology U.left) ((ProEt.topology S).over U)
  let F := ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom U.prop
  let : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let e : E.obj (((proEtaleRootsOfUnitySheaf S (l ^ (n + 1))).over U)) ≅
      E.obj (((SheafOfModules.toSheaf _).obj
        (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n)))).over U) :=
    rootRestrictionIso S U _ ≪≫ rawRootIso U.left _ ≪≫
      (ProEtale.constantRootsIso _ z hz hd).symm ≪≫
      ((G.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
        (ProEt.topology U.left) (ProEt.topology S)).app
        ((Functor.const S.ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))) ≪≫
      F.mapIso (unitAbIso S l n).symm
  exact finiteIsoOfAbIso S l n U (E.preimageIso e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem globalPrimeUnit (S : Scheme.{u}) (l : ℕ)
    [∀ x : S, Invertible (l : S.residueField x)] : IsUnit (l : Γ(S, ⊤)) := by
  apply S.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  rw [map_natCast]
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (S.residue x).hom (l : S.presheaf.stalk x) ≠ 0
  simpa only [map_natCast] using (isUnit_of_invertible (l : S.residueField x)).ne_zero

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteRootCover (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)] (n : ℕ) :
    ∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      (∀ i, Etale (U i).hom) ∧
      ∀ i, Nonempty ((purTwistRootsModule S l n).over (U i) ≅
        (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over (U i)) := by
  classical
  let N := l ^ (n + 1)
  have hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  have hunit : IsUnit (N : Γ(S, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (globalPrimeUnit S l).pow (n + 1)
  have : Etale (primitiveRootsCover Γ(S, ⊤) N) :=
    etale_primitiveRootsCover _ N (Nat.ne_of_gt hN) hunit
  let V := pullback S.toSpecΓ (primitiveRootsCover Γ(S, ⊤) N)
  let q : V ⟶ S := pullback.fst _ _
  have hq : Function.Surjective q.base := by
    intro t
    obtain ⟨v, hv⟩ := surjective_primitiveRootsCover Γ(S, ⊤) N hunit (S.toSpecΓ t)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback t v hv.symm
    exact ⟨z, hz⟩
  let φ : CommRingCat.of (PrimitiveRootsAlgebra Γ(S, ⊤) N) ⟶ Γ(V, ⊤) :=
    (ΓSpecIso (.of (PrimitiveRootsAlgebra Γ(S, ⊤) N))).inv ≫
      (pullback.snd S.toSpecΓ (primitiveRootsCover Γ(S, ⊤) N)).appTop
  let z : Γ(V, ⊤)ˣ := ((PrimitiveRootsAlgebra.isUnit_zeta Γ(S, ⊤) N hN).map φ.hom).unit
  have hz : z ^ N = 1 := by
    ext
    simp only [z, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one, ← map_pow,
      PrimitiveRootsAlgebra.zeta_pow, map_one]
  have hd : ∀ i < N, ∀ j < N, i ≠ j →
      IsUnit ((z : Γ(V, ⊤)) ^ i - (z : Γ(V, ⊤)) ^ j) := by
    intro i hi j hj hij
    simpa only [z, IsUnit.unit_spec, ← map_pow, ← map_sub] using
      (PrimitiveRootsAlgebra.isUnit_zeta_pow_sub_zeta_pow Γ(S, ⊤) N hi hj hij).map φ.hom
  let U : PUnit.{u + 2} → S.ProEt := fun _ ↦ ProEt.mk q
  let f : ∀ i, U i ⟶ ProEt.mk (𝟙 S) := fun _ ↦ MorphismProperty.Over.homMk q
  refine ⟨PUnit, U, f, ?_, ?_, fun _ ↦ ⟨finiteRootBasis S l n _ z hz hd⟩⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    change Presieve.ofArrows (fun _ : PUnit.{u + 2} ↦ V) (fun _ ↦ q) ∈
      proetalePrecoverage S
    apply etalePrecoverage_le_proetalePrecoverage
    change Presieve.ofArrows (fun _ : PUnit.{u + 2} ↦ V) (fun _ ↦ q) ∈
      Scheme.precoverage @Etale S
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun t ↦ ⟨PUnit.unit, hq t⟩, fun _ ↦ inferInstance⟩
  · intro i
    change Etale q
    infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def stalkFiberIso {S : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (F : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) :
    proEtaleGeometricStalk s F ≅ (ProEtale.geometricPoint s).sheafFiber.obj F :=
  Functor.Final.colimitIso (ProEtale.geometricElementsEquiv s).functor.op
    ((Functor.Elements.π (ProEtale.geometricPoint s).fiber).op ⋙ F.obj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def fiberOverIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    (Φ : J.Point.{u + 1}) {U : C} (x : Φ.fiber.obj U)
    (F : Sheaf J AddCommGrpCat.{u + 1}) :
    (Φ.over x).sheafFiber.obj (F.over U) ≅ Φ.sheafFiber.obj F :=
  Functor.Final.colimitIso
    ((FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).functor ⋙
      Over.forget (Φ.fiber.elementsMk U x)).op
    ((Functor.Elements.π Φ.fiber).op ⋙ F.obj)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteRootStalk (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)] (n : ℕ)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    Finite ((proEtaleGeometricStalk (C := AddCommGrpCat.{u + 1}) s
      (proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) : Type (u + 1)) := by
  classical
  let : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨I, U, f, hc, he, hb⟩ := finiteRootCover S l n
  let Φ := ProEtale.geometricPoint s
  obtain ⟨V, g, hg, v, hv⟩ := Φ.jointly_surjective
    (Sieve.generate (Presieve.ofArrows U f))
    (Precoverage.generate_mem_toGrothendieck hc)
    (ULift.up (Over.homMk s (Category.comp_id s)))
  obtain ⟨_, a, b, ⟨i⟩, hab⟩ := hg
  let w := Φ.fiber.map a v
  let F := proEtaleRootsOfUnitySheaf S (l ^ (n + 1))
  let B := AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))
  let T := (Over.forget (U i)).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    ((ProEt.topology S).over (U i)) (ProEt.topology S)
  let c : (constantSheaf ((ProEt.topology S).over (U i)) AddCommGrpCat.{u + 1}).obj B ≅
      T.obj ((constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj B) :=
    ((Over.forget (U i)).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u + 1} ((ProEt.topology S).over (U i)) (ProEt.topology S)).app
        ((Functor.const S.ProEtᵒᵖ).obj B)
  let e : F.over (U i) ≅
      (constantSheaf ((ProEt.topology S).over (U i)) AddCommGrpCat.{u + 1}).obj B :=
    (SheafOfModules.toSheaf _).mapIso (hb i).some ≪≫
      T.mapIso (unitAbIso S l n) ≪≫ c.symm
  let E := stalkFiberIso s F ≪≫ (fiberOverIso Φ w F).symm ≪≫
    (Φ.over w).sheafFiber.mapIso e ≪≫ (Φ.over w).sheafFiberConstantSheafIso B
  exact Finite.of_equiv B E.addCommGroupIsoToAddEquiv.toEquiv.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def successorIndex : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ ⥤ ℕ from
    { obj := fun n ↦ n + 1
      map := fun f ↦ homOfLE (Nat.add_le_add_right (leOfHom f) 1) }).op

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem successorIndex_step (n : ℕ) :
    successorIndex.map (homOfLE (Nat.le_succ n)).op =
      (homOfLE (Nat.le_succ (n + 1))).op := Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def actualRawRootTowerIso (S : Scheme.{u}) (l : ℕ)
    [Fact l.Prime] :
    proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ≅
      successorIndex ⋙ ProEtale.rawRootsSystem S l := by
  let t : proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1} ⟶
      successorIndex ⋙ ProEtale.rawRootsSystem S l :=
    NatTrans.ofOpSequence (fun n ↦ (rootRawPresheafIso S (l ^ (n + 1))).hom) (by
      intro n
      simp only [Functor.comp_map, successorIndex_step, proEtaleRootsOfUnityTower,
        ProEtale.rawRootsSystem, Functor.ofOpSequence_map_homOfLE_succ]
      ext U x
      apply ULift.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      change _ = ((ProEtale.rawRootsTransition S l (n + 1)).app U
        ((rootRawPresheafIso S (l ^ (n + 2))).hom.app U x)).down.toMul.val.val
      rw [ProEtale.rawRootsTransition_val]
      have hx := (existsUnique_proEtaleRootsOfUnitySections S (l ^ (n + 2)) U).exists.choose_spec x
      have hy := (existsUnique_proEtaleRootsOfUnitySections S (l ^ (n + 1)) U).exists.choose_spec
          ((proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
            (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
            (pow_dvd_pow l (Nat.le_succ (n + 1)))).hom.app U x)
      have h := proEtaleRootsOfUnityTransition_prime S l (Fact.out : l.Prime) n U x
      rw [← hx, ← hy] at h
      exact congrArg (fun y ↦ y.down.toMul.val) h)
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs
    (IsIso (rootRawPresheafIso S _).hom)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def actualRootTowerIso (S : Scheme.{u}) (l : ℕ)
    [Fact l.Prime] :
    proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ≅
      successorIndex ⋙ ProEtale.tateRootsSystem S l := by
  exact (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _
      (sheafificationNatIso (ProEt.topology S) AddCommGrpCat.{u + 1}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (actualRawRootTowerIso S l) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft successorIndex (ProEtale.rootsSheafificationIso S l)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem forgetCommAbPreserves (S : Scheme.{u}) :
    (ProEt.topology S).PreservesSheafification
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
  constructor
  intro P Q f hf
  apply ((ProEt.topology S).W_iff_isLocallyBijective _).mpr
  have hi := hf.isLocallyInjective
  have hs := hf.isLocallySurjective
  constructor
  · exact ⟨fun x y h ↦ Presheaf.equalizerSieve_mem (ProEt.topology S) f x y h⟩
  · exact ⟨fun x ↦ Presheaf.imageSieve_mem (ProEt.topology S) f x⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def coefficientTowerIso (S : Scheme.{u}) (l : ℕ)
    [Fact l.Prime] :
    purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) ≅
      successorIndex ⋙ ProEtale.constantTateResidueSystem S l := by
  letI := forgetCommAbPreserves S
  let c := constantCommuteCompose (ProEt.topology S)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let t : purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) ⟶
      successorIndex ⋙ ProEtale.constantTateResidueSystem S l :=
    NatTrans.ofOpSequence
      (fun n ↦ (c.app (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))).hom)
      (by
        intro n
        let f := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          ((ZMod.castHom (pow_dvd_pow l (Nat.le_succ (n + 1)))
            (ZMod (l ^ (n + 1)))).comp ULift.ringEquiv.toRingHom))
        simp only [Functor.comp_map, successorIndex_step, purTwistZlTower,
          ProEtale.constantTateResidueSystem, Functor.ofOpSequence_map_homOfLE_succ]
        exact c.hom.naturality f)
  have : ∀ n, IsIso (t.app n) := fun _ ↦ inferInstanceAs (IsIso (c.app _).hom)
  have : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def localTowerIso (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : S.ProEt)
    (e : ProEtale.tateRootsSystem S l ⋙ ProEtale.upperStar AddCommGrpCat.{u + 1} U.hom ≅
      ProEtale.constantTateResidueSystem S l ⋙
        ProEtale.upperStar AddCommGrpCat.{u + 1} U.hom) :
    proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U ≅
      (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
          (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U := by
  let H := (ProEt.sliceEquiv S U).inverse
  letI := ProEt.sliceDense S U
  let E := H.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (ProEt.topology U.left) ((ProEt.topology S).over U)
  let F := ProEtale.localizationRestriction AddCommGrpCat.{u + 1} U.hom U.prop
  let h := ProEtale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.hom U.prop
  let q : proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙ F ≅
      (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙ F :=
    Functor.isoWhiskerRight (actualRootTowerIso S l) F ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft successorIndex
        (Functor.isoWhiskerLeft (ProEtale.tateRootsSystem S l) h.symm ≪≫ e ≪≫
          Functor.isoWhiskerLeft (ProEtale.constantTateResidueSystem S l) h) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (coefficientTowerIso S l).symm F
  exact ((Functor.FullyFaithful.ofFullyFaithful E).whiskeringRight ℕᵒᵖ).preimageIso q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientAbPreservesLimits (S : Scheme.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ (sheafCompose (ProEt.topology S)
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) := by
  let A := sheafCompose (ProEt.topology S)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  have : PreservesLimitsOfShape ℕᵒᵖ
      (A ⋙ sheafToPresheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfShape_of_natIso
      (Iso.refl (sheafToPresheaf (ProEt.topology S) CommRingCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj
          ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
        forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def limitBasisAb (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : S.ProEt)
    (q : proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U ≅
      (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
          (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U) :
    (purTwistZlOne S l).over U ≅
      ((sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (purTwistZlCompletion S l)).over U := by
  have := coefficientAbPreservesLimits S
  let A := sheafCompose (ProEt.topology S)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let F := (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U
  exact preservesLimitIso F (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) ≪≫
    HasLimit.isoOfNatIso q ≪≫
    (preservesLimitIso (A ⋙ F) (purTwistZlTower S l)).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem limitBasisAb_projection (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : S.ProEt)
    (q : proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U ≅
      (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
          (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U)
    (n : ℕ) (W : (Over U)ᵒᵖ) (x : (purTwistZlOne S l).obj.obj (op W.unop.left)) :
    (purTwistZlProjection S l n).hom.app (op W.unop.left)
        ((limitBasisAb S l U q).hom.hom.app W x) =
      (q.hom.app (op n)).hom.app W
        ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
          (op W.unop.left) x) := by
  have := coefficientAbPreservesLimits S
  have h : (limitBasisAb S l U q).hom ≫
      ((sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U).map
          (purTwistZlProjection S l n) =
      ((ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U).map
        (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)) ≫
          q.hom.app (op n) := by
    change _ ≫ _ ≫ (preservesLimitIso
      (sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U)
      (purTwistZlTower S l)).inv ≫
      (sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U).map
        (limit.π (purTwistZlTower S l) (op n)) = _
    rw [preservesLimitIso_inv_π]
    erw [HasLimit.isoOfNatIso_hom_π q (op n)]
    rw [preservesLimitIso_hom_π_assoc]
  exact congrArg (fun f ↦ f.hom.app W x) h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def completedBasis (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : S.ProEt)
    (q : proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U ≅
      (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
          (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U) :
    (purTwistZlModule S l).over U ≅
      (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over U := by
  let a := limitBasisAb S l U q
  let f : (purTwistZlModule S l).over U ⟶
      (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over U :=
    ⟨PresheafOfModules.homMk a.hom.hom (by
      intro W r x
      let ev : Sheaf (ProEt.topology S) CommRingCat.{u + 1} ⥤ CommRingCat.{u + 1} :=
        sheafToPresheaf (ProEt.topology S) CommRingCat.{u + 1} ⋙
          (CategoryTheory.evaluation S.ProEtᵒᵖ CommRingCat.{u + 1}).obj (op W.unop.left)
      apply Concrete.isLimit_ext (purTwistZlTower S l ⋙ ev)
        (isLimitOfPreserves ev (limit.isLimit (purTwistZlTower S l)))
      intro n
      change (purTwistZlProjection S l n.unop).hom.app (op W.unop.left)
          (a.hom.hom.app W (r • x)) =
        (purTwistZlProjection S l n.unop).hom.app (op W.unop.left)
          (@Mul.mul ((purTwistZlCompletion S l).obj.obj (op W.unop.left))
            inferInstance r (a.hom.hom.app W x))
      rw [limitBasisAb_projection]
      have hm := ((purTwistZlProjection S l n.unop).hom.app
        (op W.unop.left)).hom.map_mul r (a.hom.hom.app W x)
      erw [hm]
      rw [limitBasisAb_projection]
      have hp := (purTwistZlAction_existsUnique S l).exists.choose_spec.2
        n.unop (op W.unop.left) r x
      erw [hp]
      exact ((finiteIsoOfAbIso S l n.unop U (q.app n)).hom.val.app W).hom.map_smul
        ((purTwistZlProjection S l n.unop).hom.app (op W.unop.left) r)
        ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) n).hom.app
          (op W.unop.left) x))⟩
  have : IsIso ((SheafOfModules.toSheaf _).map f) := inferInstanceAs (IsIso a.hom)
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf _)
  exact asIso f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedBasis_projection (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : S.ProEt)
    (q : proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U ≅
      (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
          (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U)
    (n : ℕ) (W : (Over U)ᵒᵖ) (x : (purTwistZlModule S l).val.obj (op W.unop.left)) :
    (purTwistZlProjection S l n).hom.app (op W.unop.left)
        ((completedBasis S l U q).hom.val.app W x) =
      (finiteIsoOfAbIso S l n U (q.app (op n))).hom.val.app W
        ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
          (op W.unop.left) x) :=
  limitBasisAb_projection S l U q n W x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def rootProjectionModule (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (n : ℕ) :
    purTwistZlModule S l ⟶
      (SheafOfModules.restrictScalars
        ((sheafCompose (ProEt.topology S)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (purTwistZlProjection S l n))).obj (purTwistRootsModule S l n) :=
  ⟨PresheafOfModules.homMk
    (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom
    (fun U a x ↦ (purTwistZlAction_existsUnique S l).exists.choose_spec.2 n U a x)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localTowerCover (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)] :
    ∃ (I : Type (u + 1)) (U : I → S.ProEt)
      (f : ∀ i, U i ⟶ ProEt.mk (𝟙 S)),
      Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
      ∀ i, Nonempty
        (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
            (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} (U i) ≅
          (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
            ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
              (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} (U i)) := by
  classical
  obtain ⟨B, hb⟩ := ProEtale.exists_compatible_roots_diagram_basis S l (globalPrimeUnit S l)
  let (i : B.I₀) : WeaklyEtale (B.f i) := B.forgetQc.map_prop i
  let I := ULift.{u + 1} B.I₀
  let U : I → S.ProEt := fun i ↦ ProEt.mk (B.f i.down)
  let f : ∀ i, U i ⟶ ProEt.mk (𝟙 S) := fun i ↦ MorphismProperty.Over.homMk (B.f i.down)
  refine ⟨I, U, f, ?_, fun i ↦ ⟨localTowerIso S l (U i) (hb i.down).some⟩⟩
  rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
  change Presieve.ofArrows (fun i : I ↦ B.X i.down) (fun i ↦ B.f i.down) ∈ _
  exact (Presieve.ofArrows_comp_eq_of_surjective (B.f)
    (a := ULift.down) ULift.down_surjective).symm ▸ B.mem₀

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def rootReductionMap (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (n : ℕ) :
    SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistZlProjection S l n) (purTwistZlModule S l) ⟶ purTwistRootsModule S l n :=
  SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1} (purTwistZlProjection S l n)
    (purTwistZlModule S l) (purTwistRootsModule S l n) (rootProjectionModule S l n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rootReductionMap_local (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (U : S.ProEt)
    (q : proEtaleRootsOfUnityTower S l (Fact.out : l.Prime) ⋙
        (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U ≅
      (purTwistZlTower S l ⋙ sheafCompose (ProEt.topology S)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
          (ProEt.topology S).overPullback AddCommGrpCat.{u + 1} U)
    (n : ℕ) : IsIso ((rootReductionMap S l n).over U) := by
  let e := completedBasis S l U q
  let b := finiteIsoOfAbIso S l n U (q.app (op n))
  let d := SheafOfModules.extendedBasisIso (purTwistZlProjection S l n)
    (purTwistZlModule S l) e
  have h : (rootReductionMap S l n).over U = d.hom ≫ b.inv := by
    apply SheafOfModules.extension_over_hom_ext (purTwistZlProjection S l n)
      (purTwistZlModule S l) U
    intro W r x
    change (SheafOfModules.scalarExtensionLift.{u + 1, u, u + 1, u + 1}
      (purTwistZlProjection S l n) (purTwistZlModule S l) (purTwistRootsModule S l n)
      (rootProjectionModule S l n)).val.app (op W.unop.left)
        (SheafOfModules.scalarExtensionSection (purTwistZlProjection S l n)
          (purTwistZlModule S l) (op W.unop.left) r x) = _
    erw [SheafOfModules.scalarExtensionLift_tmul.{u + 1, u, u + 1, u + 1}
      (purTwistZlProjection S l n) (purTwistZlModule S l) (purTwistRootsModule S l n)
      (rootProjectionModule S l n) (op W.unop.left) r x]
    change r • (show (purTwistRootsModule S l n).val.obj (op W.unop.left) from
      (limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
        (op W.unop.left) x) =
      b.inv.val.app W
        ((SheafOfModules.extendedCoordinateMap (purTwistZlProjection S l n)
          (purTwistZlModule S l) e).val.app W
            (SheafOfModules.scalarExtensionSection (purTwistZlProjection S l n)
              (purTwistZlModule S l) (op W.unop.left) r x))
    erw [SheafOfModules.extendedCoordinateMap_tmul.{u + 1, u, u + 1}
      (purTwistZlProjection S l n) (purTwistZlModule S l) e W r x]
    change _ = b.inv.val.app W
      ((purTwistZlProjection S l n).hom.app (op W.unop.left) (e.hom.val.app W x) * r)
    rw [completedBasis_projection, mul_comm]
    change _ = b.inv.val.app W (r • b.hom.val.app W _)
    rw [map_smul]
    congr 1
    exact (congrArg (fun f ↦ f.val.app W
      ((limit.π (proEtaleRootsOfUnityTower S l (Fact.out : l.Prime)) (op n)).hom.app
        (op W.unop.left) x)) b.hom_inv_id).symm
  rw [h]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite roots have étale local bases, and compatible lifts on weakly contractible
covers trivialize the entire inverse limit and identify its finite quotients. -/
theorem purTwistRootLocalModels (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ,
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        (∀ i : I, Etale (U i).hom) ∧
        ∀ i : I, Nonempty ((purTwistRootsModule S l n).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over (U i))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite ((proEtaleGeometricStalk (C := AddCommGrpCat.{u + 1}) s
          (proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) : Type (u + 1)))) ∧
    ((∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i : I, Nonempty ((purTwistZlModule S l).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over (U i))) ∧
      ∀ n : ℕ, Nonempty
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistZlProjection S l n)
          (purTwistZlModule S l) ≅ purTwistRootsModule S l n)) := by
  classical
  obtain ⟨I, U, f, hc, hq⟩ := localTowerCover S l
  have hU : (ProEt.topology S).CoversTop U := by
    let hT : IsTerminal (ProEt.mk (𝟙 S)) := MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  refine ⟨fun n ↦ ⟨finiteRootCover S l n, finiteRootStalk S l n⟩,
    ⟨I, U, f, hc, fun i ↦ ⟨completedBasis S l (U i) (hq i).some⟩⟩, ?_⟩
  intro n
  have : IsIso ((SheafOfModules.toSheaf _).map (rootReductionMap S l n)) := by
    apply Sheaf.isIso_of_coversTop hU
    intro i
    have := rootReductionMap_local S l (U i) (hq i).some n
    exact Functor.map_isIso (SheafOfModules.toSheaf _)
      ((rootReductionMap S l n).over (U i))
  have : IsIso (rootReductionMap S l n) :=
    isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
  exact ⟨asIso (rootReductionMap S l n)⟩

end AlgebraicGeometry.Scheme
