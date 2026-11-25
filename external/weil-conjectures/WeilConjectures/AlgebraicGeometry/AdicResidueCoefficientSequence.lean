/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Torsion.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The consecutive finite coefficient sequence on a slice

Source: Stacks Project, more-algebra.tex, Tag 0G1T, and proetale.tex, Tag 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory.ConstantCompletion
namespace AdicCoefficientProof

universe w
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)

open SheafOfModules

private theorem constant_exact (B : Type w) [CommRing B] :
    (constantCoefficientModule T B).Additive ∧
      PreservesFiniteLimits (constantCoefficientModule T B) ∧
      PreservesFiniteColimits (constantCoefficientModule T B) := by
  let P := strictPerfectConstantPresheaf (C := C) B
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun _ ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun _ ↦ hc)⟩
  have : PreservesFiniteLimits (constantCoefficientModule T B) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (constantCoefficientModule T B) :=
    comp_preservesFiniteColimits _ _
  refine ⟨?_, inferInstance, inferInstance⟩
  apply leftExactFunctor_le_additiveFunctor _ _
  rw [leftExactFunctor_iff]
  infer_instance

@[irreducible] private def constantRestrictionIso {B D : Type w} [CommRing B] [CommRing D]
    (f : B →+* D) (M : ModuleCat.{w} D) :
    (constantCoefficientModule T B).obj ((ModuleCat.restrictScalars f).obj M) ≅
      (res ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom f))).obj
        ((constantCoefficientModule T D).obj M) := by
  let α := constantCoefficientUnit T B
  let β := constantCoefficientUnit T D
  let φ := ((constantSheaf T CommRingCat.{w}) ⋙
    sheafCompose T (forget₂ CommRingCat.{w} RingCat.{w})).map (CommRingCat.ofHom f)
  let P := (strictPerfectConstantPresheaf (C := C) B).obj
    ((ModuleCat.restrictScalars f).obj M)
  let N := (constantCoefficientModule T D).obj M
  let a := (PresheafOfModules.sheafificationAdjunction β).unit.app
    ((strictPerfectConstantPresheaf (C := C) D).obj M)
  let g : P ⟶ (PresheafOfModules.restrictScalars α).obj
      ((SheafOfModules.restrictScalars φ).obj N).val :=
    { app := fun U ↦ ModuleCat.ofHom (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars α).obj
          ((SheafOfModules.restrictScalars φ).obj N).val).obj U)
        { toFun := a.app U
          map_add' := (a.app U).hom.map_add
          map_smul' := fun b m ↦ by
            have hs : β.app U (f b) = φ.hom.app U (α.app U b) :=
              ConcreteCategory.congr_hom
                (NatTrans.congr_app (toSheafify_naturality T
                  ((Functor.const Cᵒᵖ).map (CommRingCat.ofHom f))) U) b
            change a.app U (f b • (show M from m)) =
              φ.hom.app U (α.app U b) • (show N.val.obj U from a.app U m)
            calc
              _ = β.app U (f b) • (show N.val.obj U from a.app U m) :=
                (a.app U).hom.map_smul (f b) (show M from m)
              _ = _ := by rw [hs] }
      naturality := fun {U V} h ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact congrArg (fun k ↦ k m) (a.naturality h) }
  let e : (constantCoefficientModule T B).obj ((ModuleCat.restrictScalars f).obj M) ⟶
      (SheafOfModules.restrictScalars φ).obj N :=
    (PresheafOfModules.sheafificationHomEquiv α).symm g
  have hfac : toSheafify T P.presheaf ≫ ((SheafOfModules.toSheaf _).map e).hom =
      (PresheafOfModules.toPresheaf _).map g := by
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv α (P := P)
        (F := (SheafOfModules.restrictScalars φ).obj N)).apply_symm_apply g)
  have hg : Presheaf.IsLocallyInjective T ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallyInjective T (toSheafify T P.presheaf))
  have hg' : Presheaf.IsLocallySurjective T ((PresheafOfModules.toPresheaf _).map g) :=
    inferInstanceAs (Presheaf.IsLocallySurjective T (toSheafify T P.presheaf))
  have : Presheaf.IsLocallyInjective T ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac T _ hfac
  have : Presheaf.IsLocallySurjective T ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac T hfac
  have : IsIso ((SheafOfModules.toSheaf _).map e) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (SheafOfModules.toSheaf _)
  exact asIso e

@[irreducible] private def constantUnitIso (B : Type w) [CommRing B] :
    (constantCoefficientModule T B).obj (ModuleCat.of B B) ≅
      SheafOfModules.unit (constantCoefficientRing T B) := by
  let α := constantCoefficientUnit T B
  let P := (strictPerfectConstantPresheaf (C := C) B).obj (ModuleCat.of B B)
  let g : P ⟶ (PresheafOfModules.restrictScalars α).obj
      (SheafOfModules.unit (constantCoefficientRing T B)).val :=
    { app := fun U ↦ ModuleCat.ofHom (X := P.obj U)
        (Y := ((PresheafOfModules.restrictScalars α).obj
          (SheafOfModules.unit (constantCoefficientRing T B)).val).obj U)
        { toFun := α.app U
          map_add' := map_add _
          map_smul' := fun b x ↦ (α.app U).hom.map_mul b x }
      naturality := fun {U V} h ↦ by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (α.naturality h) x }
  let e : (constantCoefficientModule T B).obj (ModuleCat.of B B) ⟶
      SheafOfModules.unit (constantCoefficientRing T B) :=
    (PresheafOfModules.sheafificationHomEquiv α).symm g
  have : Presheaf.IsLocallyInjective T ((PresheafOfModules.toPresheaf _).map g) := by
    constructor
    intro U x y h
    exact Presheaf.equalizerSieve_mem T α x y h
  have : Presheaf.IsLocallySurjective T ((PresheafOfModules.toPresheaf _).map g) := by
    constructor
    intro U x
    exact Presheaf.imageSieve_mem T α x
  have hfac : toSheafify T P.presheaf ≫ ((SheafOfModules.toSheaf _).map e).hom =
      (PresheafOfModules.toPresheaf _).map g := by
    exact congrArg ((PresheafOfModules.toPresheaf _).map)
      ((PresheafOfModules.sheafificationHomEquiv α (P := P)
        (F := SheafOfModules.unit (constantCoefficientRing T B))).apply_symm_apply g)
  have : Presheaf.IsLocallyInjective T ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac T _ hfac
  have : Presheaf.IsLocallySurjective T ((SheafOfModules.toSheaf _).map e).hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac T hfac
  have : IsIso ((SheafOfModules.toSheaf _).map e) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨inferInstance, inferInstance⟩
  have : IsIso e := isIso_of_reflects_iso e (SheafOfModules.toSheaf _)
  exact asIso e

end AdicCoefficientProof

namespace AdicCoefficientProof

universe w

private structure DescendedAction {R S M : Type w}
    [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] (f : R →+* S) where
  action : Module S M
  equation : let := action; ∀ (r : R) (m : M), f r • m = r • m

@[irreducible] private def descendedAction {R S M : Type w}
    [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (f : R →+* S) (hf : Function.Surjective f)
    (hM : Module.IsTorsionBySet R M (RingHom.ker f)) : DescendedAction (M := M) f := by
  let := hM.module
  refine ⟨Module.compHom M (f.quotientKerEquivOfSurjective hf).symm.toRingHom, ?_⟩
  dsimp only
  intro r m
  change (f.quotientKerEquivOfSurjective hf).symm (f r) • m = r • m
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

private structure KernelSequence {R S : Type w} [CommRing R] [CommRing S]
    (q : R →+* S) where
  sequence : ShortComplex (ModuleCat.{w} R)
  shortExact : sequence.ShortExact
  first : sequence.X₁ ≅ ModuleCat.of R (RingHom.ker q)
  middle : sequence.X₂ ≅ ModuleCat.of R R
  last : sequence.X₃ ≅ (ModuleCat.restrictScalars q).obj (ModuleCat.of S S)

@[irreducible] private def canonicalKernelSequence {R S : Type w}
    [CommRing R] [CommRing S] (q : R →+* S) (hq : Function.Surjective q) :
    KernelSequence q := by
  let L := RingHom.ker q
  let D := (ModuleCat.restrictScalars q).obj (ModuleCat.of S S)
  let f : ModuleCat.of R L ⟶ ModuleCat.of R R := ModuleCat.ofHom L.subtype
  let g : ModuleCat.of R R ⟶ D := ModuleCat.ofHom
    (X := ModuleCat.of R R) (Y := D)
    { toFun := q
      map_add' := q.map_add
      map_smul' := q.map_mul }
  let E := ShortComplex.mk f g (by ext x; exact x.property)
  refine ⟨E, ?_, Iso.refl _, Iso.refl _, Iso.refl _⟩
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change q x = 0 ↔ ∃ y : L, (y : R) = x
    exact ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.property⟩
  · exact Subtype.val_injective
  · exact hq

private theorem algebra_sequence (A : Type w) [CommRing A] (I : Ideal A) (n : ℕ) :
    let B := A ⧸ I ^ (n + 2)
    let D := A ⧸ I ^ (n + 1)
    let K := A ⧸ I ^ 1
    let q := Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
    let r := Ideal.Quotient.factorPow I (by omega : 1 ≤ n + 2)
    ∃ (N : ModuleCat.{w} K) (S : ShortComplex (ModuleCat.{w} B)),
      S.ShortExact ∧ Nonempty (S.X₁ ≅ (ModuleCat.restrictScalars r).obj N) ∧
        Nonempty (S.X₂ ≅ ModuleCat.of B B) ∧
        Nonempty (S.X₃ ≅ (ModuleCat.restrictScalars q).obj (ModuleCat.of D D)) := by
  dsimp only
  let B := A ⧸ I ^ (n + 2)
  let D := A ⧸ I ^ (n + 1)
  let K := A ⧸ I ^ 1
  let q : B →+* D := Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
  let r : B →+* K := Ideal.Quotient.factorPow I (by omega : 1 ≤ n + 2)
  let L := RingHom.ker q
  have hL : Module.IsTorsionBySet B L (RingHom.ker r) := by
    intro x b
    apply Subtype.ext
    change (b : B) * (x : B) = 0
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (b : B)
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (x : B)
    have ha' : a ∈ I ^ 1 := Ideal.Quotient.eq_zero_iff_mem.mp (by
      change r (Ideal.Quotient.mk (I ^ (n + 2)) a) = 0
      rw [ha]
      exact b.property)
    have hc' : c ∈ I ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp (by
      change q (Ideal.Quotient.mk (I ^ (n + 2)) c) = 0
      rw [hc]
      exact x.property)
    rw [← ha, ← hc, ← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [← pow_add, Nat.add_comm 1 (n + 1)] using Ideal.mul_mem_mul ha' hc'
  have hr : Function.Surjective r := by
    intro k
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective k
    exact ⟨Ideal.Quotient.mk (I ^ (n + 2)) a, rfl⟩
  have hq : Function.Surjective q := by
    intro d
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective d
    exact ⟨Ideal.Quotient.mk (I ^ (n + 2)) a, rfl⟩
  let action := descendedAction r hr hL
  let : Module K L := action.action
  let N := ModuleCat.of K L
  let eL : ModuleCat.of B L ≅ (ModuleCat.restrictScalars r).obj N := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro b
    ext x
    change r b • (show L from x) = b • (show L from x)
    exact action.equation b (show L from x)
  let data := canonicalKernelSequence q hq
  exact ⟨N, data.sequence, data.shortExact, ⟨data.first ≪≫ eL⟩,
    ⟨data.middle⟩, ⟨data.last⟩⟩

end AdicCoefficientProof

namespace AdicCoefficientProof

universe w
variable {C : Type w} [SmallCategory C] (T : GrothendieckTopology C)

private theorem projection_factor (A : Type w) [CommRing A] (I : Ideal A)
    {n m : ℕ} (h : n ≤ m) :
    projection T A I m ≫ (constantSheaf T CommRingCat.{w}).map
      (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.add_le_add_right h 1))) =
        projection T A I n := by
  induction m, h using Nat.le_induction with
  | base =>
    have hid : CommRingCat.ofHom
        (Ideal.Quotient.factorPow I (Nat.add_le_add_right (Nat.le_refl n) 1)) =
        𝟙 (CommRingCat.of (A ⧸ I ^ (n + 1))) := by
      ext x
      rfl
    rw [hid, CategoryTheory.Functor.map_id, Category.comp_id]
  | succ m h ih =>
    have hc : (constantSheaf T CommRingCat.{w}).map
        (CommRingCat.ofHom (Ideal.Quotient.factorPow I
          (Nat.add_le_add_right (Nat.le_succ_of_le h) 1))) =
        transition T A I m ≫ (constantSheaf T CommRingCat.{w}).map
          (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.add_le_add_right h 1))) := by
      rw [transition, ← CategoryTheory.Functor.map_comp]
      congr 1
      ext x
      rfl
    rw [hc, ← Category.assoc]
    have hp : projection T A I (m + 1) ≫ transition T A I m = projection T A I m := by
      dsimp only [projection, completed]
      have hw := limit.w (finiteSystem T A I) (homOfLE (Nat.le_succ m)).op
      have hm : (finiteSystem T A I).map (homOfLE (Nat.le_succ m)).op =
          transition T A I m := Functor.ofOpSequence_map_homOfLE_succ _ _
      rw [hm] at hw
      exact hw
    rw [hp, ih]

private def overConstantRestrictionIso {B D : Type w} [CommRing B] [CommRing D]
    (f : B →+* D) (M : ModuleCat.{w} D) (U : C) :
    (SheafOfModules.overFunctor (SheafOfModules.constantCoefficientRing T B) U).obj
        ((SheafOfModules.constantCoefficientModule T B).obj
          ((ModuleCat.restrictScalars f).obj M)) ≅
      (res ((T.overPullback CommRingCat U).map
        ((constantSheaf T CommRingCat.{w}).map (CommRingCat.ofHom f)))).obj
          ((SheafOfModules.overFunctor (SheafOfModules.constantCoefficientRing T D) U).obj
            ((SheafOfModules.constantCoefficientModule T D).obj M)) :=
  (SheafOfModules.overFunctor (SheafOfModules.constantCoefficientRing T B) U).mapIso
    (constantRestrictionIso T f M)

end AdicCoefficientProof

namespace AlgebraicGeometry.Scheme

/-- The consecutive finite quotients form a short exact sequence whose kernel has
an action of the residue coefficient sheaf, on the actual slice site.

Source: Stacks Project, more-algebra.tex, Tag 0G1T, consecutive-power filtration in
lemma-derived-vanishing-mod-I; proetale.tex, Tag 09C6, finite reduction argument.
(auxiliary; not a blueprint node).

Proof: the algebraic sequence has kernel J^(n+1)/J^(n+2). Multiplication by J
kills this kernel since J * J^(n+1) = J^(n+2), so its action factors through A/J.
Apply constant-module sheafification to the algebraic sequence, which is exact,
and restrict to the slice over U. The coefficient-ring comparison identifies
its middle and last terms with the units of the two constant quotient sheaves.
Restrict their actions along the completed coefficient projections. On the
kernel this action factors through the residue projection: both actions are
induced by multiplication after the map to A/J^(n+2), and reduction modulo J
gives the same action on J^(n+1)/J^(n+2). This constructs N, S and the three
isomorphisms. Exact restriction of scalars preserves the sequence. For J=0 the
kernel is zero; for J=top all three terms are zero. No complex is involved. -/
theorem adicResidue_coefficient_sequence
    (X : AlgebraicGeometry.Scheme.{u}) {A : Type (max v (u + 1))}
    [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    let B := (completed (coefficientProEtaleModelTopology.{u, v} X) A J).over U
    let p := adicResidueLocalProjection.{u, v} X J U
    ∃ (N : Mod ((finite (coefficientProEtaleModelTopology.{u, v} X) A J 0).over U))
      (S : ShortComplex (Mod B)),
      S.ShortExact ∧ Nonempty (S.X₁ ≅ (res (p 0)).obj N) ∧
        Nonempty (S.X₂ ≅ (res (p (n + 1))).obj (SheafOfModules.unit _)) ∧
        Nonempty (S.X₃ ≅ (res (p n)).obj (SheafOfModules.unit _)) := by
  let T := coefficientProEtaleModelTopology.{u, v} X
  let B := A ⧸ J ^ (n + 2)
  let D := A ⧸ J ^ (n + 1)
  let K := A ⧸ J ^ 1
  let q : B →+* D := Ideal.Quotient.factorPow J (Nat.le_succ (n + 1))
  let r : B →+* K := Ideal.Quotient.factorPow J (by omega : 1 ≤ n + 2)
  let V := T.overPullback CommRingCat.{max v (u + 1)} U
  let p := adicResidueLocalProjection.{u, v} X J U
  let cq := (constantSheaf T CommRingCat.{max v (u + 1)}).map (CommRingCat.ofHom q)
  let cr := (constantSheaf T CommRingCat.{max v (u + 1)}).map (CommRingCat.ofHom r)
  have hq : p (n + 1) ≫ V.map cq = p n := by
    change V.map (projection T A J (n + 1)) ≫ V.map cq = V.map (projection T A J n)
    rw [← V.map_comp]
    exact congrArg V.map (AdicCoefficientProof.projection_factor T A J (Nat.le_succ n))
  have hr : p (n + 1) ≫ V.map cr = p 0 := by
    change V.map (projection T A J (n + 1)) ≫ V.map cr = V.map (projection T A J 0)
    rw [← V.map_comp]
    exact congrArg V.map (AdicCoefficientProof.projection_factor T A J (Nat.zero_le _))
  obtain ⟨N, S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := AdicCoefficientProof.algebra_sequence A J n
  let G := SheafOfModules.constantCoefficientModule T B
  let OB := SheafOfModules.overFunctor (SheafOfModules.constantCoefficientRing T B) U
  let OD := SheafOfModules.overFunctor (SheafOfModules.constantCoefficientRing T D) U
  let OK := SheafOfModules.overFunctor (SheafOfModules.constantCoefficientRing T K) U
  let H := res (p (n + 1))
  let F := G ⋙ OB ⋙ H
  have := (AdicCoefficientProof.constant_exact T B).1
  have := (AdicCoefficientProof.constant_exact T B).2.1
  have := (AdicCoefficientProof.constant_exact T B).2.2
  have := (siteRestrictScalars_exact (p (n + 1))).1
  have := (siteRestrictScalars_exact (p (n + 1))).2
  let N' := OK.obj ((SheafOfModules.constantCoefficientModule T K).obj N)
  refine ⟨N', S.map F, hS.map_of_exact F, ?_, ?_, ?_⟩
  · have ec : H.obj ((res (V.map cr)).obj N') ≅ (res (p 0)).obj N' := by
      simpa only [H, CategoryTheory.Functor.comp_obj, hr] using
        (adicFiniteResComp (p (n + 1)) (V.map cr)).app N'
    exact ⟨F.mapIso e₁ ≪≫
      H.mapIso (AdicCoefficientProof.overConstantRestrictionIso T r N U) ≪≫ ec⟩
  · exact ⟨F.mapIso e₂ ≪≫
      H.mapIso (OB.mapIso (AdicCoefficientProof.constantUnitIso T B)) ≪≫
        H.mapIso (ringedOverRingIso (constant T B) U)⟩
  · let MD := OD.obj ((SheafOfModules.constantCoefficientModule T D).obj (ModuleCat.of D D))
    have ec : H.obj ((res (V.map cq)).obj MD) ≅ (res (p n)).obj MD := by
      simpa only [H, CategoryTheory.Functor.comp_obj, hq] using
        (adicFiniteResComp (p (n + 1)) (V.map cq)).app MD
    exact ⟨F.mapIso e₃ ≪≫
      H.mapIso (AdicCoefficientProof.overConstantRestrictionIso T q (ModuleCat.of D D) U) ≪≫
        ec ≪≫ (res (p n)).mapIso (OD.mapIso (AdicCoefficientProof.constantUnitIso T D)) ≪≫
          (res (p n)).mapIso (ringedOverRingIso (constant T D) U)⟩

end AlgebraicGeometry.Scheme
