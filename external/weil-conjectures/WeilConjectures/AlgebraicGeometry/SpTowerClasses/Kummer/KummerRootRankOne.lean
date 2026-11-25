/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistRootLocalModels

/-! # Rank of the integral Kummer root system -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private abbrev systemRing (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  SemilinearSections.ring (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (SemilinearSections.systemRing (Scheme.ProEt.topology T)
      (fun n ↦ (Rrings l T).obj (op n))
      (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op))

private def integerMap {C : Type (u + 1)} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u + 1}) :
    (Functor.const Cᵒᵖ).obj (RingCat.of (ULift.{u + 1} ℤ)) ⟶ R where
  app U := RingCat.ofHom ((Int.castRingHom (R.obj U)).comp ULift.ringEquiv.toRingHom)
  naturality U V f := by
    ext z
    exact (map_intCast (R.map f).hom z.down).symm

private theorem integerMap_surjective (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    Presheaf.IsLocallySurjective (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (integerMap (systemRing l T).obj) := by
  constructor
  intro U x
  let n := U.1
  let a := toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1))))))
  change (Presheaf.imageSieve (integerMap (systemRing l T).obj) x).functorPullback
    (Prod.sectR U.1 T.ProEt) ∈ (Scheme.ProEt.topology T) U.2
  apply (Scheme.ProEt.topology T).superset_covering ?_
    (Presheaf.imageSieve_mem (Scheme.ProEt.topology T) a x)
  intro V f hf
  obtain ⟨b, hb⟩ := hf
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective b.down
  refine ⟨ULift.up z, ?_⟩
  have hcast : a.app (op V) b = (z : (Rlevel l T n).obj.obj (op V)) := by
    have he : b = (z : ULift.{u + 1} (ZMod (l ^ (n + 1)))) := by
      apply ULift.ext
      exact hz.symm
    rw [he]
    exact map_intCast (a.app (op V)).hom z
  change (z : (Rlevel l T n).obj.obj (op V)) = _
  rw [← hcast, hb]
  let B := SemilinearSections.rings (Scheme.ProEt.topology T)
    (fun m ↦ (Rrings l T).obj (op m))
    (fun m ↦ (Rrings l T).map (homOfLE (Nat.le_succ m)).op)
  exact (congrArg
    (fun g : Rlevel l T n ⟶ Rlevel l T n ↦
      (g.hom.app (op U.2) ≫ (Rlevel l T n).obj.map f.op) x)
    (B.map_id (op n))).symm

private def linearIso {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u + 1})
    [Presheaf.IsLocallySurjective J (integerMap R.obj)]
    (M N : SheafOfModules.{u + 1} R)
    (e : (SheafOfModules.toSheaf R).obj M ≅ (SheafOfModules.toSheaf R).obj N) : M ≅ N := by
  let lift (M N : SheafOfModules.{u + 1} R)
      (f : (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj N) :
      M ⟶ N := by
    let g : (PresheafOfModules.restrictScalars (integerMap R.obj)).obj M.val ⟶
        (PresheafOfModules.restrictScalars (integerMap R.obj)).obj N.val :=
      PresheafOfModules.homMk f.hom (by
        intro U z x
        change f.hom.app U
            (@SMul.smul _ _ (M.val.obj U).isModule.toSMul (z.down : R.obj.obj U) x) =
          @SMul.smul _ _ (N.val.obj U).isModule.toSMul
            (z.down : R.obj.obj U) (f.hom.app U x)
        calc
          _ = f.hom.app U (z.down • (x : M.val.obj U)) := congrArg (f.hom.app U)
            (@Int.cast_smul_eq_zsmul (R.obj.obj U) (M.val.obj U) _ _
              (M.val.obj U).isModule z.down x)
          _ = z.down • f.hom.app U x := (f.hom.app U).hom.map_zsmul z.down x
          _ = _ := (@Int.cast_smul_eq_zsmul (R.obj.obj U) (N.val.obj U) _ _
            (N.val.obj U).isModule z.down (f.hom.app U x)).symm)
    exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (integerMap R.obj) N.isSheaf).symm g⟩
  exact
    { hom := lift M N e.hom
      inv := lift N M e.inv
      hom_inv_id := by
        apply (SheafOfModules.toSheaf R).map_injective
        exact e.hom_inv_id
      inv_hom_id := by
        apply (SheafOfModules.toSheaf R).map_injective
        exact e.inv_hom_id }

private theorem castSquare {A B A' B' : AddCommGrpCat.{u + 1}}
    (a : A = A') (b : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq f.hom g.hom) : f ≫ eqToHom b = eqToHom a ≫ g := by
  subst A'
  subst B'
  have h' := eq_of_heq h
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using
    (AddCommGrpCat.hom_ext h')

private abbrev flatten (T : Scheme.{u}) (A : Ab T) :=
  (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor ⋙
    Functor.uncurry.obj (A ⋙ sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})

private def forgetPresheafIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (F : Forget T (Rrings l T)) (M : Systems T (Rrings l T)) :
    flatten T (F.F.obj M) ≅ M.val.presheaf := by
  refine NatIso.ofComponents (fun U ↦ eqToIso (F.sections M U.unop.1 (op U.unop.2))) ?_
  intro X Y f
  have hv := castSquare
    (F.sections M Y.unop.1 (op X.unop.2))
    (F.sections M Y.unop.1 (op Y.unop.2))
    (((F.F.obj M).obj (op Y.unop.1)).obj.map f.unop.2.op)
    (M.val.presheaf.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op)
    (F.restrictions M Y.unop.1 f.unop.2.op)
  have ht := F.transitions M (leOfHom f.unop.1) (op X.unop.2)
  have hh : homOfLE (leOfHom f.unop.1) = f.unop.1 := Subsingleton.elim _ _
  rw [hh] at ht
  have hh' := castSquare (F.sections M X.unop.1 (op X.unop.2))
    (F.sections M Y.unop.1 (op X.unop.2)) _
    (M.val.presheaf.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op) ht
  change (((F.F.obj M).map f.unop.1.op).hom.app (op X.unop.2) ≫
    ((F.F.obj M).obj (op Y.unop.1)).obj.map f.unop.2.op) ≫
      eqToHom (F.sections M Y.unop.1 (op Y.unop.2)) =
    eqToHom (F.sections M X.unop.1 (op X.unop.2)) ≫ M.val.presheaf.map f
  rw [Category.assoc, hv, ← Category.assoc, hh', Category.assoc, ← M.val.presheaf.map_comp]
  congr 1

private theorem sequenceCover {T : Scheme.{u}} {I : Type (u + 1)} (U : I → T.ProEt)
    (hU : (Scheme.ProEt.topology T).CoversTop U) :
    (coefficientSequenceTopology (Scheme.ProEt.topology T)).CoversTop
      (fun p : ℕ × I ↦ (p.1, U p.2)) := by
  intro X
  change (Sieve.ofObjects (fun p : ℕ × I ↦ (p.1, U p.2)) X).functorPullback
    (Prod.sectR X.1 T.ProEt) ∈ (Scheme.ProEt.topology T) X.2
  apply (Scheme.ProEt.topology T).superset_covering ?_ (hU X.2)
  rintro V f ⟨i, ⟨g⟩⟩
  exact ⟨(X.1, i), ⟨Prod.mkHom (𝟙 X.1) g⟩⟩

private def sliceIndex (T : Scheme.{u}) (n : ℕ) (U : T.ProEt) :
    Over (n, U) ⥤ ℕ × Over U where
  obj V := (V.left.1, Over.mk V.hom.2)
  map {V W} f := Prod.mkHom f.left.1
    (Over.homMk f.left.2 (congrArg Prod.snd f.w))

private def flattenSlice (T : Scheme.{u}) (A : Ab T) (n : ℕ) (U : T.ProEt) :
    (Over.forget (n, U)).op ⋙ flatten T A ≅
      (sliceIndex T n U).op ⋙ (prodOpEquiv (C := ℕ) (D := Over U)).functor ⋙
        Functor.uncurry.obj
          ((A ⋙ (Scheme.ProEt.topology T).overPullback AddCommGrpCat.{u + 1} U) ⋙
            sheafToPresheaf ((Scheme.ProEt.topology T).over U) AddCommGrpCat.{u + 1}) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ by rfl)

private def ringTowerIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    SemilinearSections.rings (Scheme.ProEt.topology T)
      (fun n ↦ (Rrings l T).obj (op n))
      (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op) ≅ Rrings l T := by
  let f := NatTrans.ofOpSequence (F := SemilinearSections.rings (Scheme.ProEt.topology T)
      (fun n ↦ (Rrings l T).obj (op n))
      (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op))
    (G := Rrings l T) (fun _ ↦ 𝟙 _) (by
      intro n
      simp only [SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ,
        Category.comp_id, Category.id_comp])
  have : ∀ n, IsIso (f.app n) := fun _ ↦ inferInstanceAs (IsIso (𝟙 _))
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact asIso f

private def coefficientPresheafIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (SheafOfModules.unit (systemRing l T)).val.presheaf ≅
      flatten T ((Rrings l T) ⋙ sheafCompose (Scheme.ProEt.topology T)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) :=
  Functor.isoWhiskerLeft (prodOpEquiv (C := ℕ) (D := T.ProEt)).functor
    (Functor.uncurry.mapIso
      (Functor.isoWhiskerRight (ringTowerIso l T)
        (sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1} ⋙
          (Functor.whiskeringRight _ _ _).obj
            ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
              forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))))

private def chartAddIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (F : Forget T (Rrings l T)) (M : Systems T (Rrings l T))
    (e : F.F.obj M ≅ roots l T) (n : ℕ) (U : T.ProEt)
    (q : roots l T ⋙ (Scheme.ProEt.topology T).overPullback AddCommGrpCat.{u + 1} U ≅
      ((Rrings l T) ⋙ sheafCompose (Scheme.ProEt.topology T)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})) ⋙
        (Scheme.ProEt.topology T).overPullback AddCommGrpCat.{u + 1} U) :
    (M.over (n, U)).val.presheaf ≅
      ((SheafOfModules.unit (systemRing l T)).over (n, U)).val.presheaf := by
  let c := (Rrings l T) ⋙ sheafCompose (Scheme.ProEt.topology T)
    ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
      forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})
  let a := Functor.isoWhiskerRight e
    ((Scheme.ProEt.topology T).overPullback AddCommGrpCat.{u + 1} U) ≪≫ q
  exact Functor.isoWhiskerLeft (Over.forget (n, U)).op (forgetPresheafIso l T F M).symm ≪≫
    flattenSlice T (F.F.obj M) n U ≪≫
    Functor.isoWhiskerLeft
      ((sliceIndex T n U).op ⋙ (prodOpEquiv (C := ℕ) (D := Over U)).functor)
      (Functor.uncurry.mapIso (Functor.isoWhiskerRight a
        (sheafToPresheaf ((Scheme.ProEt.topology T).over U) AddCommGrpCat.{u + 1}))) ≪≫
    (flattenSlice T c n U).symm ≪≫
    Functor.isoWhiskerLeft (Over.forget (n, U)).op (coefficientPresheafIso l T).symm

/-- The integral root system is locally free of rank one on the
vertical sequence site.

Source: blueprint latest, `sk-prop-diagonal-tower/_section.md`, Tate-twist paragraph;
`sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: lem-sfb-kummer-root-rank-one).

Proof: choose the common pro-etale primitive-root cover with generators zeta_n
satisfying zeta_(n+1)^l = zeta_n. On each covering chart the maps a to a zeta_n
identify the root modules with the constant quotient rings Z/l^(n+1). The
sections, restrictions and transitions equations of F and e transport these
maps to M. They are linear: the
constant quotient-ring action is locally determined by integer multiplication,
so every additive map between these torsion sheaves is linear. Compatibility
of the generators gives compatibility also along the sequence direction.
Restrict to every slice of the sequence site; these isomorphisms identify the
root system with the coefficient unit locally. Thus M is locally free on one
generator. The covering
criterion for finite local freeness gives rank one. This argument includes
zero section rings and empty charts, and uses the positive level n+1 also at
n=0 and at l=2. -/
theorem kummerRoot_rank_one (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤)))
    (F : Forget T (Rrings l T)) (M : Systems T (Rrings l T))
    (e : F.F.obj M ≅ roots l T) :
    M.IsFiniteLocallyFreeOfRank 1 := by
  classical
  let (x : T) : Invertible (l : T.residueField x) :=
    (show IsUnit (l : T.residueField x) by
      simpa only [map_natCast] using hT.map (T.Γevaluation x).hom).invertible
  obtain ⟨I, U, f, hc, hq⟩ := Scheme.localTowerCover T l
  have hU : (Scheme.ProEt.topology T).CoversTop U := by
    let ht : IsTerminal (Scheme.ProEt.mk (𝟙 T)) :=
      MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ ht]
    rw [← Sieve.ofArrows_eq_ofObjects ht U f]
    exact Precoverage.generate_mem_toGrothendieck hc
  apply (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one M).mp
  apply SheafOfModules.isInvertible_of_forall_over_unit
    (fun p : ℕ × I ↦ (p.1, U p.2)) (sequenceCover U hU)
  rintro ⟨n, i⟩
  let R := systemRing l T
  let X := (n, U i)
  have := integerMap_surjective l T
  have : Presheaf.IsLocallySurjective
      ((coefficientSequenceTopology (Scheme.ProEt.topology T)).over X)
      (integerMap (R.over X).obj) :=
    Presheaf.isLocallySurjective_whisker
      ((coefficientSequenceTopology (Scheme.ProEt.topology T)).over X)
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (Over.forget X) (integerMap R.obj)
  let a : (SheafOfModules.toSheaf (R.over X)).obj (M.over X) ≅
      (SheafOfModules.toSheaf (R.over X)).obj ((SheafOfModules.unit R).over X) :=
    (fullyFaithfulSheafToPresheaf
      ((coefficientSequenceTopology (Scheme.ProEt.topology T)).over X)
      AddCommGrpCat.{u + 1}).preimageIso (chartAddIso l T F M e n (U i) (hq i).some)
  exact ⟨linearIso (R.over X) (M.over X) ((SheafOfModules.unit R).over X) a⟩

end AlgebraicGeometry.ProEtale.SpTowerClasses
