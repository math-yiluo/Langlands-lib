import Langlands.AlgebraicGeometry.SmoothLifting.ChartDerivation
import Mathlib.RingTheory.LocalProperties.Exactness

/-! # Flat base change of modules of lifts

For a smooth morphism `f`, square-zero data over `C` and a flat `C`-algebra `B`, restriction of
lifts from `C` to `B` is a base change: `B ⊗[C] (lifts on C) ≃ (lifts on B)`. The proof localizes
at the elements of a chart cover, where it is `Chart.isBaseChange_resLin`, and glues with
`bijective_of_isLocalized_span`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits TensorProduct

namespace Langlands.AlgebraicGeometry.SmoothLifting

/-- **Base change is local**: a linear map whose localizations at a spanning set of elements are
base changes is a base change. -/
theorem isBaseChange_of_isLocalized_span {R B M N : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module B N]
    [IsScalarTower R B N] (φ : M →ₗ[R] N) (s : Set R) (hs : Ideal.span s = ⊤)
    (Bc : s → Type*) [∀ r, CommRing (Bc r)] [∀ r, Algebra R (Bc r)] [∀ r, Algebra B (Bc r)]
    [∀ r, IsScalarTower R B (Bc r)]
    [∀ r : s, IsLocalization.Away (algebraMap R B r.1) (Bc r)]
    (Nc : s → Type*) [∀ r, AddCommGroup (Nc r)] [∀ r, Module R (Nc r)] [∀ r, Module B (Nc r)]
    [∀ r, Module (Bc r) (Nc r)] [∀ r, IsScalarTower R (Bc r) (Nc r)]
    [∀ r, IsScalarTower B (Bc r) (Nc r)] [∀ r, IsScalarTower R B (Nc r)]
    (ℓ : ∀ r, N →ₗ[B] Nc r)
    [∀ r : s, IsLocalizedModule (Submonoid.powers (algebraMap R B r.1)) (ℓ r)]
    (h : ∀ r, IsBaseChange (Bc r) ((ℓ r).restrictScalars R ∘ₗ φ)) : IsBaseChange B φ := by
  let Φ := LinearMap.liftBaseChange B φ
  suffices hbij : Function.Bijective Φ by
    refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ hbij) fun x => ?_
    change Φ (1 ⊗ₜ x) = _
    rw [LinearMap.liftBaseChange_tmul, one_smul]
  let f : ∀ r : s, B ⊗[R] M →ₗ[R] Bc r ⊗[R] M := fun r =>
    (AlgebraTensorModule.rTensor R M (Algebra.linearMap B (Bc r))).restrictScalars R
  have hf : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (f r) := fun r =>
    IsLocalizedModule.restrictScalars_powers r.1 _
  have hℓ : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) ((ℓ r).restrictScalars R) :=
    fun r => IsLocalizedModule.restrictScalars_powers r.1 _
  refine bijective_of_isLocalized_span s hs (fun r => Bc r ⊗[R] M) f Nc
    (fun r => (ℓ r).restrictScalars R) (Φ.restrictScalars R) fun r => ?_
  have key : IsLocalizedModule.map (Submonoid.powers r.1) (f r) ((ℓ r).restrictScalars R)
      (Φ.restrictScalars R) =
        (LinearMap.liftBaseChange (Bc r) ((ℓ r).restrictScalars R ∘ₗ φ)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.1) (f r)
      ((ℓ r).restrictScalars R)
    rw [IsLocalizedModule.map_comp]
    refine TensorProduct.ext' fun b m => ?_
    change ℓ r (b • φ m) = algebraMap B (Bc r) b • ℓ r (φ m)
    rw [map_smul, algebraMap_smul]
  rw [key]
  have heq : ⇑((LinearMap.liftBaseChange (Bc r) ((ℓ r).restrictScalars R ∘ₗ φ)).restrictScalars
      R) = ⇑(h r).equiv := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul b m =>
      change LinearMap.liftBaseChange (Bc r) _ (b ⊗ₜ m) = _
      rw [LinearMap.liftBaseChange_tmul, IsBaseChange.equiv_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [heq]
  exact (h r).equiv.bijective

variable {X S : Scheme.{u}} {f : X ⟶ S} {C : CommRingCat.{u}} {I : Ideal C}
  {x₀ : Spec (CommRingCat.of (C ⧸ I)) ⟶ X} {s : Spec C ⟶ S}

/-- Lifts for the base change of data along `C → R'`, on an `R'`-algebra `T`, are lifts of the
original data. -/
theorem isLift_bc_iff (R' T : Type u) [CommRing R'] [Algebra C R'] [CommRing T] [Algebra C T]
    [Algebra R' T] [IsScalarTower C R' T] (y : Spec (CommRingCat.of T) ⟶ X) :
    IsLift f (bcI (I := I) R') (bcx₀ x₀ R') (bcs s R') T y ↔ IsLift f I x₀ s T y := by
  have hJ : redIdeal I T = redIdeal (bcI (I := I) R') T := by
    change I.map (algebraMap C T) = (I.map (algebraMap C R')).map (algebraMap R' T)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let ε : T ⧸ redIdeal I T ≃+* T ⧸ redIdeal (bcI (I := I) R') T := Ideal.quotEquivOfEq hJ
  let εc := (RingEquiv.toCommRingCatIso ε).hom
  have e1 : redMap (bcI (I := I) R') T = redMap I T ≫ εc := by
    ext
    rfl
  have e2 : redStruct I R' ≫ redStruct (bcI (I := I) R') T = redStruct I T ≫ εc := by
    ext x
    change Ideal.Quotient.mk _ (algebraMap R' T (algebraMap C R' x)) =
      Ideal.Quotient.mk _ (algebraMap C T x)
    rw [← IsScalarTower.algebraMap_apply]
  have e3 : strMap (C := C) R' ≫ strMap (C := CommRingCat.of R') T = strMap (C := C) T := by
    ext x
    exact (IsScalarTower.algebraMap_apply C R' T x).symm
  change (Spec.map (redMap (bcI (I := I) R') T) ≫ y =
      Spec.map (redStruct (bcI (I := I) R') T) ≫ (Spec.map (redStruct I R') ≫ x₀) ∧
      y ≫ f = Spec.map (strMap (C := CommRingCat.of R') T) ≫
        (Spec.map (strMap (C := C) R') ≫ s)) ↔
    (Spec.map (redMap I T) ≫ y = Spec.map (redStruct I T) ≫ x₀ ∧
      y ≫ f = Spec.map (strMap (C := C) T) ≫ s)
  refine and_congr ?_ ?_
  · rw [e1, Spec.map_comp, Category.assoc, ← Category.assoc (Spec.map _) (Spec.map _) x₀,
      ← Spec.map_comp, e2, Spec.map_comp, Category.assoc, cancel_epi]
  · rw [← Category.assoc, ← Spec.map_comp, e3]

set_option maxHeartbeats 1600000 in
/-- **Flat base change of lifts.** For a smooth morphism `f` and square-zero data over `C`,
restriction of lifts to a flat `C`-algebra `B` is a base change. -/
theorem LiftModule.isBaseChange_resLin [Smooth f] (hI : SqZero I) (e : GLift f I x₀ s)
    (B : Type u) [CommRing B] [Algebra C B] [Module.Flat C B] :
    IsBaseChange B (LiftModule.resLin B hI e) := by
  classical
  obtain ⟨n, chs, hspan⟩ := exists_charts hI e.2.h₀
  have hIB : SqZero (bcI (I := I) B) := hI.map (algebraMap C B)
  let s' : Set C := Set.range fun i => (chs i).g
  let instC : ∀ r : s', Module C (LiftModule (hIB.map (algebraMap (CommRingCat.of B)
      (Localization.Away (algebraMap C B r.1)))) (GLift.res (Localization.Away
        (algebraMap C B r.1)) (GLift.res B e))) := fun r =>
    Module.compHom _ (algebraMap C (Localization.Away (algebraMap C B r.1)))
  have towC : ∀ r : s', IsScalarTower C (Localization.Away (algebraMap C B r.1))
      (LiftModule (hIB.map (algebraMap (CommRingCat.of B)
        (Localization.Away (algebraMap C B r.1)))) (GLift.res (Localization.Away
          (algebraMap C B r.1)) (GLift.res B e))) := fun r =>
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have towCB : ∀ r : s', IsScalarTower C B
      (LiftModule (hIB.map (algebraMap (CommRingCat.of B)
        (Localization.Away (algebraMap C B r.1)))) (GLift.res (Localization.Away
          (algebraMap C B r.1)) (GLift.res B e))) := fun r =>
    IsScalarTower.of_algebraMap_smul fun c x => by
      change algebraMap B (Localization.Away (algebraMap C B r.1)) (algebraMap C B c) • x =
        algebraMap C (Localization.Away (algebraMap C B r.1)) c • x
      rw [← IsScalarTower.algebraMap_apply]
  let ℓ : ∀ r : s', LiftModule hIB (GLift.res B e) →ₗ[B]
      LiftModule (hIB.map (algebraMap (CommRingCat.of B)
        (Localization.Away (algebraMap C B r.1)))) (GLift.res (Localization.Away
          (algebraMap C B r.1)) (GLift.res B e)) := fun r =>
    { toFun := LiftModule.resLin (Localization.Away (algebraMap C B r.1)) hIB (GLift.res B e)
      map_add' := map_add _
      map_smul' := (LiftModule.resLin (Localization.Away (algebraMap C B r.1)) hIB
        (GLift.res B e)).map_smul }
  have locℓ : ∀ r : s', IsLocalizedModule (Submonoid.powers (algebraMap C B r.1)) (ℓ r) :=
    fun r => LiftModule.isLocalizedModule_resLin hIB (GLift.res B e) (algebraMap C B r.1)
  refine isBaseChange_of_isLocalized_span (R := C) (B := B) (LiftModule.resLin B hI e) s' hspan
    (fun r => Localization.Away (algebraMap C B r.1))
    (fun r => LiftModule (hIB.map (algebraMap (CommRingCat.of B)
      (Localization.Away (algebraMap C B r.1)))) (GLift.res (Localization.Away
        (algebraMap C B r.1)) (GLift.res B e)))
    ℓ fun r => ?_
  obtain ⟨i, hi⟩ := r.2
  let Br := Localization.Away (algebraMap C B r.1)
  let : Algebra (Loc r.1) Br := (Localization.awayMap (algebraMap C B) r.1).toAlgebra
  have : IsScalarTower C (Loc r.1) Br := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap C Br x =
      Localization.awayMap (algebraMap C B) r.1 (algebraMap C (Loc r.1) x)
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
      IsScalarTower.algebraMap_apply C B Br]
  have : Module.Flat (Loc r.1) Br :=
    (Module.flat_iff_of_isLocalization (Loc r.1) (Submonoid.powers r.1) Br).mpr inferInstance
  have hQ : IsBaseChange (Loc r.1) (LiftModule.resLin (Loc r.1) hI e) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r.1) (Loc r.1) _).mp inferInstance
  have hgc : IsUnit (algebraMap (CommRingCat.of (Loc r.1)) (CommRingCat.of (Loc r.1))
      ((chs i).bc (Loc r.1)).g) := by
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    change IsUnit (algebraMap C (Loc r.1) (chs i).g)
    rw [show (chs i).g = r.1 from hi]
    exact isUnit_loc r.1
  have hL := ((chs i).bc (Loc r.1)).isBaseChange_resLin (hI.map (algebraMap C (Loc r.1))) hgc Br
    (GLift.res (Loc r.1) e)
  let instO : Module C (LiftModule ((hI.map (algebraMap C (Loc r.1))).map
      (algebraMap (CommRingCat.of (Loc r.1)) Br)) (GLift.res Br (GLift.res (Loc r.1) e))) :=
    Module.compHom _ (algebraMap C Br)
  have : IsScalarTower C (Loc r.1) (LiftModule ((hI.map (algebraMap C (Loc r.1))).map
      (algebraMap (CommRingCat.of (Loc r.1)) Br)) (GLift.res Br (GLift.res (Loc r.1) e))) :=
    IsScalarTower.of_algebraMap_smul fun c x => by
      change algebraMap (Loc r.1) Br (algebraMap C (Loc r.1) c) • x = algebraMap C Br c • x
      rw [← IsScalarTower.algebraMap_apply]
  have : IsScalarTower C Br (LiftModule ((hI.map (algebraMap C (Loc r.1))).map
      (algebraMap (CommRingCat.of (Loc r.1)) Br)) (GLift.res Br (GLift.res (Loc r.1) e))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hC := hQ.comp (S := Loc r.1) hL
  have hiff : ∀ y, IsGlobalLift f (bcI (I := bcI (I := I) (Loc r.1)) Br)
      (bcx₀ (bcx₀ x₀ (Loc r.1)) Br) (bcs (bcs s (Loc r.1)) Br) y ↔
      IsGlobalLift f (bcI (I := bcI (I := I) B) Br) (bcx₀ (bcx₀ x₀ B) Br) (bcs (bcs s B) Br) y :=
    fun y => (isLift_bc_iff (Loc r.1) Br y).trans (isLift_bc_iff B Br y).symm
  have he : (GLift.res Br (GLift.res (Loc r.1) e)).1 = (GLift.res Br (GLift.res B e)).1 :=
    (restrC_restrC (Loc r.1) e.1).trans (restrC_restrC B e.1).symm
  let E := LiftModule.equivOfIff ((hI.map (algebraMap C (Loc r.1))).map
      (algebraMap (CommRingCat.of (Loc r.1)) Br)) (hIB.map (algebraMap (CommRingCat.of B) Br))
    (GLift.res Br (GLift.res (Loc r.1) e)) (GLift.res Br (GLift.res B e)) hiff he
  refine IsBaseChange.of_equiv (hC.equiv.trans E) fun x => ?_
  have h1 := hC.equiv_tmul 1 x
  rw [one_smul] at h1
  rw [LinearEquiv.trans_apply, h1]
  apply Subtype.ext
  change restrC Br (restrC (Loc r.1) (x : GLift f I x₀ s).1) =
    restrC Br (restrC B (x : GLift f I x₀ s).1)
  exact (restrC_restrC (Loc r.1) _).trans (restrC_restrC B _).symm

end Langlands.AlgebraicGeometry.SmoothLifting
