/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Coefficient.DiagonalTraceCoefficientIdentification
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerForgetEvaluation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # The finite Tate-line identification -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses WeilConjectures

private theorem systemCoefficient_iso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    IsIso (coefficientSystemMap l (ULift.{u} (Padic l)) T) := by
  have : IsIso ((sheafToPresheaf _ _).map
      (coefficientSystemMap l (ULift.{u} (Padic l)) T)) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    rintro ⟨n, U⟩
    have h := (SemilinearSections.systemMap_existsUnique.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T)
      (fun n ↦ (Rrings l T).obj (op n))
      (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op)
      (SpTowerShriek.B l (ULift.{u} (Padic l)) T)
      (SpTowerShriek.tau l (ULift.{u} (Padic l)) T)
      (SpTowerClasses.coefficientMap l (ULift.{u} (Padic l)) T)
      (coefficientMap_transition l (ULift.{u} (Padic l)) T)).exists.choose_spec n (op U)
    change IsIso ((coefficientSystemMap l (ULift.{u} (Padic l)) T).hom.app (op (n, U)))
    rw [show (coefficientSystemMap l (ULift.{u} (Padic l)) T).hom.app (op (n, U)) =
      (SpTowerClasses.coefficientMap l (ULift.{u} (Padic l)) T n).hom.app (op U) from h]
    have := coefficientMap_iso l T n
    infer_instance
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

private def restrictionEquivalence {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u + 1}} (d : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R := by
  have : (CategoryTheory.Equivalence.refl (C := C)).functor.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  have : (CategoryTheory.Equivalence.refl (C := C)).inverse.IsContinuous J J :=
    inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  exact SheafOfModules.pushforwardPushforwardEquivalence
    (CategoryTheory.Equivalence.refl (C := C)) d.hom d.inv
    (by
      change Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ)) S.obj = d.inv.hom ≫ d.hom.hom
      rw [Functor.whiskerRight_id']
      exact (congrArg (fun f ↦ f.hom) d.inv_hom_id).symm)
    (by
      change d.hom.hom ≫ d.inv.hom ≫ Functor.whiskerRight (𝟙 (𝟭 Cᵒᵖ)) R.obj = 𝟙 _
      rw [Functor.whiskerRight_id']
      change d.hom.hom ≫ d.inv.hom ≫ 𝟙 R.obj = 𝟙 _
      rw [Category.comp_id]
      exact congrArg (fun f ↦ f.hom) d.hom_inv_id)

private theorem scalarUnit_iso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (c : Chern l (ULift.{u} (Padic l)) T) :
    IsIso (c.scalar.ordinaryAdjunction.unit.app c.rootModule) := by
  have := systemCoefficient_iso l T
  let d := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (asIso (coefficientSystemMap l (ULift.{u} (Padic l)) T))
  have : (SemilinearSections.res.{u + 1, u, u + 1}
      (coefficientSystemMap l (ULift.{u} (Padic l)) T)).IsEquivalence :=
    (restrictionEquivalence d).isEquivalence_functor
  infer_instance

private def underlyingLevelIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) (n : ℕ) :
    (diagonalForget l T).obj ((r.F.obj M).obj (op n)) ≅
      ((c.reduction.forget.F.obj
        ((SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l (ULift.{u} (Padic l)) T)).obj M)).obj (op n)) := by
  let N := (SemilinearSections.res.{u + 1, u, u + 1}
    (coefficientSystemMap l (ULift.{u} (Padic l)) T)).obj M
  let h := fun U ↦ (r.underlying M n U).trans (c.reduction.forget.sections N n U).symm
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦ eqToIso (h U)) ?_)
  intro U V f
  apply transport_addHom (h U) (h V)
  exact (r.restrictions M n f).trans (c.reduction.forget.restrictions N n f).symm

private def underlyingTowerIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (M : Systems T (Arings l (ULift.{u} (Padic l)) T)) :
    r.F.obj M ⋙ diagonalForget l T ≅ c.reduction.forget.F.obj
      ((SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l (ULift.{u} (Padic l)) T)).obj M) := by
  let η : r.F.obj M ⋙ diagonalForget l T ⟶ c.reduction.forget.F.obj
      ((SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l (ULift.{u} (Padic l)) T)).obj M) :=
    NatTrans.ofOpSequence (fun n ↦ (underlyingLevelIso l T c r M n).hom) (by
      intro n
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext U
      let N := (SemilinearSections.res.{u + 1, u, u + 1}
        (coefficientSystemMap l (ULift.{u} (Padic l)) T)).obj M
      apply transport_addHom
        ((r.underlying M (n + 1) U).trans
          (c.reduction.forget.sections N (n + 1) U).symm)
        ((r.underlying M n U).trans (c.reduction.forget.sections N n U).symm)
      exact (r.transitions M (Nat.le_succ n) U).trans
        (c.reduction.forget.transitions N (Nat.le_succ n) U).symm)
  have : IsIso η := by
    apply (NatTrans.isIso_iff_isIso_app η).2
    intro n
    exact inferInstanceAs (IsIso (underlyingLevelIso l T c r M n.unop).hom)
  exact asIso η

private theorem scalarUnit_section (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (c : Chern l (ULift.{u} (Padic l)) T) (W : (ℕ × T.ProEt)ᵒᵖ)
    (x : c.rootModule.val.obj W) :
    (c.scalar.ordinaryAdjunction.unit.app c.rootModule).val.app W x =
      SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l (ULift.{u} (Padic l)) T) c.scalar c.rootModule W x := by
  have h := c.scalar.unit_section c.rootModule W x
  dsimp only [SemilinearSections.scalarExtensionSection]
  rw [← h]
  change _ = ((eqToHom (c.scalar.model.obj_eq c.rootModule) ≫
    eqToHom (c.scalar.model.obj_eq c.rootModule).symm).val.app W) _
  simp

private theorem transport_apply {A B A' B' : AddCommGrpCat.{u + 1}}
    (eA : A = A') (eB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (hf : HEq f.hom g.hom) (x : A) (y : A') (hx : HEq x y) :
    HEq (f x) (g y) := by
  subst A'
  subst B'
  have hf' := eq_of_heq hf
  have hx' := eq_of_heq hx
  change HEq (f.hom x) (g.hom y)
  rw [hf', hx']

/-- Scalar extension of the root module over the base p-adic coefficient field.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
the finite Tate-line identification, with the ordinary scalar model of Chern data.
(blueprint: lem-sfb-diagonal-trace-line-identification).

Proof: the map Z/l^(n+1) → O_(ULift Q_l)/(l^(n+1)) is the unital ring
isomorphism induced by the lifted identity of valuation rings. These maps commute
with quotient transitions, so they form an isomorphism on the ringed sequence
site. Restriction and extension along this isomorphism are inverse. For the
specified ordinary scalar-extension model, its sheafification-adjunction
normalization identifies the comparison with the tensor unitor: x tensor one
maps to x, including for nonfree root modules. Apply the section, vertical and
horizontal equations of r and of c.reduction.forget to obtain the additive tower
comparison from the scalar-extended root module to c.rootModule. Compose with
c.rootForget. The unitor equation on pure tensors gives the formula below.
This uses only the ordinary scalar model; no completed root-limit projection or
derived trace is used. -/
@[no_expose] def diagonalTraceLineIdentification (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T) :
    r.F.obj (lineModule l (ULift.{u} (Padic l)) c) ⋙ diagonalForget l T ≅ roots l T :=
  haveI := scalarUnit_iso l T c
  underlyingTowerIso l T c r (lineModule l (ULift.{u} (Padic l)) c) ≪≫
    (c.reduction.forget.F.mapIso
      (asIso (c.scalar.ordinaryAdjunction.unit.app c.rootModule))).symm ≪≫ c.rootForget

/-- The line identification sends the scalar extension of a root section `x` to the image
of `x` under `c.rootForget`. -/
theorem diagonalTraceLineIdentification_hom_app_hom_app (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (c : Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : c.rootModule.val.obj (op (n, U.unop)))
    (x' : ((c.reduction.forget.F.obj c.rootModule).obj (op n)).obj.obj U)
    (v : ((r.F.obj (lineModule l (ULift.{u} (Padic l)) c)).obj (op n)).obj.obj U)
    (hx : HEq x x')
    (hv : HEq v (SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
      (coefficientSystemMap l (ULift.{u} (Padic l)) T) c.scalar c.rootModule
      (op (n, U.unop)) x)) :
    ((diagonalTraceLineIdentification l T c r).hom.app (op n)).hom.app U v =
      (c.rootForget.hom.app (op n)).hom.app U x' := by
  let η := c.scalar.ordinaryAdjunction.unit.app c.rootModule
  have : IsIso η := scalarUnit_iso l T c
  let a := c.reduction.forget.F.mapIso (asIso η)
  let b := underlyingTowerIso l T c r (lineModule l (ULift.{u} (Padic l)) c)
  let y := ((c.reduction.forget.F.map η).app (op n)).hom.app U x'
  have hy : HEq y (η.val.app (op (n, U.unop)) x) := by
    apply transport_apply
      (c.reduction.forget.sections c.rootModule n U)
      (c.reduction.forget.sections _ n U)
      (((c.reduction.forget.F.map η).app (op n)).hom.app U)
      ((forget₂ (ModuleCat _) AddCommGrpCat).map (η.val.app (op (n, U.unop))))
      (c.reduction.forget.morphisms η n U) x' x hx.symm
  have hby : (b.hom.app (op n)).hom.app U v = y := by
    exact transport_element
      ((r.underlying (lineModule l (ULift.{u} (Padic l)) c) n U).trans
        (c.reduction.forget.sections
          ((SemilinearSections.res.{u + 1, u, u + 1}
            (coefficientSystemMap l (ULift.{u} (Padic l)) T)).obj
              (lineModule l (ULift.{u} (Padic l)) c)) n U).symm) v y
      ((hv.trans (heq_of_eq (scalarUnit_section l T c _ x).symm)).trans hy.symm)
  change (c.rootForget.hom.app (op n)).hom.app U
    ((a.inv.app (op n)).hom.app U ((b.hom.app (op n)).hom.app U v)) = _
  rw [hby]
  congr 1
  change ((a.hom.app (op n)) ≫ (a.inv.app (op n))).hom.app U x' = x'
  rw [a.hom_inv_id_app]
  rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
