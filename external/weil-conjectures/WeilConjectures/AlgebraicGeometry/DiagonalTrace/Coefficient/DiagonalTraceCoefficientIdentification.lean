/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTraceModels
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerForgetEvaluation

/-! # The finite coefficient-unit identification -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses WeilConjectures

private theorem integral_mem (l : ℕ) [Fact l.Prime] (x : ULift.{u} (Padic l)) :
    x ∈ Padic.coefficientExtensionIntegers l (ULift.{u} (Padic l)) ↔ ‖x.down‖ ≤ 1 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l (ULift.{u} (Padic l))).choose_spec.1 x
  refine h.trans ?_
  have he := spectralNorm_extends (K := Padic l) (L := ULift.{u} (Padic l)) x.down
  change spectralNorm (Padic l) (ULift.{u} (Padic l)) x ≤ 1 ↔ ‖x.down‖ ≤ 1
  rw [show spectralNorm (Padic l) (ULift.{u} (Padic l)) x = ‖x.down‖ from he]

private def integerEquiv (l : ℕ) [Fact l.Prime] :
    Padic.coefficientExtensionIntegers l (ULift.{u} (Padic l)) ≃+* ℤ_[l] where
  toFun x := ⟨x.val.down, (integral_mem l x.val).mp x.property⟩
  invFun x := ⟨ULift.up (x : Padic l), (integral_mem l _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def quotientEquiv (l : ℕ) [Fact l.Prime] (n : ℕ) :
    SpTowerShriek.R l (ULift.{u} (Padic l)) n ≃+* ZMod (l ^ (n + 1)) := by
  let e := integerEquiv.{u} l
  have hi : RingHom.ker (PadicInt.toZModPow (n + 1)) =
      Ideal.map e.toRingHom (spEllIdeal l (ULift.{u} (Padic l)) ^ (n + 1)) := by
    rw [PadicInt.ker_toZModPow, Ideal.map_pow, spEllIdeal, Ideal.map_span,
      Set.image_singleton, map_natCast, Ideal.span_singleton_pow]
  exact (Ideal.quotientEquiv _ _ e hi).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow _)))

private theorem coefficientMap_iso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (n : ℕ) :
    IsIso (SpTowerClasses.coefficientMap l (ULift.{u} (Padic l)) T n) := by
  let e : ULift.{u + 1} (ZMod (l ^ (n + 1))) ≃+*
      ULift.{u + 1} (SpTowerShriek.R l (ULift.{u} (Padic l)) n) :=
    ULift.ringEquiv.trans ((quotientEquiv.{u} l n).symm.trans ULift.ringEquiv.symm)
  let f := ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
    ((ZMod.castHom (ringChar.dvd (coefficient_annihilates l (ULift.{u} (Padic l)) n))
      (SpTowerShriek.R l (ULift.{u} (Padic l)) n)).comp
        ULift.ringEquiv.{0, u + 1}.toRingHom)
  have hf : f = e.toRingHom := by
    apply (RingHom.cancel_right (f := ULift.ringEquiv.symm.toRingHom)
      (fun x ↦ ⟨x.down, rfl⟩)).mp
    exact Subsingleton.elim _ _
  have he : IsIso (CommRingCat.ofHom f) := by
    rw [hf]
    exact inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  exact Functor.map_isIso (constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (CommRingCat.ofHom f)

private theorem coefficient_vertical (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (n : ℕ) {U V : T.ProEtᵒᵖ} (f : U ⟶ V) :
    ((coefficient T B).val.map (Prod.mkHom (𝟙 n) f.unop).op).hom.toAddMonoidHom =
      ((B.obj (op n)).obj.map f).hom.toAddMonoidHom := by
  let F := SemilinearSections.rings (Scheme.ProEt.topology T)
    (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op) ⋙
    sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}
  change ((F.map (𝟙 (op n))).app U ≫ (F.obj (op n)).map f).hom.toAddMonoidHom = _
  rw [F.map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  rfl

private theorem coefficient_horizontal (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (n : ℕ) (U : T.ProEtᵒᵖ) :
    ((coefficient T B).val.map
      (Prod.mkHom (homOfLE (Nat.le_succ n)) (𝟙 U.unop)).op).hom.toAddMonoidHom =
      ((B.map (homOfLE (Nat.le_succ n)).op).hom.app U).hom.toAddMonoidHom := by
  let R := SemilinearSections.rings (Scheme.ProEt.topology T)
    (fun n ↦ B.obj (op n)) (fun n ↦ B.map (homOfLE (Nat.le_succ n)).op)
  let F := R ⋙ sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}
  change ((F.map (homOfLE (Nat.le_succ n)).op).app U ≫
    (F.obj (op n)).map (𝟙 U)).hom.toAddMonoidHom = _
  rw [(F.obj (op n)).map_id, Category.comp_id]
  change ((R.map (homOfLE (Nat.le_succ n)).op).hom.app U).hom.toAddMonoidHom = _
  simp only [R, SemilinearSections.rings, Functor.ofOpSequence_map_homOfLE_succ]

private def coefficientLevelIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ) :
    (diagonalForget l T).obj
        ((r.F.obj (coefficient T (Arings l (ULift.{u} (Padic l)) T))).obj (op n)) ≅
      (sheafCompose (Scheme.ProEt.topology T)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            ((Arings l (ULift.{u} (Padic l)) T).obj (op n)) := by
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun U ↦
    eqToIso (r.underlying (coefficient T (Arings l (ULift.{u} (Padic l)) T)) n U)) ?_)
  intro U V g
  refine transport_addHom
    (r.underlying (coefficient T (Arings l (ULift.{u} (Padic l)) T)) n U)
    (r.underlying (coefficient T (Arings l (ULift.{u} (Padic l)) T)) n V) _ _ ?_
  have h := r.restrictions (coefficient T (Arings l (ULift.{u} (Padic l)) T)) n g
  exact h.trans (heq_of_eq (coefficient_vertical T _ n g))

private def coefficientUnderlyingIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Restriction l (ULift.{u} (Padic l)) T) :
    r.F.obj (coefficient T (Arings l (ULift.{u} (Padic l)) T)) ⋙ diagonalForget l T ≅
      Arings l (ULift.{u} (Padic l)) T ⋙
        sheafCompose (Scheme.ProEt.topology T)
          ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
            forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) := by
  let η : r.F.obj (coefficient T (Arings l (ULift.{u} (Padic l)) T)) ⋙
      diagonalForget l T ⟶ Arings l (ULift.{u} (Padic l)) T ⋙
      sheafCompose (Scheme.ProEt.topology T)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
    NatTrans.ofOpSequence (fun n ↦ (coefficientLevelIso l T r n).hom) (by
    intro n
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    refine transport_addHom
      (r.underlying (coefficient T (Arings l (ULift.{u} (Padic l)) T)) (n + 1) U)
      (r.underlying (coefficient T (Arings l (ULift.{u} (Padic l)) T)) n U) _ _ ?_
    have h := r.transitions (coefficient T (Arings l (ULift.{u} (Padic l)) T))
      (Nat.le_succ n) U
    exact h.trans (heq_of_eq (coefficient_horizontal T _ n U)))
  have : IsIso η := by
    apply (NatTrans.isIso_iff_isIso_app η).2
    intro n
    exact inferInstanceAs (IsIso (coefficientLevelIso l T r n.unop).hom)
  exact asIso η

private def coefficientRingIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    Rrings l T ≅ Arings l (ULift.{u} (Padic l)) T := by
  let η : Rrings l T ⟶ Arings l (ULift.{u} (Padic l)) T :=
    NatTrans.ofOpSequence (SpTowerClasses.coefficientMap l (ULift.{u} (Padic l)) T) (by
      intro n
      exact (coefficientMap_transition l (ULift.{u} (Padic l)) T n).symm)
  have : IsIso η := by
    apply (NatTrans.isIso_iff_isIso_app η).2
    intro n
    exact coefficientMap_iso l T n.unop
  exact asIso η

/-- The unital additive identification of the restricted coefficient tower.

Source: blueprint latest, `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1),
finite scalar restriction and the coefficient-unit identification.
(blueprint: lem-sfb-diagonal-trace-coefficient-identification).

Proof: the spectral absolute value on ULift Q_l is the lifted p-adic absolute
value. Its valuation-one subring identifies with Z_l by the lifted identity.
The quotient by l^(n+1) therefore identifies with Z/l^(n+1), by the surjective
residue map with kernel (l^(n+1)). Apply constant sheafification to these unital
ring isomorphisms, then forget to additive groups. The section, restriction and
transition equations of r identify its underlying coefficient tower with the
one just constructed. Quotient reductions commute with the residue maps, so
these comparisons form a tower isomorphism. Each map preserves one, which gives
the displayed equation after transporting by the section equality of r.
The argument includes the first positive level and the zero sheaf on an empty
site. No completed projection or root module enters the construction. -/
@[no_expose] def diagonalTraceCoefficientIdentification (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (r : Restriction l (ULift.{u} (Padic l)) T) :
    r.F.obj (coefficient T (Arings l (ULift.{u} (Padic l)) T)) ⋙ diagonalForget l T ≅
      Scheme.purTwistZlTower T l ⋙
        sheafCompose (Scheme.ProEt.topology T)
          ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
            forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}) :=
  coefficientUnderlyingIso l T r ≪≫
    Functor.isoWhiskerRight (coefficientRingIso l T).symm
      (sheafCompose (Scheme.ProEt.topology T)
        ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) ⋙
          forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1}))

/-- The coefficient identification sends the unit section to the unit section. -/
theorem diagonalTraceCoefficientIdentification_hom_app_hom_app_eq_one (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (r : Restriction l (ULift.{u} (Padic l)) T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((r.F.obj (coefficient T (Arings l (ULift.{u} (Padic l)) T))).obj
      (op n)).obj.obj U)
    (hx : HEq x (1 : (SpTowerClasses.systemRing l (ULift.{u} (Padic l)) T).obj.obj
      (op (n, U.unop)))) :
    ((diagonalTraceCoefficientIdentification l T r).hom.app (op n)).hom.app U x =
      (1 : (Scheme.purTwistFiniteRing T l n).obj.obj U) := by
  have hx' : (coefficientLevelIso l T r n).hom.hom.app U x =
      (1 : ((Arings l (ULift.{u} (Padic l)) T).obj (op n)).obj.obj U) := by
    exact transport_element
      (r.underlying (coefficient T (Arings l (ULift.{u} (Padic l)) T)) n U) x
      (1 : (SpTowerClasses.systemRing l (ULift.{u} (Padic l)) T).obj.obj
        (op (n, U.unop))) hx
  change ((coefficientRingIso l T).inv.app (op n)).hom.app U
    ((coefficientLevelIso l T r n).hom.hom.app U x) = _
  rw [hx']
  exact map_one (((coefficientRingIso l T).inv.app (op n)).hom.app U).hom

end AlgebraicGeometry.ProEtale.DiagonalTrace
