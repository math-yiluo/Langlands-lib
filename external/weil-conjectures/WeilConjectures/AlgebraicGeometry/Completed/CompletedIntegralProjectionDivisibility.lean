/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
/-! # Divisibility of the kernel of a finite coefficient projection

Source: blueprint main-20261015, coefficient convention in prose-09-21.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u w v z
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
@[irreducible] private def qm {A : Type u} [CommRing A] (π : A) (m r : ℕ) :
    A ⧸ Ideal.span ({π} : Set A) ^ r → A ⧸ Ideal.span ({π} : Set A) ^ (m + r) :=
  Quotient.lift (fun a ↦ Ideal.Quotient.mk _ (π ^ m * a)) (by
    intro a b hab
    apply Ideal.Quotient.eq.mpr
    have h : a - b ∈ Ideal.span ({π} : Set A) ^ r := Ideal.Quotient.eq.mp
      (Quotient.sound hab : Ideal.Quotient.mk _ a = Ideal.Quotient.mk _ b)
    rw [← mul_sub]
    have := Ideal.mul_mem_mul (Ideal.pow_mem_pow
      (Ideal.subset_span (Set.mem_singleton π)) m) h
    simpa only [← pow_add, Nat.add_comm m r] using this)

private theorem qm_mk {A : Type u} [CommRing A] (π : A) (m r : ℕ) (a : A) :
    qm π m r (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (π ^ m * a) := by
  unfold qm
  rfl

private theorem qm_inj {A : Type u} [CommRing A] [IsDomain A]
    (π : A) (hπ : π ≠ 0) (m r : ℕ) : Function.Injective (qm π m r) := by
  intro x y h
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [qm_mk, qm_mk] at h
  rw [Ideal.Quotient.eq, ← mul_sub, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at h
  obtain ⟨d, hd⟩ := h
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨d, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero m hπ)
  calc
    π ^ m * (d * π ^ r) = d * π ^ (m + r) := by rw [pow_add]; ring
    _ = π ^ m * (a - b) := hd

private theorem qm_pullback {A : Type u} [CommRing A] [IsDomain A]
    (π : A) (hπ : π ≠ 0) (m r : ℕ) :
    IsPullback (TypeCat.ofHom (qm π m r))
      (TypeCat.ofHom (fun _ ↦ PUnit.unit))
      (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_add_right m r)))
      (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦ (0 : A ⧸ Ideal.span ({π} : Set A) ^ m))) := by
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_add_right m r)
      (qm π m r (Ideal.Quotient.mk _ a)) = 0
    rw [qm_mk]
    change Ideal.Quotient.mk _ (π ^ m * a) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow
      (Ideal.subset_span (Set.mem_singleton π)) m)
  · intro x y h
    exact qm_inj π hπ m r h.1
  · intro x z hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (Ideal.span {π} ^ m) b = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton'] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨Ideal.Quotient.mk _ a, ?_, Subsingleton.elim _ _⟩
    change qm π m r (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ b
    rw [qm_mk]
    rw [mul_comm, ha]

private theorem qmF {A : Type u} [CommRing A] [IsDomain A]
    (π : A) (hπ : π ≠ 0) (m r : ℕ) (F : Type u ⥤ Type z)
    [PreservesFiniteLimits F] (x : F.obj (A ⧸ Ideal.span ({π} : Set A) ^ (m + r)))
    (z : F.obj PUnit.{u + 1})
    (hx : F.map (TypeCat.ofHom
      (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_add_right m r))) x =
      F.map (TypeCat.ofHom (fun _ : PUnit.{u + 1} ↦
        (0 : A ⧸ Ideal.span ({π} : Set A) ^ m))) z) :
    ∃! y, F.map (TypeCat.ofHom (qm π m r)) y = x := by
  have hp := (qm_pullback π hπ m r).map F
  obtain ⟨y, hy, _⟩ := Types.exists_of_isPullback hp x z hx
  refine ⟨y, hy, ?_⟩
  intro y' hy'
  apply Types.ext_of_isPullback hp (hy'.trans hy.symm)
  have : Subsingleton (F.obj PUnit.{u + 1}) := by
    let h : IsTerminal PUnit.{u + 1} := Types.isTerminalPUnit
    let := (Types.isTerminalEquivUnique _).toFun (h.isTerminalObj F)
    infer_instance
  exact Subsingleton.elim _ _

private theorem kernel_family {A : Type u} [CommRing A] [IsDomain A]
    (π : A) (hπ : π ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (F : Type u ⥤ Type z) [PreservesFiniteLimits F]
    (x : ∀ n : ℕ, F.obj (A ⧸ Ideal.span ({π} : Set A) ^ (n + 1)))
    (hx : ∀ (i j : ℕ) (h : i ≤ j),
      F.map (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
        (Nat.add_le_add_right h 1))) (x j) = x i)
    (z : F.obj PUnit.{u + 1})
    (hz : F.map (TypeCat.ofHom
      (fun _ : PUnit.{u + 1} ↦
        (0 : A ⧸ Ideal.span ({π} : Set A) ^ (m - 1 + 1)))) z = x (m - 1)) :
    ∃ y : ∀ n : ℕ, F.obj (A ⧸ Ideal.span ({π} : Set A) ^ (n + 1)),
      (∀ (i j : ℕ) (h : i ≤ j),
        F.map (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
          (Nat.add_le_add_right h 1))) (y j) = y i) ∧
      ∀ n : ℕ, F.map (TypeCat.ofHom
        (fun a : A ⧸ Ideal.span ({π} : Set A) ^ (n + 1) ↦
          Ideal.Quotient.mk _ (π ^ m) * a)) (y n) = x n := by
  classical
  cases m with
  | zero => omega
  | succ m =>
    let xx (n : ℕ) : F.obj (A ⧸ Ideal.span ({π} : Set A) ^ ((m + 1) + (n + 1))) :=
      x ((m + 1) + n)
    have hxzero (n : ℕ) : F.map (TypeCat.ofHom
        (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_add_right (m + 1) (n + 1))))
          (xx n) = F.map (TypeCat.ofHom
            (fun _ : PUnit.{u + 1} ↦ (0 : A ⧸ Ideal.span ({π} : Set A) ^ (m + 1)))) z := by
      have hh := (hx m ((m + 1) + n) (by omega)).trans hz.symm
      convert hh using 1
    have hy (n : ℕ) := qmF π hπ (m + 1) (n + 1) F (xx n) z (hxzero n)
    choose y hy hyuniq using hy
    refine ⟨y, ?_, ?_⟩
    · intro i j hij
      apply hyuniq i
      have hcomm :
          TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
            (Nat.add_le_add_right hij 1)) ≫ TypeCat.ofHom (qm π (m + 1) (i + 1)) =
          TypeCat.ofHom (qm π (m + 1) (j + 1)) ≫
            TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
              (Nat.add_le_add_left (Nat.add_le_add_right hij 1) (m + 1))) := by
        ext a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change qm π (m + 1) (i + 1) (Ideal.Quotient.mk _ a) =
          Ideal.Quotient.factorPow (Ideal.span {π})
            (Nat.add_le_add_left (Nat.add_le_add_right hij 1) (m + 1))
              (qm π (m + 1) (j + 1) (Ideal.Quotient.mk _ a))
        rw [qm_mk, qm_mk]
        rfl
      change (F.map (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
        (Nat.add_le_add_right hij 1))) ≫ F.map (TypeCat.ofHom (qm π (m + 1) (i + 1))))
          (y j) = xx i
      rw [← F.map_comp, hcomm, F.map_comp]
      change F.map _ (F.map _ (y j)) = _
      rw [hy j]
      convert (hx ((m + 1) + i) ((m + 1) + j)
        (Nat.add_le_add_left hij (m + 1))) using 1
    · intro n
      have hcomm :
          TypeCat.ofHom (fun a : A ⧸ Ideal.span ({π} : Set A) ^ (n + 1) ↦
            Ideal.Quotient.mk _ (π ^ (m + 1)) * a) =
          TypeCat.ofHom (qm π (m + 1) (n + 1)) ≫
            TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
              (Nat.le_add_left (n + 1) (m + 1))) := by
        ext a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change Ideal.Quotient.mk _ (π ^ (m + 1)) * Ideal.Quotient.mk _ a =
          Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_add_left (n + 1) (m + 1))
            (qm π (m + 1) (n + 1) (Ideal.Quotient.mk _ a))
        rw [qm_mk]
        exact (map_mul (Ideal.Quotient.mk _) _ _).symm
      rw [hcomm, F.map_comp]
      change F.map _ (F.map _ (y n)) = _
      rw [hy n]
      convert (hx n ((m + 1) + n) (Nat.le_add_left n (m + 1))) using 1
section
variable {C : Type w} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{u}] [HasSheafify J (Type u)]
  [J.PreservesSheafification (forget CommRingCat.{u})]
  [J.HasSheafCompose (forget CommRingCat.{u})]
private def ct (U : Cᵒᵖ) : Type u ⥤ Type u :=
  (Functor.const Cᵒᵖ) ⋙ presheafToSheaf J (Type u) ⋙
    sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj U
private def ce (A : CommRingCat.{u}) :
    sheafify J ((Functor.const Cᵒᵖ).obj ((forget CommRingCat.{u}).obj A)) ≅
      sheafify J ((Functor.const Cᵒᵖ).obj A) ⋙ forget CommRingCat.{u} :=
  (Functor.mapIso (presheafToSheaf J (Type u) ⋙ sheafToPresheaf J (Type u))
    (Functor.constComp Cᵒᵖ A (forget CommRingCat.{u})).symm) ≪≫
      sheafifyComposeIso J (forget CommRingCat.{u}) ((Functor.const Cᵒᵖ).obj A)
private theorem ce_unit (A : CommRingCat.{u}) :
    toSheafify J ((Functor.const Cᵒᵖ).obj ((forget CommRingCat.{u}).obj A)) ≫
      (ce J A).hom =
      (Functor.constComp Cᵒᵖ A (forget CommRingCat.{u})).inv ≫
      Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj A)) (forget CommRingCat.{u}) :=
  by
    change toSheafify J _ ≫ (sheafifyMap J _) ≫ _ = _
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
      sheafComposeIso_hom_fac]
    rfl
private def cmul {A B : CommRingCat.{u}} (q : A ⟶ B) (b : B) :
    (sheafify J ((Functor.const Cᵒᵖ).obj A) ⋙ forget CommRingCat.{u}) ⟶
      (sheafify J ((Functor.const Cᵒᵖ).obj B) ⋙ forget CommRingCat.{u}) where
  app U := TypeCat.ofHom (fun x ↦
    (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b *
      (sheafifyMap J ((Functor.const Cᵒᵖ).map q)).app U x)
  naturality {U V} f := by
    ext x
    have h := congrArg (fun h ↦ h b)
      ((toSheafify J ((Functor.const Cᵒᵖ).obj B)).naturality f)
    dsimp at h ⊢
    rw [map_mul, ← h]
    have hq := congrArg (fun h ↦ h x)
      ((sheafifyMap J ((Functor.const Cᵒᵖ).map q)).naturality f)
    exact congrArg (_ * ·) (by simpa only [CommRingCat.comp_apply] using hq)
private theorem ct_mul {A B : CommRingCat.{u}} (q : A ⟶ B) (b : B)
    (U : Cᵒᵖ) (x : (sheafify J ((Functor.const Cᵒᵖ).obj A)).obj U) :
    (ce J B).hom.app U ((ct J U).map (TypeCat.ofHom (fun a : A ↦ b * q a))
      ((ce J A).inv.app U x)) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b *
        (sheafifyMap J ((Functor.const Cᵒᵖ).map q)).app U x := by
  have h :
      (sheafifyMap J ((Functor.const Cᵒᵖ).map
        (TypeCat.ofHom (fun a : A ↦ b * q a)))) ≫
        (ce J B).hom = (ce J A).hom ≫ cmul J q b := by
    have hQ : Presheaf.IsSheaf J
        (sheafify J ((Functor.const Cᵒᵖ).obj B) ⋙ forget CommRingCat.{u}) :=
      ((sheafCompose J (forget CommRingCat.{u})).obj
        ((constantSheaf J CommRingCat.{u}).obj B)).property
    apply sheafify_hom_ext _ _ _ hQ
    rw [← Category.assoc, ← toSheafify_naturality, Category.assoc, ce_unit]
    rw [← Category.assoc (toSheafify J _), ce_unit]
    ext V a
    change (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V (b * q a) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app V b *
        (sheafifyMap J ((Functor.const Cᵒᵖ).map q)).app V
          ((toSheafify J ((Functor.const Cᵒᵖ).obj A)).app V a)
    rw [map_mul]
    congr 1
    have hn := congrArg (fun h ↦ h.app V a)
      (toSheafify_naturality J ((Functor.const Cᵒᵖ).map q))
    exact hn
  have h' := congrArg (fun h ↦ h.app U ((ce J A).inv.app U x)) h
  change _ = (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b *
    (sheafifyMap J ((Functor.const Cᵒᵖ).map q)).app U
      ((ce J A).hom.app U ((ce J A).inv.app U x)) at h'
  have hi : (ce J A).hom.app U ((ce J A).inv.app U x) = x :=
    congrArg (fun h ↦ h.app U x) (ce J A).inv_hom_id
  rw [hi] at h'
  exact h'

private theorem ct_map {A B : CommRingCat.{u}} (q : A ⟶ B)
    (U : Cᵒᵖ) (x : (sheafify J ((Functor.const Cᵒᵖ).obj A)).obj U) :
    (ce J B).hom.app U ((ct J U).map ((forget CommRingCat.{u}).map q)
      ((ce J A).inv.app U x)) =
      (sheafifyMap J ((Functor.const Cᵒᵖ).map q)).app U x := by
  simpa only [one_mul, map_one] using ct_mul J q 1 U x

private theorem ct_map_direct {A B : CommRingCat.{u}} (q : A ⟶ B)
    (U : Cᵒᵖ) (x : (ct J U).obj A) :
    (ce J B).hom.app U ((ct J U).map ((forget CommRingCat.{u}).map q) x) =
      (sheafifyMap J ((Functor.const Cᵒᵖ).map q)).app U ((ce J A).hom.app U x) := by
  have h := ct_map J q U ((ce J A).hom.app U x)
  have hi : (ce J A).inv.app U ((ce J A).hom.app U x) = x :=
    congrArg (fun h ↦ h.app U x) (ce J A).hom_inv_id
  with_unfolding_all rwa [hi] at h

private theorem ct_mul_direct {A B : CommRingCat.{u}} (q : A ⟶ B) (b : B)
    (U : Cᵒᵖ) (x : (ct J U).obj A) :
    (ce J B).hom.app U ((ct J U).map (TypeCat.ofHom (fun a : A ↦ b * q a)) x) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app U b *
        (sheafifyMap J ((Functor.const Cᵒᵖ).map q)).app U ((ce J A).hom.app U x) := by
  have h := ct_mul J q b U ((ce J A).hom.app U x)
  have hi : (ce J A).inv.app U ((ce J A).hom.app U x) = x :=
    congrArg (fun h ↦ h.app U x) (ce J A).hom_inv_id
  with_unfolding_all rwa [hi] at h

private theorem ce_injective (A : CommRingCat.{u}) (U : Cᵒᵖ) :
    Function.Injective ((ce J A).hom.app U) :=
  ((ce J A).app U).toEquiv.injective

private theorem ce_inv (A : CommRingCat.{u}) (U : Cᵒᵖ)
    (x : (sheafify J ((Functor.const Cᵒᵖ).obj A)).obj U) :
    (ce J A).hom.app U ((ce J A).inv.app U x) = x :=
  congrArg (fun h ↦ h.app U x) (ce J A).inv_hom_id

end

open WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})
private def quotientTower : ℕᵒᵖ ⥤ CommRingCat.{max u (t + 1)} where
  obj n := CommRingCat.of (ULift.{t + 1}
    (Padic.coefficientExtensionIntegers l E ⧸
      Padic.coefficientExtensionIdeal l E (n.unop + 1)))
  map f := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPow (Ideal.span {Padic.coefficientExtensionUniformizer l E})
      (Nat.add_le_add_right (leOfHom f.unop) 1)).comp ULift.ringEquiv.toRingHom))
  map_id n := by
    ext x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn with
    | h x => rfl
  map_comp f g := by
    ext x
    rcases x with ⟨x⟩
    induction x using Quotient.inductionOn with
    | h x => rfl

private theorem coefficientTower_map (i j : ℕ) (hij : i ≤ j) :
    (integralCoefficientSheafSystem l E T).map (homOfLE hij).op =
      ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}) ⋙
        sheafCompose _ (forget₂ CommRingCat RingCat)).map
          ((quotientTower.{t, u} l E).map (homOfLE hij).op) := by
  let h : integralCoefficientSheafSystem l E T ⟶ quotientTower.{t, u} l E ⋙
      constantSheaf _ _ ⋙ sheafCompose _ (forget₂ CommRingCat RingCat) :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (fun n ↦ by
      simp only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.comp_map, Category.comp_id, Category.id_comp]
      rfl)
  exact (Category.comp_id _).symm.trans ((h.naturality (homOfLE hij).op).trans
    (Category.id_comp _))

private theorem uniformizer_ne_zero : Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  let A := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsDiscreteValuationRing A := h.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({π} : Set A) = Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
    (hm.symm.trans hgen.symm)).ne_zero

/-- The kernel of the positive uniformizer-level projection is generated by that power.
Source: blueprint main-20261015, coefficient convention, prose-09-21;
the finite-quotient uniqueness argument in the completed-coefficient comparison.
(blueprint: lem-sp-completed-integral-projection-divisibility)

Proof: Put O = O_E and pi = pi_E. The recorded DVR structure makes pi a nonzero
nonzerodivisor. For every r >= 1, multiplication by pi^(n+1) induces an additive
isomorphism from O/(pi^r) onto the kernel of O/(pi^(r+n+1)) -> O/(pi^(n+1)).
Surjectivity is the principal-ideal membership formula; injectivity cancels pi^(n+1)
in the domain O. The isomorphisms commute with the quotient reductions. Constant
sheafification preserves these kernel diagrams and these isomorphisms, as it is left
exact on the underlying abelian groups. Evaluation computes the kernels sectionwise.
Apply the inverse isomorphisms to the shifted projections of x. Their compatibility
produces a section y of the original inverse-limit sheaf, using the sectionwise limit
universal property. Multiplying y by the constant pi^(n+1) has the same projection as x
at every level, hence equals x. For levels below n+1 use that both reduce to zero;
for higher levels use the defining finite-level isomorphism. The constant pi section
in the completion is the image under the actual constant-to-completed limit lift,
so the scalar used here is exactly the one displayed. This proves the claim for every
site object, with independent site and coefficient universes; no sheafification is
interchanged with an infinite limit. -/
theorem completedIntegralProjection_divisible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U)
    (_hx : (limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U x = 0) :
    ∃ y : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U,
      x = ((integralConstantToCompletionOfUniverses l E T).hom.app U
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
              (ULift.up (Padic.coefficientExtensionUniformizer l E)))) ^ (n + 1) * y := by
  have hx := _hx
  -- Pin the size universe used by sheafification instances on the pro-étale site.
  have : LocallySmall.{max u (t + 1)} T.ProEt := inferInstance
  classical
  let J := Scheme.ProEt.topology T
  have : HasColimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, max u (t + 1), max u (t + 1)} _
  have : PreservesFilteredColimitsOfSize.{t + 1, t + 1} (forget CommRingCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t + 1, max u (t + 1)} _
  have : J.PreservesSheafification (forget CommRingCat.{max u (t + 1)}) :=
    GrothendieckTopology.instPreservesSheafification J _
  let A := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  let F : Type u ⥤ Type (max u (t + 1)) := uliftFunctor.{t + 1} ⋙ ct.{max u (t + 1)} J U
  have hF : PreservesFiniteLimits F := by
    dsimp [F, ct]
    infer_instance
  let B (k : ℕ) := CommRingCat.of (ULift.{t + 1} (A ⧸ Ideal.span {π} ^ (k + 1)))
  let p (k : ℕ) := (limit.π (integralCoefficientSheafSystem l E T) (op k)).hom.app U
  let xx (k : ℕ) : F.obj (A ⧸ Ideal.span {π} ^ (k + 1)) :=
    (ce.{max u (t + 1)} J (B k)).inv.app U (p k x)
  have hxx (i j : ℕ) (hij : i ≤ j) :
      F.map (TypeCat.ofHom (Ideal.Quotient.factorPow (Ideal.span {π})
        (Nat.add_le_add_right hij 1))) (xx j) = xx i := by
    apply ce_injective J (B i) U
    rw [ce_inv]
    change (ce J (B i)).hom.app U
      ((ct.{max u (t + 1)} J U).map ((forget CommRingCat.{max u (t + 1)}).map
        ((quotientTower.{t, u} l E).map (homOfLE hij).op))
          ((ce J (B j)).inv.app U (p j x))) = p i x
    have hw := congrArg (fun h ↦ h.hom.app U x)
      (limit.w (integralCoefficientSheafSystem l E T) (homOfLE hij).op)
    rw [coefficientTower_map] at hw
    exact (ct_map J ((quotientTower.{t, u} l E).map (homOfLE hij).op) U (p j x)).trans hw
  let z : F.obj PUnit.{u + 1} :=
    (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (ULift.{t + 1} PUnit.{u + 1}))).app U
      (ULift.up PUnit.unit)
  have hz : F.map (TypeCat.ofHom
      (fun _ : PUnit.{u + 1} ↦ (0 : A ⧸ Ideal.span {π} ^ (n + 1)))) z = xx n := by
    apply ce_injective J (B n) U
    rw [ce_inv]
    change (ce J (B n)).hom.app U
      ((ct.{max u (t + 1)} J U).map (TypeCat.ofHom
        (fun _ : ULift.{t + 1} PUnit.{u + 1} ↦ (0 : B n))) z) = p n x
    have hu := congrArg (fun h ↦ h.app U (ULift.up PUnit.unit))
      (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map
        (TypeCat.ofHom (fun _ : ULift.{t + 1} PUnit.{u + 1} ↦ (0 : B n)))))
    have hu' := congrArg ((ce J (B n)).hom.app U) hu
    have he := congrArg (fun h ↦ h.app U (0 : ((forget CommRingCat).obj (B n))))
      (ce_unit J (B n))
    exact hu'.symm.trans ((he.trans
      (((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B n))).app U).hom.map_zero)).trans
        hx.symm)
  obtain ⟨yy, hyy, hmul⟩ := kernel_family π (uniformizer_ne_zero l E) (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) F xx hxx z (by simpa using hz)
  let ev : Sheaf J RingCat.{max u (t + 1)} ⥤ Type (max u (t + 1)) :=
    sheafToPresheaf J RingCat.{max u (t + 1)} ⋙
      (evaluation T.ProEtᵒᵖ RingCat.{max u (t + 1)}).obj U ⋙ forget RingCat
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves ev (limit.isLimit (integralCoefficientSheafSystem l E T)))
  let ys : (integralCoefficientSheafSystem l E T ⋙ ev).sections :=
    ⟨fun k ↦ (ce J (B k.unop)).hom.app U (yy k.unop), by
      intro i j f
      have hh := hyy j.unop i.unop (leOfHom f.unop)
      have hh := congrArg ((ce J (B j.unop)).hom.app U) hh
      change (ce J (B j.unop)).hom.app U
        ((ct.{max u (t + 1)} J U).map ((forget CommRingCat.{max u (t + 1)}).map
          ((quotientTower.{t, u} l E).map f)) (yy i.unop)) = _ at hh
      have hh := (ct_map_direct J ((quotientTower.{t, u} l E).map f) U
        (yy i.unop)).symm.trans hh
      change ((integralCoefficientSheafSystem l E T).map f).hom.app U
        ((ce J (B i.unop)).hom.app U (yy i.unop)) = _
      rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
      rw [coefficientTower_map]
      exact hh⟩
  let y : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U := e.symm ys
  have hyp (k : ℕ) : p k y = (ce J (B k)).hom.app U (yy k) :=
    Types.isLimitEquivSections_symm_apply
      (isLimitOfPreserves ev (limit.isLimit (integralCoefficientSheafSystem l E T))) ys (op k)
  let scalar : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U :=
    (integralConstantToCompletionOfUniverses l E T).hom.app U
      ((toSheafify J ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} A)))).app U (ULift.up π))
  refine ⟨y, ?_⟩
  apply e.injective
  apply Subtype.ext
  funext k
  change p k.unop x = p k.unop (scalar ^ (n + 1) * y)
  rw [map_mul, map_pow, hyp]
  have hh := congrArg ((ce J (B k.unop)).hom.app U) (hmul k.unop)
  rw [ce_inv] at hh
  change (ce J (B k.unop)).hom.app U
    ((ct.{max u (t + 1)} J U).map
      (TypeCat.ofHom (fun a : B k.unop ↦
        (ULift.up (Ideal.Quotient.mk _ (π ^ (n + 1))) : B k.unop) * a))
      (yy k.unop)) = p k.unop x at hh
  have hh' := ct_mul_direct J (𝟙 (B k.unop))
    (ULift.up (Ideal.Quotient.mk _ (π ^ (n + 1))) : B k.unop) U (yy k.unop)
  have hid : sheafifyMap J ((Functor.const T.ProEtᵒᵖ).map (𝟙 (B k.unop))) = 𝟙 _ := by
    change (presheafToSheaf J CommRingCat.{max u (t + 1)} ⋙
      sheafToPresheaf J CommRingCat.{max u (t + 1)}).map
        ((Functor.const T.ProEtᵒᵖ).map (𝟙 (B k.unop))) = _
    rw [(Functor.const T.ProEtᵒᵖ).map_id]
    exact (presheafToSheaf J CommRingCat.{max u (t + 1)} ⋙
      sheafToPresheaf J CommRingCat.{max u (t + 1)}).map_id _
  have hh : _ = p k.unop x := hh'.symm.trans hh
  rw [hid] at hh
  let bsection : (sheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k.unop))).obj U :=
    (ce J (B k.unop)).hom.app U (yy k.unop)
  change (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k.unop))).app U
    (ULift.up (Ideal.Quotient.mk _ (π ^ (n + 1)))) * bsection = p k.unop x at hh
  rw [← hh]
  congr 1
  let O := CommRingCat.of (ULift.{t + 1} A)
  let φ : O ⟶ B k.unop := CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Ideal.span {π} ^ (k.unop + 1))).comp
        ULift.ringEquiv.toRingHom))
  let a : (integralConstantRingOfUniverses l E T).obj.obj U :=
    (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj O)).app U (ULift.up π)
  have hc : p k.unop ((integralConstantToCompletionOfUniverses l E T).hom.app U a) =
      (integralConstantQuotientOfUniverses l E T k.unop).hom.app U a :=
    congrArg (fun h ↦ h.hom.app U a)
      (limit.lift_π (integralConstantConeOfUniverses l E T) (op k.unop))
  have hn := congrArg (fun h ↦ h.app U (ULift.up π))
    (toSheafify_naturality J ((Functor.const T.ProEtᵒᵖ).map φ))
  have hscalar : p k.unop
      ((integralConstantToCompletionOfUniverses l E T).hom.app U a) =
        (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k.unop))).app U
          (ULift.up (Ideal.Quotient.mk _ π)) := hc.trans hn.symm
  change (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k.unop))).app U
      (ULift.up (Ideal.Quotient.mk _ (π ^ (n + 1)))) =
    (p k.unop ((integralConstantToCompletionOfUniverses l E T).hom.app U a)) ^ (n + 1)
  rw [hscalar]
  let s := (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (B k.unop))).app U
  have hpow : (ULift.up (Ideal.Quotient.mk _ (π ^ (n + 1))) : B k.unop) =
      (ULift.up (Ideal.Quotient.mk _ π) : B k.unop) ^ (n + 1) := by
    apply ULift.ext
    exact map_pow (Ideal.Quotient.mk _) π (n + 1)
  exact (congrArg s hpow).trans (s.hom.map_pow _ _)
end AlgebraicGeometry.ProEtale
