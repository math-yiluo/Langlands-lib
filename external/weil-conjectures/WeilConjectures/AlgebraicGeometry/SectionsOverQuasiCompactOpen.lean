/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.AlgebraicGeometry.IdealPowerComplement
import WeilConjectures.AlgebraicGeometry.IdealPowerEvaluationEventuallyZero
import WeilConjectures.AlgebraicGeometry.IdealPowerAnnihilatorSystem
import WeilConjectures.AlgebraicGeometry.IdealPowerQuotientLocalLifting
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Sections over the complement of a finite type ideal

Source: Stacks Project, Properties, Lemma 01PQ
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem power_mono {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι] :
    ∀ n : ℕ, Mono (idealSheafPower ι n).2 := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => dsimp [idealSheafPower]; infer_instance
  | one => exact inferInstanceAs (Mono ι)
  | more n _ ih =>
    let := ih
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    change Mono (idealModuleProductι ι (idealSheafPower ι (n + 1)).1 ≫
      (idealSheafPower ι (n + 1)).2)
    dsimp [idealModuleProductι]
    infer_instance

private theorem power_factor {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) {n m : ℕ} (h : n ≤ m) :
    ∃ r : (idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1,
      r ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2 := by
  have hs (k : ℕ) :
      ∃ r : (idealSheafPower ι (k + 1)).1 ⟶ (idealSheafPower ι k).1,
        r ≫ (idealSheafPower ι k).2 = (idealSheafPower ι (k + 1)).2 := by
    cases k with
    | zero => exact ⟨ι, Category.comp_id _⟩
    | succ k => exact ⟨idealModuleProductι ι _, rfl⟩
  induction h with
  | refl => exact ⟨𝟙 _, Category.id_comp _⟩
  | @step m h ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨t, ht⟩ := hs m
    exact ⟨t ≫ r, by rw [Category.assoc, hr, ht]⟩

private noncomputable def homDiagram {X : Scheme.{u}} (P Q : ℕ → X.Modules)
    (r : ∀ (n m : ℕ), n ≤ m → (P m ⟶ P n))
    (q : ∀ (n m : ℕ), n ≤ m → (Q n ⟶ Q m))
    (rid : ∀ n, r n n le_rfl = 𝟙 _)
    (qid : ∀ n, q n n le_rfl = 𝟙 _)
    (rcomp : ∀ n m k (h : n ≤ m) (h' : m ≤ k),
      r m k h' ≫ r n m h = r n k (h.trans h'))
    (qcomp : ∀ n m k (h : n ≤ m) (h' : m ≤ k),
      q n m h ≫ q m k h' = q n k (h.trans h')) : ℕ ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (P n ⟶ Q n)
  map {n m} f := AddCommGrpCat.ofHom
    { toFun := fun φ ↦ r n m (leOfHom f) ≫ φ ≫ q n m (leOfHom f)
      map_zero' := by simp
      map_add' := by intros; simp only [Preadditive.comp_add, Preadditive.add_comp] }
  map_id n := by ext φ; simp [rid, qid]
  map_comp {n m k} f g := by
    ext φ
    dsimp
    rw [← rcomp n m k (leOfHom f) (leOfHom g),
      ← qcomp n m k (leOfHom f) (leOfHom g)]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem colimit_eval_injective (D : ℕ ⥤ AddCommGrpCat.{u})
    (G : AddCommGrpCat.{u}) (c : D ⟶ (Functor.const ℕ).obj G)
    (hz : ∀ n (x : D.obj n), c.app n x = 0 →
      ∃ (m : ℕ) (f : n ⟶ m), D.map f x = 0) :
    Function.Injective (colimit.desc D ⟨G, c⟩) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (CategoryTheory.forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  apply (injective_iff_map_eq_zero (colimit.desc D ⟨G, c⟩).hom).2
  intro x hx
  obtain ⟨n, x, rfl⟩ := Concrete.colimit_exists_rep D x
  have hcx : c.app n x = 0 := by
    change (c.app n).hom x = (0 : G)
    exact (ConcreteCategory.congr_hom (colimit.ι_desc (F := D) ⟨G, c⟩ n) x).symm.trans hx
  obtain ⟨m, f, hf⟩ := hz n x hcx
  calc
    colimit.ι D n x = colimit.ι D m (D.map f x) := by
      exact (ConcreteCategory.congr_hom (colimit.w D f) x).symm
    _ = 0 := by rw [hf]; exact map_zero _

/-- Sections over the complement of a finite type quasi-coherent ideal on a quasi-compact
scheme. The open `U` is specified by surjectivity of the stalk inclusion, equivalently
by the stalk ideal being the whole local ring. The diagrams are identified with their
Hom groups by `e` and `e'`; their maps are exactly precomposition by the inclusions of
powers, and, in the quotient case, postcomposition by the induced quotient maps.
The cocones take a homomorphism to its value on the section `one n` above `1` on `U`.
In the quotient case this value is transported back through the quotient map on `U`.
The annihilator subsheaves are specified on every open, including all smaller opens.
Source: Stacks Project, Properties, Lemma 01PQ
(blueprint: lem-weil-pbc-sections-over-quasi-compact-open).

Proof:
1. By lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, the powers are
quasi-coherent finite type ideals, with affine sections I^n. By
lem-weil-pbc-quasi-coherent-ideal-zero-set-affine, the complement of their zero set is U.
On opens inside U the ideal contains 1, so equals the whole structure sheaf.
2. The affine tilde/Gamma adjunction and lem-weil-pbc-spec-module-tilde-sections identify
Hom of quasi-coherent modules with Hom of their affine sections, compatibly with
composition and restriction (lem-weil-pbc-affine-tilde-gamma-adjunction).
3. Evaluation at 1 commutes with restriction along powers. On D(f) it is phi(f^n)/f^n,
so agrees with the map of lem-weil-pbc-sections-over-quasi-compact-open-in-affine.
4. Cover X by finitely many affine opens. If evaluation is zero, the affine injectivity
and lem-weil-pbc-filtered-colimit-modules-elementwise give a power on which the map
vanishes on each open. Take the maximum exponent and use uniqueness of gluing
(lem-weil-pbc-glue-sheaves-of-modules) to get global vanishing and injectivity.
5. Form the annihilator subsheaves by lem-weil-pbc-sections-annihilated-by-ideal. They
increase and vanish on U. Their cokernels are quasi-coherent by
lem-weil-pbc-quasi-coherent-module-cokernel-image. Restriction preserves cokernels
(lem-weil-pbc-module-restriction-open-immersion-colimits), so the quotient maps are
isomorphisms on U; the quotient transition maps commute with evaluation there.
6. On each affine open the second comparison is the affine bijection, by the Hom
identification and the formula phi(f^n)/f^n in the quotient, transported back on D(f).
7. The same finite-cover argument proves injectivity for this second comparison.
8. Under quasi-separatedness choose a finite affine cover with quasi-compact overlaps
(lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings). Lift a section on each affine open
using the affine bijection. Cover the overlaps by finitely many affines; equality in
their colimits gives a common exponent where all lifts agree. Take the maximum and
glue by lem-weil-pbc-glue-sheaves-of-modules. This proves surjectivity. -/
theorem sections_over_quasiCompact_open {X : Scheme.{u}} [CompactSpace X]
    {I : X.Modules} (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] (F : X.Modules) [F.IsQuasicoherent] :
    ∃ (U : X.Opens)
      (one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U))
      (r : ∀ (n m : ℕ), n ≤ m →
        ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1)),
      (∀ x : X, x ∈ U ↔ Function.Surjective
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom) ∧
      (∀ n : ℕ, Mono (idealSheafPower ι n).2) ∧
      (∀ (n : ℕ) (W : X.Opens), W ≤ U →
        Function.Bijective ((idealSheafPower ι n).2.app W)) ∧
      (∀ n : ℕ, (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U))) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2) ∧
      (∃ (D : ℕ ⥤ AddCommGrpCat.{u})
        (e : ∀ n : ℕ, D.obj n ≅ AddCommGrpCat.of ((idealSheafPower ι n).1 ⟶ F))
        (c : D ⟶ (Functor.const ℕ).obj Γ(F, U)),
        (∀ (n m : ℕ) (h : n ≤ m) (φ : (idealSheafPower ι n).1 ⟶ F),
          (e m).hom (D.map (homOfLE h) ((e n).inv φ)) = r n m h ≫ φ) ∧
        (∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ F),
          c.app n ((e n).inv φ) = φ.app U (one n)) ∧
        Function.Injective (colimit.desc D ⟨Γ(F, U), c⟩)) ∧
      (QuasiSeparatedSpace X →
        ∃ (A : ℕ → X.Modules) (a : ∀ n : ℕ, A n ⟶ F),
          (∀ n : ℕ, Mono (a n)) ∧
          (∀ (n : ℕ) (W : X.Opens) (s : Γ(F, W)),
            s ∈ Set.range ((a n).app W) ↔
              ∀ (W' : X.Opens) (h : W' ≤ W)
                (b : Γ((idealSheafPower ι n).1, W')),
                (F.smul (U := W') ((idealSheafPower ι n).2.val.app (op W') b)).asHom.hom
                  (F.presheaf.map (homOfLE h).op s) = 0) ∧
          (∀ (n m : ℕ), n ≤ m → ∃ t : A n ⟶ A m, t ≫ a m = a n) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U → Subsingleton Γ(A n, W)) ∧
          (∀ n : ℕ,
            IsIso ((SheafOfModules.overFunctor X.ringCatSheaf U).map (cokernel.π (a n)))) ∧
          (∀ (n : ℕ) (W : X.Opens), W ≤ U →
            Function.Bijective ((cokernel.π (a n)).app W)) ∧
          ∃ (q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)))
            (D' : ℕ ⥤ AddCommGrpCat.{u})
            (e' : ∀ n : ℕ, D'.obj n ≅
              AddCommGrpCat.of ((idealSheafPower ι n).1 ⟶ cokernel (a n)))
            (c' : D' ⟶ (Functor.const ℕ).obj Γ(F, U)),
            (∀ (n m : ℕ) (h : n ≤ m), cokernel.π (a n) ≫ q n m h = cokernel.π (a m)) ∧
            (∀ (n m : ℕ) (h : n ≤ m)
              (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
              (e' m).hom (D'.map (homOfLE h) ((e' n).inv φ)) = r n m h ≫ φ ≫ q n m h) ∧
            (∀ (n : ℕ) (φ : (idealSheafPower ι n).1 ⟶ cokernel (a n)),
              (cokernel.π (a n)).app U (c'.app n ((e' n).inv φ)) = φ.app U (one n)) ∧
            Function.Bijective (colimit.desc D' ⟨Γ(F, U), c'⟩)) := by
  classical
  obtain ⟨U, hU, hbij⟩ := ideal_power_complement ι
  have hm := power_mono ι
  let r : ∀ (n m : ℕ), n ≤ m →
      ((idealSheafPower ι m).1 ⟶ (idealSheafPower ι n).1) :=
    fun n m h ↦ (power_factor ι h).choose
  have hr (n m : ℕ) (h : n ≤ m) :
      r n m h ≫ (idealSheafPower ι n).2 = (idealSheafPower ι m).2 :=
    (power_factor ι h).choose_spec
  let one : ∀ n : ℕ, Γ((idealSheafPower ι n).1, U) :=
    fun n ↦ ((hbij n U le_rfl).2 (1 : Γ(X, U))).choose
  have hone (n : ℕ) : (idealSheafPower ι n).2.app U (one n) = (1 : Γ(X, U)) :=
    ((hbij n U le_rfl).2 (1 : Γ(X, U))).choose_spec
  have rid (n : ℕ) : r n n le_rfl = 𝟙 _ := by
    let := hm n
    apply (cancel_mono (idealSheafPower ι n).2).1
    rw [hr n n le_rfl, Category.id_comp]
  have rcomp (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k) :
      r m k h' ≫ r n m h = r n k (h.trans h') := by
    let := hm n
    apply (cancel_mono (idealSheafPower ι n).2).1
    rw [Category.assoc, hr n m h, hr m k h', hr n k (h.trans h')]
  have hrone (n m : ℕ) (h : n ≤ m) : (r n m h).app U (one m) = one n := by
    apply (hbij n U le_rfl).1
    have hh := congrArg (fun f ↦ f.app U (one m)) (hr n m h)
    simpa only [Modules.Hom.comp_app, ConcreteCategory.comp_apply, hone] using hh
  let P : ℕ → X.Modules := fun n ↦ (idealSheafPower ι n).1
  let D : ℕ ⥤ AddCommGrpCat.{u} := homDiagram P (fun _ ↦ F) r
    (fun _ _ _ ↦ 𝟙 F) rid (fun _ ↦ rfl) rcomp (by intros; simp)
  let c : D ⟶ (Functor.const ℕ).obj Γ(F, U) :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        { toFun := fun φ ↦ φ.app U (one n)
          map_zero' := by simp
          map_add' := by intros; simp }
      naturality := by
        intro n m f
        ext φ
        change ((r n m (leOfHom f) ≫ φ ≫ 𝟙 F).app U (one m)) =
          φ.app U (one n)
        simp only [Category.comp_id, Modules.Hom.comp_app,
          ConcreteCategory.comp_apply, hrone]
        rfl }
  have hinj : Function.Injective (colimit.desc D ⟨Γ(F, U), c⟩) := by
    apply colimit_eval_injective D Γ(F, U) c
    intro n φ hφ
    obtain ⟨m, h, hh⟩ := ideal_power_evaluation_eventually_zero ι F U one r hU hone hr
      n φ hφ
    refine ⟨m, homOfLE h, ?_⟩
    change r n m h ≫ φ ≫ 𝟙 F = 0
    simpa using hh
  refine ⟨U, one, r, hU, hm, hbij, hone, hr, ?_, ?_⟩
  · refine ⟨D, fun _ ↦ Iso.refl _, c, ?_, ?_, hinj⟩
    · intro n m h φ
      change r n m h ≫ φ ≫ 𝟙 F = r n m h ≫ φ
      simp
    · intro n φ
      rfl
  · intro hqs
    let := hqs
    obtain ⟨A, a, ha, hqc, hann, hinc, hzero, hiso, hquot⟩ :=
      ideal_power_annihilator_system ι F U hbij
    have hkill (n m : ℕ) (h : n ≤ m) : a n ≫ cokernel.π (a m) = 0 := by
      obtain ⟨t, ht⟩ := hinc n m h
      rw [← ht, Category.assoc, cokernel.condition, comp_zero]
    let q : ∀ (n m : ℕ), n ≤ m → (cokernel (a n) ⟶ cokernel (a m)) :=
      fun n m h ↦ cokernel.desc (a n) (cokernel.π (a m)) (hkill n m h)
    have hq (n m : ℕ) (h : n ≤ m) :
        cokernel.π (a n) ≫ q n m h = cokernel.π (a m) :=
      cokernel.π_desc _ _ _
    have qid (n : ℕ) : q n n le_rfl = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (a n))).1
      rw [hq n n le_rfl, Category.comp_id]
    have qcomp (n m k : ℕ) (h : n ≤ m) (h' : m ≤ k) :
        q n m h ≫ q m k h' = q n k (h.trans h') := by
      apply (cancel_epi (cokernel.π (a n))).1
      rw [← Category.assoc, hq n m h, hq m k h', hq n k (h.trans h')]
    let Q : ℕ → X.Modules := fun n ↦ cokernel (a n)
    let D' : ℕ ⥤ AddCommGrpCat.{u} := homDiagram P Q r q rid qid rcomp qcomp
    let v (n : ℕ) : Γ(F, U) ≃ₗ[Γ(X, U)] Γ(cokernel (a n), U) :=
      LinearEquiv.ofBijective ((cokernel.π (a n)).val.app (op U)).hom (hquot n U le_rfl)
    have hv (n : ℕ) (s : Γ(cokernel (a n), U)) :
        (cokernel.π (a n)).app U ((v n).symm s) = s :=
      (v n).apply_symm_apply s
    let c' : D' ⟶ (Functor.const ℕ).obj Γ(F, U) :=
      { app := fun n ↦ AddCommGrpCat.ofHom
          { toFun := fun φ ↦ (v n).symm (φ.app U (one n))
            map_zero' := by simp
            map_add' := by intros; simp }
        naturality := by
          intro n m f
          ext φ
          apply (hquot m U le_rfl).1
          change (cokernel.π (a m)).app U
              ((v m).symm ((r n m (leOfHom f) ≫ φ ≫ q n m (leOfHom f)).app U
                (one m))) =
            (cokernel.π (a m)).app U ((v n).symm (φ.app U (one n)))
          rw [hv]
          have hqq := congrArg (fun g ↦ g.app U ((v n).symm (φ.app U (one n))))
            (hq n m (leOfHom f))
          rw [← hqq]
          simp only [Modules.Hom.comp_app, ConcreteCategory.comp_apply, hrone, hv]
          rfl }
    obtain ⟨hvanish, hlift⟩ := ideal_power_quotient_local_lifting ι F U one r hU hone hr
      A a ha hqc hann hquot q hq
    have hinj' : Function.Injective (colimit.desc D' ⟨Γ(F, U), c'⟩) := by
      apply colimit_eval_injective D' Γ(F, U) c'
      intro n φ hφ
      have heval : φ.app U (one n) = 0 := by
        have hh := congrArg ((cokernel.π (a n)).app U) hφ
        change (cokernel.π (a n)).app U ((v n).symm (φ.app U (one n))) =
          (cokernel.π (a n)).app U 0 at hh
        simpa only [hv, map_zero] using hh
      obtain ⟨m, h, hh⟩ := hvanish n φ heval
      exact ⟨m, homOfLE h, hh⟩
    have hsurj' : Function.Surjective (colimit.desc D' ⟨Γ(F, U), c'⟩) := by
      intro s
      obtain ⟨n, φ, hφ⟩ := hlift s
      refine ⟨colimit.ι D' n φ, ?_⟩
      rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
      change (v n).symm (φ.app U (one n)) = s
      rw [← hφ]
      exact (v n).symm_apply_apply s
    refine ⟨A, a, ha, hann, hinc, hzero, hiso, hquot,
      q, D', fun _ ↦ Iso.refl _, c', hq, ?_, ?_, hinj', hsurj'⟩
    · intro n m h φ
      rfl
    · intro n φ
      exact hv n (φ.app U (one n))

end AlgebraicGeometry.Scheme
