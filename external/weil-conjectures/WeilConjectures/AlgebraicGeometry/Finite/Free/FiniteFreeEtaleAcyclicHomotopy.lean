/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import WeilConjectures.AlgebraicGeometry.FiniteFreeConstantLocalLift
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-! # Local null-homotopies into acyclic etale complexes

Source: Stacks Project, Cohomology on Sites, Tag 08FP, assertion (1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

private structure AboveHomotopy
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} (α : E ⟶ F) (k : ℤ) where
  h : Cochain E F (-1)
  comm : ∀ n : ℤ, k < n →
    α.f n = E.d n (n + 1) ≫ h.v (n + 1) n (by omega) +
      h.v n (n - 1) (by omega) ≫ F.d (n - 1) n

private def AboveHomotopy.map
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {E F : CochainComplex C ℤ} {α : E ⟶ F} {k : ℤ}
    (H : AboveHomotopy α k) (R : C ⥤ D) [R.Additive] :
    AboveHomotopy ((R.mapHomologicalComplex (.up ℤ)).map α) k where
  h := H.h.map R
  comm n hn := by
    change R.map (α.f n) = _
    rw [H.comm n hn, R.map_add, R.map_comp, R.map_comp]
    simp only [Cochain.map_v]
    rfl

private def AboveHomotopy.ofNatIso
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {E F : CochainComplex C ℤ} {α : E ⟶ F} {k : ℤ}
    {R S : C ⥤ D} [R.Additive] [S.Additive] (e : R ≅ S)
    (H : AboveHomotopy ((S.mapHomologicalComplex (.up ℤ)).map α) k) :
    AboveHomotopy ((R.mapHomologicalComplex (.up ℤ)).map α) k where
  h := Cochain.mk (fun n m hnm ↦
    e.hom.app (E.X n) ≫ H.h.v n m hnm ≫ e.inv.app (F.X m))
  comm n hn := by
    simp only [Cochain.mk_v]
    dsimp only [Functor.mapHomologicalComplex] at *
    have heq := H.comm n hn
    dsimp only [Functor.mapHomologicalComplex] at heq
    rw [← cancel_mono (e.hom.app (F.X n))]
    simp only [Preadditive.add_comp, Category.assoc]
    erw [e.hom.naturality (F.d (n - 1) n), e.inv_hom_id_app_assoc,
      e.inv_hom_id_app, Category.comp_id]
    erw [e.hom.naturality_assoc (E.d n (n + 1)), e.hom.naturality (α.f n)]
    rw [heq]
    simp only [Preadditive.comp_add]

private theorem local_lift_from_finiteFree
    {U : Scheme.{u}} {B : Type (u + 1)} [CommRing B]
    {A M N : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (hA : ∃ r : ℕ, Nonempty (A ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B (Fin r → B))))
    (p : M ⟶ N) [Epi p] (a : A ⟶ N) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
      ∃ t : (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).obj A ⟶
          (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).obj M,
        t ≫ (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).map p =
          (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).map a := by
  obtain ⟨r, ⟨e⟩⟩ := hA
  obtain ⟨𝒰, h𝒰⟩ := exists_finiteFreeConstant_local_lift p r (e.inv ≫ a)
  refine ⟨𝒰, fun j ↦ ?_⟩
  obtain ⟨t, ht⟩ := h𝒰 j
  let R := Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)
  let c := (upperStarConstantSheafIso (ModuleCat.{u + 1} B) (𝒰.f j)).app
    (ModuleCat.of B (Fin r → B))
  refine ⟨R.map e.hom ≫ c.hom ≫ t, ?_⟩
  simp only [Category.assoc]
  rw [ht]
  change R.map e.hom ≫ c.hom ≫ c.inv ≫ R.map (e.inv ≫ a) = R.map a
  rw [c.hom_inv_id_assoc, ← R.map_comp, e.hom_inv_id_assoc]

private theorem AboveHomotopy.step
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} {α : E ⟶ F} {k : ℤ}
    (H : AboveHomotopy α k) (t : E.X k ⟶ F.X (k - 1))
    (htd : t ≫ F.d (k - 1) k =
      α.f k - E.d k (k + 1) ≫ H.h.v (k + 1) k (by omega)) :
    Nonempty (AboveHomotopy α (k - 1)) := by
  classical
  let t' := t - H.h.v k (k - 1) (by omega)
  let hm := H.h + Cochain.single (K := E) (L := F) t' (-1)
  refine ⟨{ h := hm, comm := ?_ }⟩
  intro n hn
  by_cases he : n = k
  · subst n
    simp only [hm, Cochain.add_v,
      Cochain.single_v_eq_zero (K := E) (L := F) t' (-1) (k + 1) k (by omega) (by omega),
      add_zero, Cochain.single_v]
    dsimp only [t']
    have ht : H.h.v k (k - 1) (by omega) +
        (t - H.h.v k (k - 1) (by omega)) = t := by abel
    rw [ht, htd]
    abel
  · have hn' : k < n := by omega
    simpa only [hm, Cochain.add_v,
      Cochain.single_v_eq_zero (K := E) (L := F) t' (-1) (n + 1) n (by omega) (by omega),
      Cochain.single_v_eq_zero (K := E) (L := F) t' (-1) n (n - 1) (by omega) he,
      add_zero] using H.comm n hn'

private theorem cochain_comp_d_eq
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} (h : Cochain E F (-1))
    (n m m' p : ℤ) (hm : n - 1 = m) (hm' : n - 1 = m') :
    h.v n m (by omega) ≫ F.d m p = h.v n m' (by omega) ≫ F.d m' p := by
  subst m
  subst m'
  rfl

private theorem above_step
    {U : Scheme.{u}} {B : Type (u + 1)} [CommRing B]
    {E F : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ}
    (hfree : ∀ n : ℤ, ∃ r : ℕ, Nonempty (E.X n ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B (Fin r → B))))
    (hF : F.Acyclic) (α : E ⟶ F) (k : ℤ) (H : AboveHomotopy α k) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
      Nonempty (AboveHomotopy
        (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
          (.up ℤ)).map α) (k - 1)) := by
  classical
  let z := α.f k - E.d k (k + 1) ≫ H.h.v (k + 1) k (by omega)
  have hz : z ≫ F.d k (k + 1) = 0 := by
    dsimp only [z]
    rw [Preadditive.sub_comp, Category.assoc, α.comm k (k + 1)]
    have heq := H.comm (k + 1) (by omega)
    rw [cochain_comp_d_eq H.h (k + 1) (k + 1 - 1) k (k + 1) rfl (by omega)] at heq
    have heq' : H.h.v (k + 1) k (by omega) ≫ F.d k (k + 1) =
        α.f (k + 1) - E.d (k + 1) (k + 1 + 1) ≫ H.h.v (k + 1 + 1) (k + 1) (by omega) := by
      exact eq_sub_iff_add_eq'.mpr heq.symm
    rw [heq', Preadditive.comp_sub, ← Category.assoc, E.d_comp_d, zero_comp, sub_zero,
      sub_self]
  let a := F.liftCycles z (k + 1) (by simp) hz
  have : Epi (F.toCycles (k - 1) k) := (hF k).epi_toCycles _ (by simp)
  obtain ⟨𝒰, h𝒰⟩ := local_lift_from_finiteFree (hfree k) (F.toCycles (k - 1) k) a
  refine ⟨𝒰, fun j ↦ ?_⟩
  obtain ⟨t, ht⟩ := h𝒰 j
  let R := Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)
  have htd : t ≫ R.map (F.d (k - 1) k) = R.map z := by
    rw [← F.toCycles_i (k - 1) k, R.map_comp, ← Category.assoc, ht, ← R.map_comp]
    exact congrArg R.map (F.liftCycles_i z (k + 1) (by simp) hz)
  apply (H.map R).step t
  simpa only [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_map_f,
    AboveHomotopy.map, Cochain.map_v, z, R.map_sub, R.map_comp] using htd

private theorem finiteFree_map
    {U V : Scheme.{u}} {B : Type (u + 1)} [CommRing B] (f : V ⟶ U)
    {E : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ}
    (hfree : ∀ n : ℤ, ∃ r : ℕ, Nonempty (E.X n ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B (Fin r → B)))) :
    ∀ n : ℤ, ∃ r : ℕ, Nonempty
      ((((Etale.upperStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj E).X n ≅
        (constantSheaf V.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
          (ModuleCat.of B (Fin r → B))) := by
  intro n
  obtain ⟨r, ⟨e⟩⟩ := hfree n
  exact ⟨r, ⟨(Etale.upperStar (ModuleCat.{u + 1} B) f).mapIso e ≪≫
    (upperStarConstantSheafIso (ModuleCat.{u + 1} B) f).app _⟩⟩

private theorem above_iterate
    {U : Scheme.{u}} {B : Type (u + 1)} [CommRing B]
    {E F : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ}
    (hfree : ∀ n : ℤ, ∃ r : ℕ, Nonempty (E.X n ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B (Fin r → B))))
    (hF : F.Acyclic) (α : E ⟶ F) (k : ℤ) (H : AboveHomotopy α k) (d : ℕ) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
      Nonempty (AboveHomotopy
        (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
          (.up ℤ)).map α) (k - (d : ℤ))) := by
  classical
  let : etalePrecoverage.IsStableUnderComposition :=
    inferInstanceAs ((precoverage @Etale).IsStableUnderComposition)
  induction d with
  | zero =>
    refine ⟨coverOfIsIso (P := @Etale) (𝟙 U), fun j ↦ ?_⟩
    rw [Nat.cast_zero, sub_zero]
    exact ⟨H.map _⟩
  | succ d ih =>
    obtain ⟨𝒰, h𝒰⟩ := ih
    have hj (j : 𝒰.I₀) := above_step (finiteFree_map (𝒰.f j) hfree)
      (hF.map (Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)))
      (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex (.up ℤ)).map α)
      (k - (d : ℤ)) (h𝒰 j).some
    choose 𝒱 h𝒱 using hj
    refine ⟨𝒰.bind 𝒱, fun j ↦ ?_⟩
    obtain ⟨Hj⟩ := h𝒱 j.1 j.2
    have Hcomp : AboveHomotopy
        ((((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j.1)) ⋙
          (Etale.upperStar (ModuleCat.{u + 1} B) ((𝒱 j.1).f j.2))).mapHomologicalComplex
            (.up ℤ)).map α) (k - (d : ℤ) - 1) := Hj
    have Hres := AboveHomotopy.ofNatIso
      (Etale.upperStarComp (ModuleCat.{u + 1} B) ((𝒱 j.1).f j.2) (𝒰.f j.1)) Hcomp
    have heq : k - ((d + 1 : ℕ) : ℤ) = k - (d : ℤ) - 1 := by omega
    rw [heq]
    exact ⟨Hres⟩

private theorem homotopy_of_above
    {C : Type*} [Category C] [Preadditive C]
    {E F : CochainComplex C ℤ} (α : E ⟶ F) (a : ℤ)
    (hbelow : ∀ n : ℤ, n < a → IsZero (E.X n))
    (H : AboveHomotopy α (a - 1)) : Nonempty (Homotopy α 0) := by
  refine ⟨(Cochain.equivHomotopy α 0).symm ⟨H.h, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  ext n
  rw [δ_v (-1) 0 (by omega) H.h n n (by omega) (n - 1) (n + 1) (by omega) (by omega)]
  by_cases hn : a ≤ n
  · simpa only [Cochain.ofHom_v, Int.negOnePow_zero, one_smul, add_comm] using
      H.comm n (by omega)
  · exact (hbelow n (by omega)).eq_of_src _ _

/-- Maps from a bounded finite free constant complex into an acyclic complex
are null-homotopic on an etale cover.

Source: Stacks Project, sites-cohomology.tex, Tag 08FP, lemma-local-homotopy (1).
(blueprint: lem-weil-pbc-finite-free-etale-acyclic-homotopy).

Proof: choose bounds a,b for P. Descend from b to a, constructing the homotopy
components. Once the equation holds above n, the difference between the n-th
map component and d_P followed by the component already constructed is a cycle
in F^n. Acyclicity says that F^(n-1) maps epimorphically onto these cycles.
Use a finite basis of P^n to lift this cycle map on an etale covering, and take
that lift as the next homotopy component. Refine the preceding covering at each
of the finitely many steps. Below a and above b all equations hold because the
source terms are zero. The resulting components define one homotopy on each
member of the composite cover. Zero ranks require no lifts, and an empty base
admits the empty cover. -/
theorem finiteFree_etale_acyclic_homotopy
    (U : Scheme.{u}) (B : Type (u + 1)) [CommRing B]
    (P : CochainComplex (ModuleCat.{u + 1} B) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (P.X n ≅ ModuleCat.of B (Fin r → B)))
    (F : CochainComplex (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) ℤ)
    (hF : F.Acyclic)
    (α : (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) ⟶ F) :
    ∃ 𝒰 : Cover.{u} etalePrecoverage U, ∀ j : 𝒰.I₀,
      Nonempty (Homotopy
        (((Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map α) 0) := by
  classical
  let E := ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
    (.up ℤ)).obj P
  obtain ⟨a, b, hb⟩ := hbounded
  have hE (n : ℤ) (hn : n < a ∨ b < n) : IsZero (E.X n) :=
    (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).map_isZero (hb n hn)
  have hfree' : ∀ n : ℤ, ∃ r : ℕ, Nonempty (E.X n ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).obj
        (ModuleCat.of B (Fin r → B))) := by
    intro n
    obtain ⟨r, ⟨e⟩⟩ := hfree n
    exact ⟨r, ⟨(constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapIso e⟩⟩
  let H : AboveHomotopy α b :=
    { h := 0
      comm := fun n hn ↦ (hE n (Or.inr hn)).eq_of_src _ _ }
  obtain ⟨𝒰, h𝒰⟩ := above_iterate hfree' hF α b H (b - a + 1).toNat
  refine ⟨𝒰, fun j ↦ ?_⟩
  let R := Etale.upperStar (ModuleCat.{u + 1} B) (𝒰.f j)
  obtain ⟨Hj⟩ := h𝒰 j
  have Hfull : AboveHomotopy ((R.mapHomologicalComplex (.up ℤ)).map α) (a - 1) :=
    { h := Hj.h
      comm := fun n hn ↦ Hj.comm n (by omega) }
  exact homotopy_of_above _ a (fun n hn ↦ R.map_isZero (hE n (Or.inl hn))) Hfull

end AlgebraicGeometry
