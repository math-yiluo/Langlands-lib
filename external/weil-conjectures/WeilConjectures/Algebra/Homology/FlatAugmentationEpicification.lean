/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
import WeilConjectures.Algebra.Homology.FlatCoverFunctor
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!
# Making a bounded flat augmentation termwise epic using identity disks

Source: Stacks Project, Derived Categories, Lemma 06XX, contractible-disk step.
(blueprint: lem-pc-flat-augmentation-epicification).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

private theorem flat_of_iso
    {M N : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (e : M ≅ N) (h : SheafOfModules.IsFlat M) : SheafOfModules.IsFlat N := by
  let := SheafOfModules.monoidalCategory R
  exact (exactFunctor _ _).prop_of_iso
    ((MonoidalCategory.tensoringRight _).mapIso e) h

private theorem flat_biprod
    {M N : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (hM : SheafOfModules.IsFlat M) (hN : SheafOfModules.IsFlat N) :
    SheafOfModules.IsFlat (M ⊞ N) := by
  let f : ULift.{u} WalkingPair → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    fun j ↦ (Limits.pair M N).obj ⟨j.down⟩
  have hf : SheafOfModules.IsFlat (∐ f) :=
    SheafOfModules.isFlat_coproduct R f (fun ⟨j⟩ ↦ by cases j <;> assumption)
  let g : WalkingPair → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    fun j ↦ (Limits.pair M N).obj ⟨j⟩
  apply flat_of_iso _ hf
  exact (Sigma.whiskerEquiv (f := f) (g := g) Equiv.ulift (fun _ ↦ Iso.refl _)) ≪≫
    (HasColimit.isoOfNatIso (Discrete.natIso fun _ ↦ Iso.refl _) : ∐ g ≅ M ⨿ N) ≪≫
    (biprod.isoCoprod M N).symm

private theorem flat_zero : SheafOfModules.IsFlat
    (HasZeroObject.zero.choose : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  obtain ⟨⟨h⟩, _⟩ := SheafOfModules.tensorClosed R
  let := h
  exact (ObjectProperty.flat_of_isZero (isZero_zero _)).2

/-- Adding bounded-above flat identity disks makes any augmentation to a
bounded-above complex epic without changing the source up to quasi-isomorphism.

Source: Stacks Project, Derived Categories, Lemma 06XX, final contractible-disk
addition (https://stacks.math.columbia.edu/tag/06XX), applied in every degree.
(blueprint: lem-pc-flat-augmentation-epicification).

Proof: Choose a bound N for H. In each degree i <= N choose a flat epic cover
p_i : P_i -> H^i using a flat cover; put P_i = 0 for i > N. Construct the direct
sum D of identity disks on P_i in degrees i,i+1. Explicitly D^j is the finite
sum P_j plus P_(j-1), its differential sends the first summand identically to
the second summand in degree j+1 and kills the second. This complex has a
contracting homotopy sending the second summand to the first in degree j-1.
The maps p_i and p_i >> d_H assemble to a chain map a : D -> H. Each component
is epic, since its restriction to P_i is p_i when i <= N, and H^i is zero
otherwise. Set F = E plus D, let s be the first inclusion, and g = [f,a].
Then s >> g = f strictly, g is termwise epic, and s is a homotopy equivalence
because D is contractible, hence a quasi-isomorphism. The terms of F are finite
sums of flat objects, including zero terms, so are flat. Both E and D are
bounded above; D vanishes above N+1. Thus F is bounded above. No assumption on
the cohomology or the components of f is used. Zero H allows D = 0; arbitrary
bounds and negative N are covered by the same construction. -/
theorem exists_boundedAbove_flat_epicification
    (E H : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : E ⟶ H)
    (hE : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i))
    (hH : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (H.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (E.X i)) :
    ∃ (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (s : E ⟶ F) (g : F ⟶ H),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (F.X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlat (F.X i)) ∧ QuasiIso s ∧
      (∀ i : ℤ, Epi (g.f i)) ∧ s ≫ g = f := by
  classical
  obtain ⟨N, hN⟩ := hH
  obtain ⟨T, π, hT⟩ := SheafOfModules.exists_functorial_flat_cover J R
  choose Q p hQ hp using fun M ↦ (⟨T.obj M, π.app M, hT M⟩ :
    ∃ (P : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (p : P ⟶ M), SheafOfModules.IsFlat P ∧ Epi p)
  let P : ℤ → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    fun i ↦ if i ≤ N then Q (H.X i) else HasZeroObject.zero.choose
  have hP (i : ℤ) : SheafOfModules.IsFlat (P i) := by
    dsimp [P]
    split_ifs
    · exact hQ _
    · exact flat_zero
  have hzP (i : ℤ) (hi : N < i) : IsZero (P i) := by
    dsimp [P]
    rw [ite_eq_right (not_le.mpr hi)]
    exact HasZeroObject.zero.choose_spec
  let q (i : ℤ) : P i ⟶ H.X i :=
    if hi : i ≤ N then eqToHom (by simp [P, hi]) ≫ p (H.X i) else 0
  have hq (i : ℤ) : Epi (q i) := by
    by_cases hi : i ≤ N
    · dsimp only [q]
      rw [dite_eq_left hi]
      have := hp (H.X i)
      infer_instance
    · exact (hN i (lt_of_not_ge hi)).epi _
  let X (i : ℤ) := P i ⊞ P (i - 1)
  let dd (i j : ℤ) : X i ⟶ X j :=
    if hij : i + 1 = j then
      biprod.fst ≫ eqToHom (by congr 1; omega) ≫ biprod.inr
    else 0
  let D : CochainComplex _ ℤ :=
    { X := X
      d := dd
      shape := fun i j hij ↦ dite_eq_right hij
      d_comp_d' := by
        intro i j k hij hjk
        change i + 1 = j at hij
        change j + 1 = k at hjk
        simp [dd, hij, hjk, Category.assoc] }
  let a : D ⟶ H := CochainComplex.ofHom
    (fun i ↦ biprod.desc (q i) (q (i - 1) ≫ H.d (i - 1) i)) (by
      intro i
      have hi : i + 1 - 1 = i := by omega
      apply biprod.hom_ext'
      · simp only [D, dd, dite_eq_left rfl, Category.assoc,
          biprod.inl_fst_assoc, biprod.inr_desc]
        simpa using (eqToHom_naturality
          (fun k ↦ q k ≫ H.d k (i + 1)) hi.symm)
      · simp [D, dd, Category.assoc])
  have ha (i : ℤ) : Epi (a.f i) := by
    have := hq i
    exact epi_of_epi_fac (by simp [a] :
      (biprod.inl : P i ⟶ X i) ≫ a.f i = q i)
  let hh (i j : ℤ) : D.X i ⟶ D.X j :=
    if hij : j + 1 = i then
      biprod.snd ≫ eqToHom (by congr 1; omega) ≫ biprod.inl
    else 0
  have hcontract : Homotopy (𝟙 D) 0 := by
    refine { hom := hh, zero := ?_, comm := ?_ }
    · intro i j hij
      exact dite_eq_right hij
    · intro i
      rw [dNext_eq hh (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
        prevD_eq hh (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)]
      have hi' : i - 1 + 1 = i := by omega
      simp only [D, dd, hh, dite_eq_left rfl, dite_eq_left hi', HomologicalComplex.id_f,
        HomologicalComplex.zero_f, Category.assoc, biprod.inr_snd_assoc,
        biprod.inl_fst_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        add_zero]
      exact (biprod.total (X := P i) (Y := P (i - 1))).symm
  have hDbound : ∀ i : ℤ, N + 1 < i → IsZero (D.X i) := by
    intro i hi
    exact (biprod_isZero_iff _ _).2 ⟨hzP i (by omega), hzP (i - 1) (by omega)⟩
  let F := E ⊞ D
  let s : E ⟶ F := biprod.inl
  let g : F ⟶ H := biprod.desc f a
  let e : HomotopyEquiv E F :=
    { hom := s
      inv := biprod.fst
      homotopyHomInvId := Homotopy.ofEq (by simp [s])
      homotopyInvHomId := by
        let h₁ := (hcontract.compRight (biprod.inr : D ⟶ F)).compLeft
          (biprod.snd : F ⟶ D)
        let h₂ := (Homotopy.refl (biprod.fst ≫ s)).add h₁
        exact (Homotopy.ofEq (by simp [s])).trans
          (h₂.symm.trans (Homotopy.ofEq (by
            simpa only [s, Category.id_comp] using biprod.total (X := E) (Y := D)))) }
  refine ⟨F, s, g, ?_, ?_, e.quasiIso_hom, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hE
    refine ⟨max b (N + 1), fun i hi ↦ ?_⟩
    apply IsZero.of_iso _ (HomologicalComplex.biprodXIso E D i)
    exact (biprod_isZero_iff _ _).2
      ⟨hb i (lt_of_le_of_lt (le_max_left _ _) hi),
        hDbound i (lt_of_le_of_lt (le_max_right _ _) hi)⟩
  · intro i
    exact flat_of_iso (HomologicalComplex.biprodXIso E D i).symm
      (flat_biprod (hflat i) (flat_biprod (hP i) (hP (i - 1))))
  · intro i
    have := ha i
    exact epi_of_epi_fac (HomologicalComplex.biprod_inr_desc_f f a i)
  · simp [s, g]

end CochainComplex
