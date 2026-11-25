/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits

import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Injectivity of one minus shift on a sequential coproduct

Source: Stacks Project, Derived Categories, Lemma 093W, used in Lemma 0949.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The sum of the transition maps into a fixed term, extended by zero on later terms.
Source: Stacks Project, Tag 093W, the transition-map sum in its proof
(blueprint: lem-pc-telescope-shift-mono). -/
private noncomputable def telescopeProjection
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts.{0} A]
    (E : ℕ ⥤ A) (j : ℕ) : (∐ fun n : ℕ ↦ E.obj n) ⟶ E.obj j :=
  Sigma.desc fun k ↦ if h : k ≤ j then E.map (homOfLE h) else 0

/-- The transition-map sum cancels consecutive transitions, leaving a single diagonal entry.
Source: Stacks Project, Tag 093W, the finite short exact sequence in its proof
(blueprint: lem-pc-telescope-shift-mono). -/
private lemma telescopeProjection_formula
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts.{0} A]
    (E : ℕ ⥤ A) (j k : ℕ) :
    (Sigma.ι (fun n : ℕ ↦ E.obj n) k -
      E.map (homOfLE (Nat.le_succ k)) ≫
        Sigma.ι (fun n : ℕ ↦ E.obj n) (k + 1)) ≫ telescopeProjection E j =
      if h : k = j then eqToHom (congrArg E.obj h) else 0 := by
  classical
  simp only [telescopeProjection, Preadditive.sub_comp, Category.assoc, Sigma.ι_comp_desc]
  by_cases h : k = j
  · subst j
    simp
  · by_cases hkj : k ≤ j
    · have hsj : k + 1 ≤ j := by omega
      simp only [dite_eq_left hkj, dite_eq_left hsj, dite_eq_right h]
      rw [← E.map_comp]
      simp
    · have hsj : ¬ k + 1 ≤ j := by omega
      simp [hkj, hsj, h]

/-- Restrict one minus shift to each finite subcoproduct, give an explicit retraction,
then take the exact filtered colimit of these monomorphisms into the constant target.
Source: Stacks Project, Tag 093W, proof by finite sums and exact colimits
(blueprint: lem-pc-telescope-shift-mono). -/
private lemma sequentialCoproduct_mono
    {A : Type*} [Category A] [Preadditive A] [HasCoproducts.{0} A]
    [HasColimitsOfShape (Finset (Discrete ℕ)) A]
    [HasExactColimitsOfShape (Finset (Discrete ℕ)) A]
    (E : ℕ ⥤ A) :
    Mono (Sigma.desc (fun n : ℕ ↦
      Sigma.ι (fun n : ℕ ↦ E.obj n) n -
        E.map (homOfLE (Nat.le_succ n)) ≫
          Sigma.ι (fun n : ℕ ↦ E.obj n) (n + 1))) := by
  classical
  have : IsConnected (Finset (Discrete ℕ)) := IsFiltered.isConnected _
  let u := Sigma.desc (fun n : ℕ ↦
    Sigma.ι (fun n : ℕ ↦ E.obj n) n -
      E.map (homOfLE (Nat.le_succ n)) ≫
        Sigma.ι (fun n : ℕ ↦ E.obj n) (n + 1))
  let F := CoproductsFromFiniteFiltered.liftToFinsetObj (Discrete.functor E.obj)
  let c := CoproductsFromFiniteFiltered.finiteSubcoproductsCocone (fun n ↦ E.obj n)
  let φ : F ⟶ (Functor.const (Finset (Discrete ℕ))).obj (∐ fun n ↦ E.obj n) :=
    c.ι ≫ (Functor.const _).map u
  have hφ (S : Finset (Discrete ℕ)) : Mono (φ.app S) := by
    let r : (∐ fun n ↦ E.obj n) ⟶ F.obj S :=
      ∑ j : S, telescopeProjection E j.1.as ≫ Sigma.ι (fun k : S ↦ E.obj k.1.as) j
    have hr : φ.app S ≫ r = 𝟙 _ := by
      apply Sigma.hom_ext
      intro k
      dsimp [φ, c, F, CoproductsFromFiniteFiltered.finiteSubcoproductsCocone,
        CoproductsFromFiniteFiltered.liftToFinsetObj, r]
      simp only [u, Sigma.ι_comp_desc, Preadditive.comp_sum,
        ← Category.assoc, telescopeProjection_formula]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk
        have hne : k.1.as ≠ j.1.as := by
          intro h
          apply hjk
          apply Subtype.ext
          exact Discrete.ext h.symm
        simp [hne]
      · simp
    exact (IsSplitMono.mk' ⟨r, hr⟩).mono
  have : Mono φ := NatTrans.mono_of_mono_app φ
  exact colim.map_mono' φ
    (CoproductsFromFiniteFiltered.isColimitFiniteSubproductsCocone (fun n ↦ E.obj n))
    (isColimitConstCocone (Finset (Discrete ℕ)) _) u (by intro j; simp [φ, c])

/-- One minus shift is monic on the coproduct of a sequential system of complexes
of sheaves of modules. Source: Stacks Project, Derived Categories, Lemma 093W,
proof, used in Lemma 0949 (blueprint: lem-pc-telescope-shift-mono).

Proof: For each j, define q_j from the coproduct to E_j by the transition
E_k → E_j when k ≤ j, and zero when k > j. Composing the k-th component of
one minus shift with q_j gives the identity when k = j and zero otherwise:
when k < j, the two terms cancel by functoriality of E.
For a finite set S of indices, the sum of q_j followed by the j-th injection
into the finite subcoproduct, over j in S, retracts the restriction of one
minus shift to that subcoproduct. Thus each finite restriction is split monic,
including S empty. These restrictions form a natural transformation from the
finite-subcoproduct diagram into the constant countable coproduct.
The category of sheaves of modules is Grothendieck abelian by the proved source
library theorem SheafOfModules.isGrothendieckAbelian. Exact filtered colimits
pass to complexes by Mathlib's degreewise evaluation instance. Mathlib also
identifies the colimit of the finite subcoproducts with the countable coproduct.
Applying colim.map_mono' with this colimit cocone and the constant colimit
cocone proves that one minus shift is monic. No transition map is assumed
monic; zero diagrams and zero transitions satisfy the same cancellation. -/
theorem telescopeShift_mono
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (E : ℕ ⥤ CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    Mono (Sigma.desc (fun n : ℕ ↦
      Sigma.ι (fun n : ℕ ↦ E.obj n) n -
        E.map (homOfLE (Nat.le_succ n)) ≫
          Sigma.ι (fun n : ℕ ↦ E.obj n) (n + 1))) := by
  let R' := ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R') :=
    SheafOfModules.isGrothendieckAbelian R'
  have : AB5OfSize.{0, 0} (SheafOfModules.{u} R') :=
    AB5OfSize_of_univLE (SheafOfModules.{u} R')
  exact sequentialCoproduct_mono E

end CochainComplex
