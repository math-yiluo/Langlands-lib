/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.SingleHomology

/-! # Assembling finitely many single-degree maps

Source: the finite-sum assembly in the proof of clopen rank-stratum formality.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

private theorem projection_homology_isIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : CochainComplex C ℤ) (hd : ∀ a b, P.d a b = 0) (n : ℤ) :
    IsIso ((homologyFunctor C n).map
      (Q.map (HomologicalComplex.mkHomToSingle (𝟙 (P.X n))
        (fun a _ => by rw [hd, zero_comp])))) := by
  let p := HomologicalComplex.mkHomToSingle (𝟙 (P.X n))
    (fun a _ => by rw [hd, zero_comp])
  have hp : IsIso (p.f n) := by
    dsimp [p]
    rw [HomologicalComplex.mkHomToSingle_f, Category.id_comp]
    infer_instance
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map p
  let γ := ShortComplex.LeftHomologyMapData.ofZeros φ
    (hd _ _) (hd _ _) (by simp [HomologicalComplex.single])
    (by simp [HomologicalComplex.single])
  have : ShortComplex.QuasiIso φ := γ.quasiIso_iff.mpr (by
    change IsIso (p.f n)
    exact hp)
  have : IsIso (HomologicalComplex.homologyMap p n) := by
    change IsIso (ShortComplex.homologyMap φ)
    infer_instance
  exact (NatIso.isIso_map_iff (homologyFunctorFactors C n) p).mpr this

/-- Maps from the single terms of a finite zero-differential complex assemble
into a derived isomorphism if each map induces an isomorphism in its own degree
and the target has no homology outside the finite support.

Source: finite-sum assembly, step 3 of clopen rank-stratum formality; Stacks,
Derived Categories, Tag 05RU (quasi-isomorphisms inverted).
(blueprint: lem-sc-finite-zero-differential-assembly)

Proof: Project the complex onto each single term. Compose these projections
in the derived category with the given maps and sum over the finite support.
In degree n every summand except the n-th has zero homology, since its
intermediate single complex has zero homology there. The n-th projection
induces an isomorphism: both differentials are zero and its degree-n component
is the identity. Thus the sum induces an isomorphism in every supported degree.
Outside the support its source and target homology are both zero. Homology
functors jointly detect isomorphisms in the derived category. -/
theorem finiteZeroDifferentialAssembly
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (P : CochainComplex C ℤ) (hd : ∀ a b, P.d a b = 0)
    (s : Finset ℤ) (hP : ∀ n, n ∉ s → IsZero (P.X n))
    (K : DerivedCategory C)
    (hK : ∀ n, n ∉ s → IsZero ((homologyFunctor C n).obj K))
    (hlift : ∀ n, n ∈ s → ∃ f : Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj (P.X n)) ⟶ K,
      IsIso ((homologyFunctor C n).map f)) :
    Nonempty (Q.obj P ≅ K) := by
  classical
  let p (n : ℤ) := HomologicalComplex.mkHomToSingle (𝟙 (P.X n))
    (fun a _ => by rw [hd, zero_comp])
  let f (n : ℤ) : Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj (P.X n)) ⟶ K :=
    if hn : n ∈ s then (hlift n hn).choose else 0
  have hf (n : ℤ) (hn : n ∈ s) : IsIso ((homologyFunctor C n).map (f n)) := by
    dsimp [f]
    rw [dite_eq_left hn]
    exact (hlift n hn).choose_spec
  let g : Q.obj P ⟶ K := ∑ n ∈ s, Q.map (p n) ≫ f n
  have hg : IsIso g := (isIso_iff C g).mpr (by
    intro n
    by_cases hn : n ∈ s
    · have hsum : (homologyFunctor C n).map g =
          (homologyFunctor C n).map (Q.map (p n)) ≫
            (homologyFunctor C n).map (f n) := by
        dsimp [g]
        rw [Functor.map_sum]
        simp only [Functor.map_comp]
        apply Finset.sum_eq_single n
        · intro m hm hmn
          have hz : IsZero ((homologyFunctor C n).obj (Q.obj
              ((HomologicalComplex.single C (ComplexShape.up ℤ) m).obj (P.X m)))) :=
            (HomologicalComplex.isZero_single_obj_homology
              (ComplexShape.up ℤ) m (P.X m) n (Ne.symm hmn)).of_iso
                ((homologyFunctorFactors C n).app _)
          rw [hz.eq_of_src ((homologyFunctor C n).map (f m)) 0, comp_zero]
        · exact fun h => (h hn).elim
      rw [hsum]
      have := projection_homology_isIso P hd n
      have := hf n hn
      infer_instance
    · have hz : IsZero ((homologyFunctor C n).obj (Q.obj P)) :=
        (HomologicalComplex.ExactAt.of_isZero (hP n hn)).isZero_homology.of_iso
          ((homologyFunctorFactors C n).app P)
      exact isIso_of_source_target_iso_zero _ hz.isoZero (hK n hn).isoZero)
  exact ⟨asIso g⟩

end DerivedCategory
