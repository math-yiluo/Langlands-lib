/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Exact Hom and K-flat dual computations for a strictly perfect local complex

Source: Stacks Project, Tag 08DQ, proof of lemma-dual-perfect-complex;
Tag 08DM, the bounded Hom calculation.
(blueprint: lem-pc-strictly-perfect-local-hom-computations).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace

open scoped ZeroObject

namespace AlgebraicGeometry

private theorem shortExact_of_retract {C : Type*} [Category C] [Abelian C]
    {S T : ShortComplex C} (h : Retract S T) (hT : T.ShortExact) : S.ShortExact := by
  have hH := h.map (ShortComplex.homologyFunctor C)
  have hz : IsZero T.homology := T.exact_iff_isZero_homology.mp hT.exact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply S.exact_iff_isZero_homology.mpr
    rw [IsZero.iff_id_eq_zero]
    change 𝟙 ((ShortComplex.homologyFunctor C).obj S) = 0
    rw [← hH.retract]
    rw [hz.eq_of_src hH.r 0, comp_zero]
  · exact (MorphismProperty.monomorphisms C).of_retract
      (h.map ShortComplex.fFunctor) hT.mono_f
  · exact (MorphismProperty.epimorphisms C).of_retract
      (h.map ShortComplex.gFunctor) hT.epi_g

private theorem exact_homObj_of_finiteFree_retract {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    (A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hA : ∃ m : ℕ,
      ∃ (i : A ⟶ SheafOfModules.free
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m)))
        (p : SheafOfModules.free
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m)) ⟶ A),
        i ≫ p = 𝟙 A)
    (S : ShortComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 A) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 A) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 A) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 A) S.g) hz).ShortExact := by
  obtain ⟨m, i, p, hip⟩ := hA
  let B := SheafOfModules.free
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (ULift.{u} (Fin m))
  obtain ⟨hzB, hB, _⟩ := SheafOfModules.finiteFreeInternalHomExact
    (R := R) m B (Iso.refl _) S hS
  have hzA : SheafOfModules.homObjMap (R := R) (𝟙 A) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 A) S.g = 0 := by
    rw [SheafOfModules.homObjMap_comp_homObjMap (R := R) (𝟙 A) (𝟙 A) S.f S.g,
      Category.id_comp, S.zero]
    apply SheafOfModules.hom_ext
    ext V φ : 3
    rfl
  let T := ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 A) S.f)
    (SheafOfModules.homObjMap (R := R) (𝟙 A) S.g) hzA
  let TB := ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 B) S.f)
    (SheafOfModules.homObjMap (R := R) (𝟙 B) S.g) hzB
  let inc : T ⟶ TB :=
    ShortComplex.homMk
      (SheafOfModules.homObjMap (R := R) p (𝟙 S.X₁))
      (SheafOfModules.homObjMap (R := R) p (𝟙 S.X₂))
      (SheafOfModules.homObjMap (R := R) p (𝟙 S.X₃))
      (by simp [T, TB, SheafOfModules.homObjMap_comp_homObjMap])
      (by simp [T, TB, SheafOfModules.homObjMap_comp_homObjMap])
  let ret : TB ⟶ T :=
    ShortComplex.homMk
      (SheafOfModules.homObjMap (R := R) i (𝟙 S.X₁))
      (SheafOfModules.homObjMap (R := R) i (𝟙 S.X₂))
      (SheafOfModules.homObjMap (R := R) i (𝟙 S.X₃))
      (by simp [T, TB, SheafOfModules.homObjMap_comp_homObjMap])
      (by simp [T, TB, SheafOfModules.homObjMap_comp_homObjMap])
  refine ⟨hzA, shortExact_of_retract (T := TB) ⟨inc, ret, ?_⟩ hB⟩
  ext <;> simp [inc, ret, T, SheafOfModules.homObjMap_comp_homObjMap, hip,
    SheafOfModules.homObjMap_id]


/-- Internal Hom from P preserves quasi-isomorphisms, and its actual ordinary dual
is K-flat. Neither assertion involves a derived evaluation map.
Source: Stacks Project, Tag 08DM, bounded Hom calculation, and Tag 08DQ,
proof of lemma-dual-perfect-complex, termwise evaluation.
(blueprint: lem-pc-strictly-perfect-local-hom-computations).

Proof: internal Hom from each term of P is a retract of internal Hom from a
finite free module. Precomposition with its projection and inclusion gives a
retraction of the associated short complexes. Finite free internal Hom is exact;
short exactness descends along this retraction. Apply the bounded exact-term Hom
quasi-isomorphism theorem to obtain the first assertion.
For an acyclic F, apply that assertion to the quasi-isomorphism 0 -> F.
Hom(P,0) is zero in each degree by its product universal property, so Hom(P,F)
is acyclic. Construct ordinary evaluation from the recorded degree maps and their
differential identity. It is invertible in each degree for strictly perfect P,
hence is an isomorphism of complexes. Transport the acyclicity of Hom(P,F) through
its inverse to obtain acyclicity of Tot(F tensor Hom(P,O[0])). This is exactly
K-flatness of the dual. This argument avoids a second proof of flatness of its
terms, and allows unbounded F, zero P, rank zero, reversed bounds and empty U.
-/
theorem strictlyPerfect_localHom_computations (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ)
    (hstrict : Scheme.IsStrictlyPerfect X U P) :
    (∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t)) ∧
      (localEvaluationDual X U P).IsKFlatTensor := by
  classical
  have hhom : ∀ (M M' : CochainComplex (localEvaluationModules X U) ℤ) (t : M ⟶ M'),
      QuasiIso t → QuasiIso (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map t) := by
    intro M M' t ht
    have := ht
    apply quasiIso_homComplex_map_of_bounded_exact_terms
      ((Opens.grothendieckTopology X).over U) (X.sheaf.over U) P hstrict.1
    intro n S hS
    exact exact_homObj_of_finiteFree_retract (X.sheaf.over U) (P.X n) (hstrict.2 n) S hS
  refine ⟨hhom, ?_⟩
  intro F hF
  let Z : CochainComplex (localEvaluationModules X U) ℤ := 0
  have hZ : (homComplex (R := X.sheaf.over U) P Z).Acyclic := by
    intro n
    apply HomologicalComplex.ExactAt.of_isZero
    rw [IsZero.iff_id_eq_zero]
    apply Fan.IsLimit.hom_ext (Classical.choice
      (homComplexProductLimit_exists (X.sheaf.over U) P Z n))
    intro r
    have hz : IsZero (Z.X (r + n)) :=
      (HomologicalComplex.eval _ (.up ℤ) (r + n)).map_isZero (isZero_zero _)
    have hH : IsZero (SheafOfModules.homObj (R := X.sheaf.over U)
        (P.X r) (Z.X (r + n))) := by
      rw [IsZero.iff_id_eq_zero]
      apply (SheafOfModules.tensorHomEquiv (R := X.sheaf.over U) (P.X r) _ _).symm.injective
      exact hz.eq_of_tgt _ _
    exact hH.eq_of_tgt _ _
  have ht : QuasiIso (0 : Z ⟶ F) :=
    (quasiIso_iff_acyclic (0 : Z ⟶ F)
      (HomologicalComplex.acyclic_of_isZero Z (isZero_zero _))).2 hF
  let z := ((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map (0 : Z ⟶ F)
  have hz : QuasiIso z := hhom Z F 0 ht
  have hHom : (homComplex (R := X.sheaf.over U) P F).Acyclic :=
    (quasiIso_iff_acyclic z hZ).1 hz
  let f : localEvaluationTensor X U P F ⟶ homComplex (R := X.sheaf.over U) P F :=
    { f := localEvaluationDegreeMap X U P F
      comm' := fun n m h ↦ localEvaluationDegreeMap_comm X U P F n m h }
  have hf : IsLocalOrdinaryEvaluation X U P F f := by
    intro p q n r hpq
    exact localEvaluationDegreeMap_formula X U P F p q n r hpq
  have : ∀ n : ℤ, IsIso (f.f n) :=
    fun n ↦ isIso_localOrdinaryEvaluation_degree X U P F hstrict f hf n
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  change (localEvaluationTensor X U P F).Acyclic
  intro n
  exact (hHom n).of_iso (asIso f).symm

end AlgebraicGeometry
