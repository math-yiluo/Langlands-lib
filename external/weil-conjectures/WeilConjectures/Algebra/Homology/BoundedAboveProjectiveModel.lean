/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Bounded-above projective models of derived module objects

Source: Stacks Project, Tags 0645 and 0646, and the downward construction of Tag 05T7
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private theorem quasiIso_unop_reverse
    {D : Type*} [Category* D] [Abelian D]
    {I J : CochainComplex Dᵒᵖ ℤ} (f : I ⟶ J) [QuasiIso f] :
    QuasiIso (((CochainComplex.opEquivalence D).inverse.map f).unop) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have hf := (quasiIsoAt_iff' f (-(n + 1)) (-n) (-(n - 1))
    (by simp; lia) (by simp; lia)).mp inferInstance
  exact ShortComplex.quasiIso_unopMap
    ((HomologicalComplex.shortComplexFunctor' Dᵒᵖ _ (-(n + 1)) (-n) (-(n - 1))).map f)

namespace DerivedCategory

/-- An object with no cohomology above `b` has a projective complex model zero above `b`.
Source: Stacks Project, Tags 0645 and 0646, parts (2) and (3)
(auxiliary; not a blueprint node).

Proof:
1. The standard t-structure supplies a representative K strictly zero above b.
2. ModuleCat A has enough projectives, so its opposite has enough injectives.
   Taking opposites and reversing integer degrees sends K to a complex K' zero below -b.
3. Apply Mathlib's exact-bound injective replacement theorem to K'. This is the unbundled
   version of `lem-sc-bounded-below-injective-resolution-existence`, and gives a
   quasi-isomorphism K' → J with injective terms and J zero below -b.
4. Reverse degrees and take opposites again. The resulting L has projective terms and
   is zero above b. The induced map L → K'' is a quasi-isomorphism: degree n homology
   is the opposite of degree -n homology, checked on the three-term short complexes.
5. The unit of the opposite equivalence identifies K'' with K. Localization inverts the
   quasi-isomorphism, and composing with Q(K) ≅ C gives the required model. -/
theorem exists_boundedAbove_projective_model
    (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{max u v} A)]
    (C : DerivedCategory (ModuleCat.{max u v} A)) (b : ℤ)
    (hC : ∀ i : ℤ, b < i → IsZero ((homologyFunctor (ModuleCat.{max u v} A) i).obj C)) :
    ∃ L : CochainComplex (ModuleCat.{max u v} A) ℤ,
      (∀ i : ℤ, Module.Projective A (L.X i)) ∧
      (∀ i : ℤ, b < i → IsZero (L.X i)) ∧ Nonempty (Q.obj L ≅ C) := by
  have : C.IsLE b := (isLE_iff C b).mpr hC
  obtain ⟨K, hK, ⟨e⟩⟩ := exists_iso_Q_obj_of_isLE C b
  let K' := (CochainComplex.opEquivalence (ModuleCat.{max u v} A)).functor.obj (Opposite.op K)
  have : K'.IsStrictlyGE (-b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE b (-i) (by lia)).op
  obtain ⟨J, f, hf, hJ, hJb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K' (-b)
  let L := ((CochainComplex.opEquivalence (ModuleCat.{max u v} A)).inverse.obj J).unop
  let g := ((CochainComplex.opEquivalence (ModuleCat.{max u v} A)).inverse.map f).unop
  have : QuasiIso g := quasiIso_unop_reverse f
  refine ⟨L, ?_, ?_, ?_⟩
  · intro i
    have : Injective (J.X (-i)) := hJ (-i)
    change Module.Projective A ((J.X (-i)).unop : ModuleCat.{max u v} A)
    infer_instance
  · intro i hi
    change IsZero (J.X (-i)).unop
    exact (J.isZero_of_isStrictlyGE (-b) (-i) (by lia)).unop
  · exact ⟨asIso (Q.map g) ≪≫
      Q.mapIso ((CochainComplex.opEquivalence (ModuleCat.{max u v} A)).unitIso.app
        (Opposite.op K)).unop ≪≫ e.symm⟩

end DerivedCategory
