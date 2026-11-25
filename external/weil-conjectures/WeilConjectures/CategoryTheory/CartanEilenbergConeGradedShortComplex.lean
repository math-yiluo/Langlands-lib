/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

import WeilConjectures.CategoryTheory.CartanEilenbergConeGradedNormalizedDifferential

/-! # Short-complex comparison for the Cartan--Eilenberg cone filtration

Source: Stacks Project, Homology, Tag 0133, canonical augmentation, and Tag 012X,
column filtration of a total complex. This is the augmented-cone refinement used
in the parent node's second proof step.
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

private theorem normalized_iso_all_degrees
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m : ℤ) :
    ∃ e : (F.gradedPiece p).X m ≅ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p),
      CartanEilenbergConeGradedNormalized K I a aug F p m e := by
  by_cases hm : p - 1 ≤ m
  · exact cartanEilenberg_cone_graded_normalized_iso
      K I a b hIbelow hKbelow aug F hF p m hm
  · have hstep : F.complexStep p m = ⊥ := by
      rw [hF]
      have hpm : ¬ p ≤ m + 1 := by omega
      have hIcc : Finset.Icc (max b p) m = ∅ := by
        apply Finset.Icc_eq_empty
        omega
      simp only [ite_eq_right hpm, hIcc, Finset.sup_empty, bot_sup_eq]
    have hzstep : IsZero ((F.step p : CochainComplex A ℤ).X m) := by
      apply IsZero.of_mono_eq_zero ((F.step p).arrow.f m)
      rw [← imageSubobject_arrow_comp ((F.step p).arrow.f m)]
      change factorThruImageSubobject ((F.step p).arrow.f m) ≫
        (F.complexStep p m).arrow = 0
      have harrow : (F.complexStep p m).arrow = 0 := by
        rw [hstep]
        exact Subobject.bot_arrow
      rw [harrow, comp_zero]
    have : Epi (F.complexQuotientπ p (p + 1) (by omega)) := by
      unfold DecreasingFiltration.complexQuotientπ
      infer_instance
    have hzgraded : IsZero ((F.gradedPiece p).X m) :=
      IsZero.of_epi ((F.complexQuotientπ p (p + 1) (by omega)).f m) hzstep
    have hzcolumn : IsZero ((CochainComplex.mappingCone
        (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p)) := by
      rw [CochainComplex.mappingCone.isZero_X_iff]
      constructor
      · apply HomologicalComplex.isZero_extend_X
        intro r
        change (r : ℤ) ≠ m - p + 1
        omega
      · apply HomologicalComplex.isZero_extend_X
        intro r
        change (r : ℤ) ≠ m - p
        omega
    refine ⟨hzgraded.iso hzcolumn, ?_⟩
    constructor
    · intro r hr
      omega
    · intro h
      omega

/-- The three terms and two differentials of a graded cone are those of its column cone.
Source: Stacks Project, Homology, Tags 0133 and 012X; augmented-cone refinement
of the parent filtration-properties node, proof step 2.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-short-complex-iso).

Proof: fix p and a total degree m. The cone object is the biproduct of K^(m+1)
and the diagonal coproduct of the extended bicomplex. The formula hF presents
step p as the sum of precisely the summands of complex index at least p.
Projection onto complex index p annihilates step p+1. Its restriction to step p
therefore descends to the degree-m cokernel of the successive-step inclusion;
evaluation on cochain complexes preserves this cokernel. Inclusion of the index-p
summands into step p followed by its cokernel projection is inverse to this
map. On the retained summand one composite is the identity. To check the other,
cancel the epic cokernel projection and check on the generating summands of
step p: the index-p summand gives the identity, and each larger-index summand
factors through step p+1 and is killed by the cokernel projection. These are
jointly generating because step p is their finite image supremum.

The retained object is the index-(m-p) object of the column mapping cone: its
K^p summand occurs exactly at m=p-1, and its I-column summand at m>=p. Identify
the former using the extension of the single complex at resolution degree zero,
and the latter using extendXIso. For p<b both are zero by hKbelow and hIbelow;
for m<p-1 both are zero by extension by zero. Thus the same construction works
for empty intervals, zero columns, and every integer p and m.

Perform this construction in the three degrees m=n-1,n,n+1. The cone differential
on K is -d_K, whose image has complex index p+1 and vanishes in the quotient.
The horizontal bicomplex differential also raises complex index and vanishes.
The resolution differential preserves complex index. Since the bicomplex is
flipped, it is the first total differential and has coefficient one. Finally,
on K^p in degree p-1 the off-diagonal differential is aug.f p; haug identifies
its retained component with the extension of (a.f p).f 0. All other components
of the extended single complex are zero. Consequently the two squares commute
with exactly the differentials of the column cone at degrees n-p-1,n-p,n-p+1.
The three degreewise isomorphisms and these two squares define the short-complex
isomorphism. No exactness or quasi-isomorphism assumption is used. -/
theorem cartanEilenberg_cone_graded_shortComplex_iso
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p n : ℤ) :
    Nonempty ((F.gradedPiece p).sc n ≅
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).sc (n - p)) := by
  let D := CochainComplex.mappingCone
    (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)
  let G := F.gradedPiece p
  obtain ⟨e₁, he₁⟩ := normalized_iso_all_degrees
    K I a b hIbelow hKbelow aug F hF p (n - 1)
  obtain ⟨e₂, he₂⟩ := normalized_iso_all_degrees
    K I a b hIbelow hKbelow aug F hF p n
  obtain ⟨e₃, he₃⟩ := normalized_iso_all_degrees
    K I a b hIbelow hKbelow aug F hF p (n + 1)
  have h₁₂ : e₁.inv ≫ G.d (n - 1) n = D.d (n - 1 - p) (n - p) ≫ e₂.inv :=
    cartanEilenberg_cone_graded_normalized_differential
      K I a b hIbelow hKbelow aug haug F hF p (n - 1) n (by omega) e₁ e₂ he₁ he₂
  have h₂₃ : e₂.inv ≫ G.d n (n + 1) = D.d (n - p) (n + 1 - p) ≫ e₃.inv :=
    cartanEilenberg_cone_graded_normalized_differential
      K I a b hIbelow hKbelow aug haug F hF p n (n + 1) rfl e₂ e₃ he₂ he₃
  let E : D.sc' (n - 1 - p) (n - p) (n + 1 - p) ≅ G.sc' (n - 1) n (n + 1) :=
    ShortComplex.isoMk e₁.symm e₂.symm e₃.symm h₁₂ h₂₃
  have hprev : (ComplexShape.up ℤ).prev n = n - 1 := by
    apply ComplexShape.prev_eq'
    change n - 1 + 1 = n
    omega
  have hnext : (ComplexShape.up ℤ).next n = n + 1 := by
    apply ComplexShape.next_eq'
    rfl
  have hprev' : (ComplexShape.up ℤ).prev (n - p) = n - 1 - p := by
    apply ComplexShape.prev_eq'
    change n - 1 - p + 1 = n - p
    omega
  have hnext' : (ComplexShape.up ℤ).next (n - p) = n + 1 - p := by
    apply ComplexShape.next_eq'
    change n - p + 1 = n + 1 - p
    omega
  exact ⟨(G.isoSc' (n - 1) n (n + 1) hprev hnext).trans
    (E.symm.trans (D.isoSc' (n - 1 - p) (n - p) (n + 1 - p) hprev' hnext').symm)⟩

end CategoryTheory.Functor
