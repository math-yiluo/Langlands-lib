/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsSiteLimits
public import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation

/-!
# Geometry of the qcqs finite-cover pro-etale subsite

Source: Stacks Project, Tags 09A1, 098M, 098Z, 0F4P, and Hypercoverings Tag 0DB1
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

set_option linter.unusedVariables false in
/-- The qcqs finite-cover subsite has scheme fibre products and slice finite limits.
Finite disjoint unions are qcqs, and affine for affine summands. Representable sheaves
carry these unions to coproducts, and sections of every sheaf carry them to products,
naturally in the sheaf, including the empty family.

Source: Stacks Project, Tags 09A1 (qcqs subsite paragraph), 098M, 098Z, 0F4P,
and Hypercoverings Tag 0DB1
(auxiliary; not a blueprint node).

Proof:
1. Apply lem-weil-pbc-proetale-qcqs-site-limits for the finite-cover site axioms,
   fibre products computed in schemes, preservation of fibre products and covers,
   slice finite limits, and stability under adjoining finitely many arrows.
   The full slice inclusion preserves these limits by the same scheme universal
   properties. Every affine scheme is quasi-compact and quasi-separated.
2. Apply lem-weil-pbc-proetale-subcanonical (Tag 098Z): every representable is a sheaf.
3. Apply lem-weil-pbc-proetale-finite-coproduct-evaluation to each finite qcqs family.
   Its scheme coproduct is qcqs and affine when the summands are affine, hence lies
   in the full qcqs subcategory. The coproduct comparison of representable sheaves
   is an isomorphism. Restriction on sections is bijective, naturally in the sheaf;
   for the empty family its source is the empty scheme and its sections are unique.
4. Combine these conclusions, retaining the common coprojections in the scheme,
   representable-sheaf and section comparisons. -/
theorem qcqs_finite_family_geometry (X : Scheme.{u}) :
    (∀ V : X.ProEt, IsAffine V.left →
      CompactSpace V.left ∧ QuasiSeparatedSpace V.left) ∧
    (∃ h : HasPullbacks (Qcqs X),
      ∃ J : @Pretopology (Qcqs X) inferInstance h,
        J.toPrecoverage = qcqsPrecoverage X ∧
        PreservesLimitsOfShape WalkingCospan (qcqsInclusion X) ∧
        PreservesLimitsOfShape WalkingCospan
          (qcqsInclusion X ⋙ ProEt.forget X ⋙ Over.forget X) ∧
        (∀ (T : Qcqs X) (R : Presieve T), R ∈ qcqsPrecoverage X T →
          R.map (qcqsInclusion X) ∈ precoverage X ((qcqsInclusion X).obj T)) ∧
        (∀ T : Qcqs X, HasFiniteLimits (Over T) ∧
          PreservesFiniteLimits (Over.post (X := T) (qcqsInclusion X)) ∧
          PreservesFiniteLimits
            (Over.post (X := T) (qcqsInclusion X ⋙ ProEt.forget X) ⋙
              Over.iteratedSliceForward ((qcqsInclusion X ⋙ ProEt.forget X).obj T))) ∧
        (∀ (T : Qcqs X) (R S : Presieve T), R ∈ qcqsPrecoverage X T →
          S ∈ Precoverage.finite (Qcqs X) T → R ⊔ S ∈ qcqsPrecoverage X T)) ∧
    (topology X).Subcanonical ∧
    (∀ (I : Type v) [Finite I] (V : I → X.ProEt)
      (hqc : ∀ i, CompactSpace (V i).left)
      (hqs : ∀ i, QuasiSeparatedSpace (V i).left),
      ∃ (W : X.ProEt) (ι : ∀ i, V i ⟶ W)
        (e : (∐ fun i ↦ (V i).left) ≅ W.left),
        (∀ i, Sigma.ι (fun i ↦ (V i).left) i ≫ e.hom = (ι i).left) ∧
        CompactSpace W.left ∧ QuasiSeparatedSpace W.left ∧
        ((∀ i, IsAffine (V i).left) → IsAffine W.left) ∧
        Nonempty (IsColimit (Cofan.mk ((topology X).uliftYoneda.{max (u + 1) w}.obj W)
          (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.map (ι i)))) ∧
        (∀ (c : Cofan (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.obj (V i)))
          (hc : IsColimit c),
          IsIso (hc.desc (Cofan.mk ((topology X).uliftYoneda.{max (u + 1) w}.obj W)
            (fun i ↦ (topology X).uliftYoneda.{max (u + 1) w}.map (ι i))))) ∧
        (∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
          Function.Bijective (fun s : F.obj.obj (op W) ↦
            fun i ↦ F.obj.map (ι i).op s)) ∧
        (∀ (F G : Sheaf (topology X) (Type (max (u + 1) w))) (η : F ⟶ G)
          (s : F.obj.obj (op W)) (i : I),
          G.obj.map (ι i).op (η.hom.app (op W) s) =
            η.hom.app (op (V i)) (F.obj.map (ι i).op s)) ∧
        (IsEmpty I → IsEmpty W.left ∧
          ∀ F : Sheaf (topology X) (Type (max (u + 1) w)),
            Nonempty (Unique (F.obj.obj (op W))))) := by
  refine ⟨?_, ?_, inferInstance, ?_⟩
  · intro V hV
    have := hV
    exact ⟨inferInstance, inferInstance⟩
  · obtain ⟨h, J, hJ, hinc, hsch, hcov, hslice, _hfin, hadd⟩ := qcqs_site_limits X
    refine ⟨h, J, hJ, hinc, hsch, hcov, ?_, hadd⟩
    intro T
    obtain ⟨hT, hpres⟩ := hslice T
    have := hT
    have := hpres
    have : (Over.iteratedSliceForward
        ((qcqsInclusion X ⋙ ProEt.forget X).obj T)).IsEquivalence :=
      inferInstanceAs (Over.iteratedSliceEquiv
        ((qcqsInclusion X ⋙ ProEt.forget X).obj T)).functor.IsEquivalence
    refine ⟨hT, ?_, hpres⟩
    have : PreservesFiniteLimits
        (Over.post (X := T) (qcqsInclusion X) ⋙
          (Over.post (ProEt.forget X) ⋙
            Over.iteratedSliceForward ((qcqsInclusion X ⋙ ProEt.forget X).obj T))) := by
      rw [← Functor.assoc, ← Over.post_comp]
      exact hpres
    exact preservesFiniteLimits_of_reflects_of_preserves
      (Over.post (X := T) (qcqsInclusion X))
      (Over.post (ProEt.forget X) ⋙
        Over.iteratedSliceForward ((qcqsInclusion X ⋙ ProEt.forget X).obj T))
  · intro I _ V hqc hqs
    exact finite_coproduct_evaluation X I V hqc hqs

end AlgebraicGeometry.Scheme.ProEt
