/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SemiRepresentableObject

public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.EtaleHypercoverHomotopyEqualizer
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverExistence
import WeilConjectures.AlgebraicGeometry.FiniteSplitHypercoverReplacement
import WeilConjectures.AlgebraicGeometry.SemiRepresentableHypercoverEtale
import WeilConjectures.AlgebraicGeometry.EtaleHypercoverProduct
import WeilConjectures.AlgebraicGeometry.FiniteSplitLocalReplacementZero
import WeilConjectures.AlgebraicGeometry.FiniteSplitLocalReplacementExtension
import WeilConjectures.AlgebraicGeometry.FiniteSplitLocalReplacementAssembly

/-!
# Blueprint statements

corollary-cohomology-pro-etale-affine.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Blueprint: corollary-cohomology-pro-etale-affine. -/
theorem exists_and_cofiltered (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    Nonempty (FiniteSplitEtaleHypercover X) ∧
      (∀ U V : FiniteSplitEtaleHypercover X,
        ∃ W : FiniteSplitEtaleHypercover X, Nonempty (W.Refinement U) ∧
          Nonempty (W.Refinement V)) ∧
      (∀ (U V : FiniteSplitEtaleHypercover X) (a b : U.Refinement V),
        ∃ (W : FiniteSplitEtaleHypercover X) (c : W.Refinement U),
          isRefinementHomotopic (c ≫ a) (c ≫ b)) := by
  have hypercover (U : FiniteSplitEtaleHypercover X) : IsEtaleHypercover U.simplicial := by
    intro n
    exact ⟨U.matching n, U.projection n, U.matchingMap n,
      U.projection_naturality n, U.matching_universal n,
      U.matchingMap_projection n, U.matching_cover n⟩
  refine ⟨exists_finite_split_hypercover X, ?_, ?_⟩
  · intro U V
    obtain ⟨W, ⟨c⟩⟩ := exists_finite_split_replacement (U.simplicial ⨯ V.simplicial)
      (isEtaleHypercover_prod X U.simplicial V.simplicial (hypercover U) (hypercover V))
    exact ⟨W, ⟨c ≫ prod.fst⟩, ⟨c ≫ prod.snd⟩⟩
  · intro U V a b
    obtain ⟨K, hK, c, ⟨H⟩⟩ := exists_etale_hypercover_homotopy_equalizer U V a b
    obtain ⟨W, ⟨d⟩⟩ := exists_finite_split_replacement K hK
    refine ⟨W, d ≫ c, Relation.EqvGen.rel _ _ ?_⟩
    exact ⟨by simpa only [Category.assoc] using H.precomp d⟩

/-- Blueprint: corollary-cohomology-pro-etale-affine. -/
theorem exists_refinement_solving_local_requirements
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (U : FiniteSplitEtaleHypercover X) (r k : ℕ) (degree : Fin k → Fin (r + 1))
    (R : ∀ j : Fin k, Sieve (U.simplicial.obj (op (SimplexCategory.mk (degree j).val))))
    (hR : ∀ j, R j ∈ X.smallEtaleTopology
      (U.simplicial.obj (op (SimplexCategory.mk (degree j).val)))) :
    ∃ (V : FiniteSplitEtaleHypercover X) (f : V.Refinement U),
      ∀ n : Fin (r + 1), ∃ (l : ℕ) (T : Fin l → X.Etale)
        (ι : ∀ i, T i ⟶ V.simplicial.obj (op (SimplexCategory.mk n.val))),
        Nonempty (IsColimit (Cofan.mk (V.simplicial.obj (op (SimplexCategory.mk n.val))) ι)) ∧
          ∀ (j : Fin k) (h : degree j = n) (i : Fin l),
            R j (ι i ≫ f.app (op (SimplexCategory.mk n.val)) ≫
              eqToHom (congrArg (fun m : Fin (r + 1) ↦
                U.simplicial.obj (op (SimplexCategory.mk m.val))) h.symm)) := by
  classical
  let D (n : ℕ) := Σ j : Fin k,
    (SimplexCategory.mk (degree j).val ⟶ SimplexCategory.mk n)
  let F (n : ℕ) (a : D n) := (R a.1).pullback (U.simplicial.map a.2.op)
  let S (n : ℕ) : Sieve (U.simplicial.obj (op (SimplexCategory.mk n))) :=
    { arrows := fun _ g ↦ ∀ a : D n, F n a g
      downward_closed := by
        intro T T' g hg f a
        exact (F n a).downward_closed (hg a) f }
  have hS (n : ℕ) : S n ∈ X.smallEtaleTopology _ := by
    have : Finite (D n) := by dsimp [D]; infer_instance
    let _ : Fintype (D n) := Fintype.ofFinite _
    apply X.smallEtaleTopology.superset_covering
      (S := Finset.univ.inf (F n))
    · intro T g hg a
      exact (Finset.inf_le (Finset.mem_univ a) :
        Finset.univ.inf (F n) ≤ F n a) g hg
    · exact Finset.inf_induction (X.smallEtaleTopology.top_mem _)
        (fun _ h₁ _ h₂ ↦ X.smallEtaleTopology.intersection_covering h₁ h₂)
        (fun a _ ↦ X.smallEtaleTopology.pullback_stable _ (hR a.1))
  have hstable (m l : ℕ) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
      (T : X.Etale) (g : T ⟶ U.simplicial.obj (op (SimplexCategory.mk m)))
      (hg : S m g) : S l (g ≫ U.simplicial.map θ.op) := by
    intro a
    have hh := hg ⟨a.1, a.2 ≫ θ⟩
    change R a.1 (g ≫ U.simplicial.map (a.2 ≫ θ).op) at hh
    change R a.1 ((g ≫ U.simplicial.map θ.op) ≫ U.simplicial.map a.2.op)
    simpa only [op_comp, Functor.map_comp, Category.assoc] using hh
  have hU : IsEtaleHypercover U.simplicial := by
    intro n
    exact ⟨U.matching n, U.projection n, U.matchingMap n,
      U.projection_naturality n, U.matching_universal n,
      U.matchingMap_projection n, U.matching_cover n⟩
  let L (n : ℕ) := {A : FiniteSplitReplacementStage U.simplicial n //
    StageSolves U.simplicial S A}
  obtain ⟨A₀, hA₀⟩ := exists_local_replacement_stage_zero U.simplicial hU S (hS 0)
  have hstep (n : ℕ) (A : L n) :
      ∃ B : L (n + 1), B.val.restrict n (Nat.le_succ n) = A.val := by
    obtain ⟨B, he, hB⟩ := exists_local_replacement_stage_extension
      U.simplicial hU S hS hstable n A.val A.property
    exact ⟨⟨B, hB⟩, he⟩
  choose next hnext using hstep
  let A : ∀ n, L n := Nat.rec ⟨A₀, hA₀⟩ (fun n B ↦ next n B)
  obtain ⟨V, f, hV⟩ := exists_local_replacement_of_stage_tower U.simplicial
    (fun n ↦ (A n).val) (fun n ↦ hnext n (A n)) S (fun n ↦ (A n).property)
  refine ⟨V, f, ?_⟩
  intro n
  obtain ⟨l, T, ι, hc, hι⟩ := hV n.val
  refine ⟨l, T, ι, hc, ?_⟩
  intro j h i
  subst n
  have hh := hι i ⟨j, 𝟙 _⟩
  change R j ((ι i ≫ f.app _) ≫ U.simplicial.map (𝟙 _).op) at hh
  change R j ((ι i ≫ f.app _) ≫ U.simplicial.map (𝟙 _)) at hh
  rw [U.simplicial.map_id, Category.comp_id] at hh
  simpa only [eqToHom_refl, Category.comp_id] using hh

/-- Blueprint: corollary-cohomology-pro-etale-affine. -/
theorem exists_truncated_refinement
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale)
    (hK : X.IsSemiRepresentableHypercover
      (K ⋙ FormalCoproduct.incl.{u} X.Etale)) (r : ℕ) :
    ∃ V : FiniteSplitEtaleHypercover X,
      Nonempty ((SimplicialObject.truncation r).obj V.simplicial ⟶
          (SimplicialObject.truncation r).obj K) := by
  have hK' : IsEtaleHypercover K :=
    AlgebraicGeometry.Scheme.semiRepresentableHypercover_isEtaleHypercover K hK
  obtain ⟨V, ⟨f⟩⟩ := exists_finite_split_replacement K hK'
  exact ⟨V, ⟨(SimplicialObject.truncation r).map f⟩⟩


end AlgebraicGeometry.FiniteSplitEtaleHypercover
