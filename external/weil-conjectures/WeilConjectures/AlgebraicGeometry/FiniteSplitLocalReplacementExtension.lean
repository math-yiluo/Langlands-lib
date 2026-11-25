/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitLocalReplacementStage
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteEtaleSieveCover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementGeometry
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementRelativeCover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementAttachmentStructure
import Mathlib.AlgebraicGeometry.LimitsOver

/-! The constrained finite split replacement construction. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

open SchemeSplitAttachment

attribute [local instance] SchemeSplitAttachment.instHasCoproductsOfShapeEtale_weilConjectures

private theorem pullback_cofan
    {X : Scheme.{u}} {I : Type} [Finite I]
    (W : I → X.Etale) (T : X.Etale) (ι : ∀ i, W i ⟶ T)
    (h : IsColimit (Cofan.mk T ι)) (N : X.Etale) (g : N ⟶ T) :
    Nonempty (IsColimit (Cofan.mk N (fun i ↦ pullback.fst g (ι i)))) := by
  have : FinitaryExtensive X.Etale := by
    have : HasFiniteCoproducts X.Etale := by dsimp [Scheme.Etale]; infer_instance
    have : HasPullbacks X.Etale := by dsimp [Scheme.Etale]; infer_instance
    let F := Scheme.Etale.forget X ⋙ Over.forget X
    have : PreservesColimitsOfShape (Discrete WalkingPair) F := by
      have : PreservesColimitsOfShape (Discrete WalkingPair)
          (MorphismProperty.Over.forget (@Etale : MorphismProperty Scheme) ⊤ X) :=
        inferInstance
      have : PreservesColimitsOfShape (Discrete WalkingPair) (Over.forget X) := inferInstance
      dsimp [F, Scheme.Etale.forget]
      infer_instance
    exact finitaryExtensive_of_preserves_and_reflects_isomorphism F
  have hi : IsIso (Sigma.desc ι) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp ⟨h⟩
  have hs := FinitaryPreExtensive.isIso_sigmaDesc_fst ι g hi
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hs

private theorem finite_cofan_trans
    {C : Type*} [Category* C] {I : Type} [Finite I]
    (W : I → C) (T : C) (ι : ∀ i, W i ⟶ T) (h : IsColimit (Cofan.mk T ι))
    {K : C} (f : T ⟶ K) (R : Sieve K)
    (hW : ∀ i, ∃ (l : ℕ) (Z : Fin l → C) (π : ∀ j, Z j ⟶ W i),
      Nonempty (IsColimit (Cofan.mk (W i) π)) ∧ ∀ j, R (π j ≫ ι i ≫ f)) :
    ∃ (l : ℕ) (Z : Fin l → C) (π : ∀ j, Z j ⟶ T),
      Nonempty (IsColimit (Cofan.mk T π)) ∧ ∀ j, R (π j ≫ f) := by
  classical
  choose l Z π hcol hR using hW
  let J := Σ i : I, Fin (l i)
  let Q (a : J) := Z a.1 a.2
  let ν (a : J) := π a.1 a.2 ≫ ι a.1
  have hh : IsColimit (Cofan.mk T ν) :=
    Cofan.isColimitTrans (Cofan.mk T ι) h π (fun i ↦ (hcol i).some)
  let _ : Fintype J := Fintype.ofFinite J
  let e := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, Q ∘ e, (fun i ↦ ν (e i)),
    ⟨(Cofan.isColimitEquivOfEquiv e (Cofan.mk T ν)) hh⟩, ?_⟩
  intro j
  simpa only [Function.comp_apply, ν, Category.assoc] using hR (e j).1 (e j).2

/-- Source: Stacks, Hypercoverings, 0DAV and 01GJ, with finite choices as in 094K.

Proof: Form the qcqs matching boundary of A and the relative matching covering
into K_(n+1), as in the unconstrained replacement construction. Pull back S_(n+1)
to this covering object. Refine the resulting etale cover by affine opens and use
quasi-compactness of the boundary to select finitely many. Their disjoint union N
is a relative matching cover, with its chosen finite cofan solving S_(n+1).
Attach N to A using the split attachment construction, retaining A below degree n+1.
The top term is N together with copies of the old nondegenerate objects indexed by
proper surjections [n+1] to [q]. For an old nondegenerate object, pull back the
finite solving cofan of A_q along its inclusion into A_q; finite coproducts are
universal in the etale category. Each resulting constituent solves S_q, and the
assumed operator stability sends this solution into S_(n+1) along the degeneracy.
Combine these finite cofans and the chosen one for N to present the whole top
term. Lower cofans are retained via the restriction equality. All new affine
pieces have the finiteness properties required for a replacement stage, and
the boundary cover gives its matching surjectivity.
(auxiliary; not a blueprint node) -/
theorem exists_local_replacement_stage_extension
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K)
    (S : ∀ n : ℕ, Sieve (K.obj (op (SimplexCategory.mk n))))
    (hS : ∀ m, S m ∈ X.smallEtaleTopology _)
    (hstable : ∀ (m l : ℕ) (θ : SimplexCategory.mk l ⟶ SimplexCategory.mk m)
      (T : X.Etale) (g : T ⟶ K.obj (op (SimplexCategory.mk m))),
      S m g → S l (g ≫ K.map θ.op))
    (n : ℕ) (A : FiniteSplitReplacementStage K n) (hA : StageSolves K S A) :
    ∃ B : FiniteSplitReplacementStage K (n + 1),
      B.restrict n (Nat.le_succ n) = A ∧ StageSolves K S B := by
  classical
  obtain ⟨Q⟩ := exists_replacement_boundary A.U
  let : CompactSpace Q.M.left := Q.compact
  obtain ⟨E, b₀, g₀, hb₀, _, hc₀⟩ := exists_finite_relative_boundary_cover K hK A Q
  obtain ⟨N, ν, k, W, ι, hb, hcol, hW, hι⟩ := exists_finite_etale_sieve_cover
    Q.M E b₀ hb₀ ((S (n + 1)).pullback g₀)
    (X.smallEtaleTopology.pullback_stable g₀ (hS (n + 1)))
  let b := ν ≫ b₀
  let g := ν ≫ g₀
  have hcomp (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)) :
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op := by
    simpa only [b, g, Category.assoc] using congrArg (fun t ↦ ν ≫ t) (hc₀ Δ θ)
  obtain ⟨U, hU, hr⟩ := exists_attached_split_structure A.U N Q b hb
    ⟨k, W, ι, hcol, hW⟩
  let B : FiniteSplitReplacementStage K (n + 1) :=
    ⟨U, eqToHom hU ≫ attachedRefinement A N Q b g hcomp⟩
  have he : B.restrict n (Nat.le_succ n) = A := by
    have stage_ext {A B : FiniteSplitReplacementStage K n} (h : A.U = B.U)
        (hf : A.f = eqToHom (congrArg TruncatedFiniteSplitEtaleHypercover.simplicial h) ≫
          B.f) : A = B := by
      cases A with
      | mk AU Af =>
        cases B with
        | mk BU Bf =>
          cases h
          simp only [eqToHom_refl, Category.id_comp] at hf
          cases hf
          rfl
    apply stage_ext hr
    change (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).map
      (eqToHom hU ≫ attachedRefinement A N Q b g hcomp) = _
    rw [Functor.map_comp, eqToHom_map, attachedRefinement_restrict]
    simp only [eqToHom_trans_assoc]
  refine ⟨B, he, ?_⟩
  intro q
  by_cases hq : q.val < n + 1
  · have hh : StageSolves K S (B.restrict n (Nat.le_succ n)) := he.symm ▸ hA
    exact hh ⟨q.val, hq⟩
  · have hq' : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; have := q.isLt; omega)
    subst q
    let J : Type := PUnit ⊕ Labels n (n + 1)
    let Z : J → X.Etale := Sum.elim (fun _ : PUnit ↦ N) (fun a : Labels n (n + 1) ↦ A.U.N a.1)
    let ζ : ∀ a : J, Z a ⟶ attachedFamily A.U N := fun a ↦ match a with
      | .inl _ => coprod.inl
      | .inr a => oldInclusion A.U N a
    have hζ : IsColimit (Cofan.mk (attachedFamily A.U N) ζ) := by
      refine Cofan.IsColimit.mk _ (fun s ↦
        coprod.desc (X := N) (Y := ∐ (fun a : Labels n (n + 1) ↦ A.U.N a.1))
          (s.inj (.inl PUnit.unit)) (Sigma.desc (fun a ↦ s.inj (.inr a)))) ?_ ?_
      · intro s a
        cases a with
        | inl x => cases x; simp [ζ, Z]
        | inr a => simp [ζ, oldInclusion, Category.assoc]
      · intro s f hf
        apply coprod.hom_ext
        · simpa [ζ, Z] using hf (.inl PUnit.unit)
        · apply Sigma.hom_ext
          intro a
          simpa [ζ, oldInclusion, Category.assoc] using hf (.inr a)
    have hZ (a : J) : ∃ (l : ℕ) (T : Fin l → X.Etale) (π : ∀ i, T i ⟶ Z a),
        Nonempty (IsColimit (Cofan.mk (Z a) π)) ∧
          ∀ i, S (n + 1) (π i ≫ ζ a ≫ topRefinement A N g) := by
      cases a with
      | inl x =>
        refine ⟨k, W, ι, hcol, ?_⟩
        intro i
        have hh := hι i
        change S (n + 1) ((ι i ≫ ν) ≫ g₀) at hh
        change S (n + 1) (ι i ≫ (coprod.inl : N ⟶ attachedFamily A.U N) ≫
          topRefinement A N g)
        rw [topRefinement, coprod.inl_desc]
        simpa only [g, Category.assoc] using hh
      | inr a =>
        obtain ⟨l, T, π, ⟨hp⟩, hπ⟩ := hA a.1
        let inc := A.U.inclusion a.1
        let P (i : Fin l) := pullback inc (π i)
        let τ (i : Fin l) : P i ⟶ A.U.N a.1 := pullback.fst inc (π i)
        refine ⟨l, P, τ, pullback_cofan T _ π hp _ inc, ?_⟩
        intro i
        have hh := (S a.1.val).downward_closed (hπ i) (pullback.snd inc (π i))
        have ht := hstable a.1.val (n + 1) a.2.val (P i)
          (pullback.snd inc (π i) ≫ π i ≫ A.f.app (op (degree a.1)))
          (by simpa only [Category.assoc] using hh)
        simpa [τ, ζ, oldInclusion, topRefinement, Category.assoc,
          ← pullback.condition_assoc] using ht
    obtain ⟨l, T, π, ⟨hp⟩, hπ⟩ := finite_cofan_trans Z (attachedFamily A.U N) ζ
      hζ (topRefinement A N g) (S (n + 1)) hZ
    let Δ : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
      op ⟨SimplexCategory.mk (n + 1), le_rfl⟩
    have ht : U.simplicial.obj Δ = attachedFamily A.U N := by
      rw [hU]
      simp [Δ, attachedSimplicial, attachmentTerm]
    let π' (i : Fin l) : T i ⟶ U.simplicial.obj Δ := π i ≫ eqToHom ht.symm
    have hp' : IsColimit (Cofan.mk (U.simplicial.obj Δ) π') :=
      hp.ofIsoColimit (Cofan.ext (eqToIso ht).symm (fun i ↦ by simp [π']))
    refine ⟨l, T, π', ⟨hp'⟩, ?_⟩
    intro i
    have hf : eqToHom ht.symm ≫ B.f.app Δ = topRefinement A N g := by
      simp [B, NatTrans.comp_app, Δ, attachedRefinement, refinementComponent,
        attachmentTerm]
    change S (n + 1) ((π i ≫ eqToHom ht.symm) ≫ B.f.app Δ)
    rw [Category.assoc, hf]
    exact hπ i

end AlgebraicGeometry.FiniteSplitEtaleHypercover
