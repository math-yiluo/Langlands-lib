/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SiteHypercoverFiniteExtensionBase

/-! # Explicit operators for split simplicial attachment

Source: Stacks Project, Tag 0DAV (lemma-hypercovering-object), construction of the
extension and the final simplicial composition check; Tag 0DAU (lemma-split).
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FormalSplitAttachment

variable {D : Type u} [Category.{v} D] {n : ℕ}

/-- The inverse normalization component for a given old index. Source: Stacks 0DAU.
(auxiliary; not a blueprint node) -/
noncomputable def denormalize
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (q : Fin (n + 1)) (i : (term K q).I) :
    (term K q).obj i ⟶ (term K (normalization K hs q i).1).obj
      (normalization K hs q i).2.2.val := by
  let a := normalization K hs q i
  have he : labelIndex K q a = i :=
    (Equiv.ofBijective (labelIndex K q) (hs.1 q)).apply_symm_apply i
  have : IsIso ((operator K a.2.1.val).φ a.2.2.val) := hs.2 q a
  exact eqToHom (congrArg (term K q).obj he.symm) ≫ inv ((operator K a.2.1.val).φ a.2.2.val)

/-- The normalization isomorphism from the labeled old family to its actual term.
Source: Stacks 0DAU. (auxiliary; not a blueprint node) -/
noncomputable def normalizationIso
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (q : Fin (n + 1)) :
    (⟨Labels K q.val, fun a ↦ (term K a.1).obj a.2.2.val⟩ : FormalCoproduct.{w} D) ≅
      term K q :=
  FormalCoproduct.isoOfComponents (Equiv.ofBijective (labelIndex K q) (hs.1 q))
    (fun a ↦ by have := hs.2 q a; exact asIso ((operator K a.2.1.val).φ a.2.2.val))

/-- Concatenating an epi on normalized labels, with identity components.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
def normalizedEpi
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    (⟨Labels K q.val, fun a ↦ (term K a.1).obj a.2.2.val⟩ : FormalCoproduct.{w} D) ⟶
      attachedFamily K V where
  f a := Sum.inr (precomposeLabel K a σ hσ)
  φ _ := 𝟙 _

/-- Concatenation of an old epi on normalized families. Source: Stacks 0DAU.
(auxiliary; not a blueprint node) -/
def normalizedOldEpi
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (q r : Fin (n + 1))
    (θ : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) (hθ : Epi θ) :
    (⟨Labels K q.val, fun a ↦ (term K a.1).obj a.2.2.val⟩ : FormalCoproduct.{w} D) ⟶
      ⟨Labels K r.val, fun a ↦ (term K a.1).obj a.2.2.val⟩ where
  f a := precomposeLabel K a θ hθ
  φ _ := 𝟙 _

/-- Old normalization is natural for epimorphisms. Source: Stacks 0DAU.
(auxiliary; not a blueprint node) -/
theorem normalizationIso_epi
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (q r : Fin (n + 1))
    (θ : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) (hθ : Epi θ) :
    (normalizationIso K hs q).hom ≫ operator K θ =
      normalizedOldEpi K q r θ hθ ≫ (normalizationIso K hs r).hom := by
  refine (FormalCoproduct.hom_ext_iff' _ _).mpr ?_
  intro a
  have hc : operator K a.2.1.val ≫ operator K θ =
      operator K (θ ≫ a.2.1.val) := by
    dsimp [operator]
    rw [← K.map_comp]
    rfl
  simpa [normalizationIso, normalizedOldEpi, precomposeLabel,
    FormalCoproduct.isoOfComponents, labelIndex] using
    (FormalCoproduct.hom_ext_iff' _ _).mp hc a.2.2.val

/-- A degeneracy into the newly attached degree. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
noncomputable def attachEpi
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    term K q ⟶ attachedFamily K V where
  f i := Sum.inr (precomposeLabel K (normalization K hs q i) σ hσ)
  φ i := denormalize K hs q i

/-- The explicit degeneracy is inverse normalization followed by label concatenation.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
theorem attachEpi_eq
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    attachEpi K hs V q σ hσ = (normalizationIso K hs q).inv ≫ normalizedEpi K V q σ hσ := by
  refine FormalCoproduct.hom_ext rfl ?_
  intro i
  simp [attachEpi, normalizationIso, normalizedEpi, denormalize, normalization]

/-- Top degeneracies commute with every old epimorphism. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachEpi_oldEpi
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q r : Fin (n + 1))
    (θ : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) (hθ : Epi θ)
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hσ : Epi σ) :
    operator K θ ≫ attachEpi K hs V r σ hσ =
      attachEpi K hs V q (σ ≫ θ) (epi_comp σ θ) := by
  have hn : normalizedOldEpi K q r θ hθ ≫ normalizedEpi K V r σ hσ =
      normalizedEpi K V q (σ ≫ θ) (epi_comp σ θ) := by
    refine FormalCoproduct.hom_ext rfl ?_
    intro a
    simp [normalizedOldEpi, normalizedEpi]
  apply (cancel_epi (normalizationIso K hs q).hom).mp
  rw [← Category.assoc, normalizationIso_epi K hs q r θ hθ]
  simp only [Category.assoc, attachEpi_eq, Iso.hom_inv_id_assoc]
  exact hn

/-- The lower faces of the attached family, on its two kinds of summands.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
def attachFace
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) :
    attachedFamily K V ⟶ term K q where
  f := Sum.elim (p.projection q α).f
    (fun a ↦ (operator K (α ≫ a.2.1.val)).f a.2.2.val)
  φ := fun z ↦ match z with
    | Sum.inl j => (p.projection q α).φ j
    | Sum.inr a => (operator K (α ≫ a.2.1.val)).φ a.2.2.val

/-- Faces of the attached family form a compatible boundary cone. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachFace_naturality
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q r : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachFace K V p r β ≫ operator K α = attachFace K V p q (α ≫ β) := by
  have hc (a : Labels K (n + 1)) :
      operator K (β ≫ a.2.1.val) ≫ operator K α =
        operator K ((α ≫ β) ≫ a.2.1.val) := by
    dsimp [operator]
    rw [← K.map_comp]
    rfl
  refine (FormalCoproduct.hom_ext_iff' _ _).mpr ?_
  intro z
  cases z with
  | inl j =>
    have hp := congrArg (fun f ↦ f.f j) (p.naturality q r α β)
    refine ⟨hp, ?_⟩
    have hp' := (FormalCoproduct.hom_ext_iff' _ _).mp (p.naturality q r α β) j
    simpa [attachFace] using hp'.2
  | inr a =>
    have hh := (FormalCoproduct.hom_ext_iff' _ _).mp (hc a) a.2.2.val
    simpa [attachFace] using hh

/-- A new degeneracy followed by an old face is the old composite operator.
Source: Stacks 0DAV, simplicial composition check.
(auxiliary; not a blueprint node) -/
theorem attachEpi_face
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q r : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ)
    (α : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEpi K hs V q σ hσ ≫ attachFace K V p r α = operator K (α ≫ σ) := by
  have hn : normalizedEpi K V q σ hσ ≫ attachFace K V p r α =
      (normalizationIso K hs q).hom ≫ operator K (α ≫ σ) := by
    have hc (a : Labels K q.val) :
        operator K a.2.1.val ≫ operator K (α ≫ σ) =
          operator K (α ≫ (σ ≫ a.2.1.val)) := by
      dsimp [operator]
      rw [← K.map_comp]
      rfl
    refine (FormalCoproduct.hom_ext_iff' _ _).mpr ?_
    intro a
    simpa [normalizedEpi, attachFace, precomposeLabel, normalizationIso,
      FormalCoproduct.isoOfComponents, labelIndex] using
      (FormalCoproduct.hom_ext_iff' _ _).mp (hc a).symm a.2.2.val
  rw [attachEpi_eq, Category.assoc, hn]
  simp

/-- An arbitrary map from the top ordinal to an old ordinal, using its image.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
noncomputable def attachLift
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) :
    term K q ⟶ attachedFamily K V :=
  let r : Fin (n + 1) := ⟨(image α).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι α)) q.isLt⟩
  operator K (q := r) (image.ι α) ≫
    attachEpi K hs V r (factorThruImage α) inferInstance

/-- The lifting operator can use any epi-mono factorization. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachLift_factor_mono
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val)
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) (hι : Mono ι)
    (hfac : ρ ≫ ι = α) :
    attachLift K hs V q α = operator K ι ≫ attachEpi K hs V r ρ hρ := by
  have : StrongEpi ρ := strongEpi_of_epi ρ
  let u := image.isoStrongEpiMono ρ ι hfac
  let t : Fin (n + 1) := ⟨(image α).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι α)) q.isLt⟩
  have h1 : operator K ι = operator K (q := t) (r := q) (image.ι α) ≫
      operator K (q := r) (r := t) u.hom := by
    dsimp [operator]
    rw [← K.map_comp]
    change K.map _ = K.map (SimplexCategory.Truncated.Hom.tr (u.hom ≫ image.ι α) _ _).op
    rw [image.isoStrongEpiMono_hom_comp_ι]
  have h2 : ρ ≫ u.hom = factorThruImage α := by
    apply (cancel_mono (image.ι α)).mp
    simp [Category.assoc, u, hfac]
  rw [h1, Category.assoc, attachEpi_oldEpi K hs V t r u.hom inferInstance ρ hρ]
  simp only [h2]
  rfl

/-- A lift can use an epi followed by any old map. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachLift_factor
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q r : Fin (n + 1))
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) :
    attachLift K hs V q (ρ ≫ ι) = operator K ι ≫ attachEpi K hs V r ρ hρ := by
  let t : Fin (n + 1) := ⟨(image ι).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι ι)) q.isLt⟩
  rw [attachLift_factor_mono K hs V q t (ρ ≫ ι) (ρ ≫ factorThruImage ι)
    (epi_comp _ _) (image.ι ι) inferInstance (by rw [Category.assoc, image.fac])]
  rw [← attachEpi_oldEpi K hs V t r (factorThruImage ι) inferInstance ρ hρ,
    ← Category.assoc]
  congr 1
  dsimp [operator]
  rw [← K.map_comp]
  change K.map (SimplexCategory.Truncated.Hom.tr
    (factorThruImage ι ≫ image.ι ι) _ _).op = _
  rw [image.fac]

/-- Lifts commute with all old operators. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachLift_naturality
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) :
    attachLift K hs V q (α ≫ β) = operator K β ≫ attachLift K hs V r α := by
  let t : Fin (n + 1) := ⟨(image α).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι α)) r.isLt⟩
  have hf : α ≫ β = factorThruImage α ≫ (image.ι α ≫ β) := by
    rw [← Category.assoc, image.fac]
  rw [hf, attachLift_factor K hs V q t (factorThruImage α) inferInstance]
  have hc : operator K (q := t) (r := q) (image.ι α ≫ β) =
      operator K β ≫ operator K (q := t) (r := r) (image.ι α) := by
    dsimp [operator]
    rw [← K.map_comp]
    rfl
  rw [hc, Category.assoc]
  rfl

/-- In the epi case no image factorization remains. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachLift_epi
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    attachLift K hs V q σ = attachEpi K hs V q σ hσ := by
  rw [attachLift_factor_mono K hs V q q σ σ hσ (𝟙 _) inferInstance (Category.comp_id σ)]
  have hi : operator K (q := q) (r := q) (𝟙 _) = 𝟙 _ := K.map_id _
  rw [hi, Category.id_comp]

/-- The same face relation for every map from the top ordinal to an old ordinal.
Source: Stacks 0DAV, image-factorization composition check.
(auxiliary; not a blueprint node) -/
theorem attachLift_face
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q r : Fin (n + 1))
    (β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val)
    (α : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachLift K hs V q β ≫ attachFace K V p r α = operator K (α ≫ β) := by
  unfold attachLift
  dsimp only
  rw [Category.assoc, attachEpi_face]
  dsimp [operator]
  rw [← K.map_comp]
  change K.map (SimplexCategory.Truncated.Hom.tr
    ((α ≫ factorThruImage β) ≫ image.ι β) _ _).op = _
  rw [Category.assoc, image.fac]

/-- An endomorphism of the top family: the identity, or a proper image factorization.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
noncomputable def attachEnd
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V)
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1)) :
    attachedFamily K V ⟶ attachedFamily K V := by
  classical
  exact if hα : Epi α then 𝟙 _ else
    let hr : (image α).len < n + 1 := by
      have hle := SimplexCategory.len_le_of_mono (image.ι α)
      have hne : image α ≠ SimplexCategory.mk (n + 1) := by
        intro he
        have hi : IsIso (image.ι α) :=
          (SimplexCategory.isIso_iff_of_mono (image.ι α)).mpr (congrArg SimplexCategory.len he)
        have : Epi (factorThruImage α ≫ image.ι α) := epi_comp _ _
        rw [image.fac] at this
        exact hα this
      exact SimplexCategory.len_lt_of_mono (image.ι α) (Ne.symm hne)
    let r : Fin (n + 1) := ⟨(image α).len, hr⟩
    attachFace K V p r (image.ι α) ≫
      attachEpi K hs V r (factorThruImage α) inferInstance

/-- A nonidentity top endomorphism can use any epi-mono factorization.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
theorem attachEnd_factor_mono
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1))
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) (hι : Mono ι)
    (hfac : ρ ≫ ι = α) :
    attachEnd K hs V p α = attachFace K V p r ι ≫ attachEpi K hs V r ρ hρ := by
  classical
  have hα : ¬ Epi α := by
    intro hα
    have : Epi (ρ ≫ ι) := hfac.symm ▸ hα
    have : Epi ι := epi_of_epi ρ ι
    have hh := SimplexCategory.len_le_of_epi ι
    have hr := r.isLt
    dsimp at hh
    omega
  have : StrongEpi ρ := strongEpi_of_epi ρ
  let u := image.isoStrongEpiMono ρ ι hfac
  have ht : (image α).len < n + 1 :=
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono u.inv) r.isLt
  let t : Fin (n + 1) := ⟨(image α).len, ht⟩
  have h1 : attachFace K V p r ι = attachFace K V p t (image.ι α) ≫
      operator K (q := r) (r := t) u.hom := by
    rw [attachFace_naturality]
    congr 1
    exact (image.isoStrongEpiMono_hom_comp_ι ρ ι hfac).symm
  have h2 : ρ ≫ u.hom = factorThruImage α := by
    apply (cancel_mono (image.ι α)).mp
    simp [Category.assoc, u, hfac]
  rw [h1, Category.assoc, attachEpi_oldEpi K hs V t r u.hom inferInstance ρ hρ]
  simp only [h2, attachEnd, dite_eq_right hα]
  rfl

/-- The top endomorphism can use an epi followed by any proper old-degree map.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
theorem attachEnd_factor
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (r : Fin (n + 1))
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd K hs V p (ρ ≫ ι) = attachFace K V p r ι ≫ attachEpi K hs V r ρ hρ := by
  let t : Fin (n + 1) := ⟨(image ι).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_epi (factorThruImage ι)) r.isLt⟩
  rw [attachEnd_factor_mono K hs V p t (ρ ≫ ι) (ρ ≫ factorThruImage ι)
    (epi_comp _ _) (image.ι ι) inferInstance (by rw [Category.assoc, image.fac])]
  rw [← attachEpi_oldEpi K hs V t r (factorThruImage ι) inferInstance ρ hρ,
    ← Category.assoc, attachFace_naturality, image.fac]

/-- Endomorphisms of the top family commute with every lower face.
Source: Stacks 0DAV, simplicial composition check.
(auxiliary; not a blueprint node) -/
theorem attachEnd_face
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q : Fin (n + 1))
    (β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd K hs V p β ≫ attachFace K V p q α = attachFace K V p q (α ≫ β) := by
  classical
  unfold attachEnd
  split_ifs with hβ
  · have he : β = 𝟙 _ := SimplexCategory.eq_id_of_epi β
    subst β
    simp
  · dsimp only
    rw [Category.assoc, attachEpi_face, attachFace_naturality]
    congr 1
    rw [Category.assoc, image.fac]

/-- A lift followed by a top endomorphism is the lift of the composite.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
theorem attachLift_end
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1))
    (β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) :
    attachLift K hs V q (α ≫ β) = attachLift K hs V q β ≫ attachEnd K hs V p α := by
  classical
  unfold attachEnd
  split_ifs with hα
  · have he : α = 𝟙 _ := SimplexCategory.eq_id_of_epi α
    subst α
    simp
  · dsimp only
    rw [← Category.assoc, attachLift_face, ← attachLift_factor]
    rw [← Category.assoc, image.fac]

/-- A lift through an old degree followed by a face gives a top endomorphism.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
theorem attachEnd_lift
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd K hs V p (α ≫ β) = attachFace K V p r β ≫ attachLift K hs V r α := by
  unfold attachLift
  dsimp only
  rw [← Category.assoc, attachFace_naturality, ← attachEnd_factor]
  rw [← Category.assoc, image.fac]

/-- The top endomorphisms compose contravariantly. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachEnd_comp
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V)
    (α β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd K hs V p (α ≫ β) = attachEnd K hs V p β ≫ attachEnd K hs V p α := by
  classical
  conv_rhs => rhs; unfold attachEnd
  split_ifs with hα
  · have he : α = 𝟙 _ := SimplexCategory.eq_id_of_epi α
    subst α
    simp
  · dsimp only
    rw [← Category.assoc, attachEnd_face, ← attachEnd_factor]
    rw [← Category.assoc, image.fac]

/-- The actual degree families of the extension; old degrees stay literally unchanged.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
def attachmentTerm
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n)
    (V : FormalCoproduct.{w} D) (q : Fin (n + 2)) : FormalCoproduct.{w} D :=
  if hq : q.val < n + 1 then term K ⟨q.val, hq⟩ else attachedFamily K V

/-- Every ordinal operator of the extension, before verifying composition.
Source: Stacks 0DAV. (auxiliary; not a blueprint node) -/
noncomputable def attachmentMap
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V)
    (q r : Fin (n + 2)) (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    attachmentTerm K V r ⟶ attachmentTerm K V q := by
  classical
  by_cases hq : q.val < n + 1
  · by_cases hr : r.val < n + 1
    · exact eqToHom (by simp only [attachmentTerm, dite_eq_left hr]) ≫
        operator K (q := ⟨q.val, hq⟩) (r := ⟨r.val, hr⟩) α ≫
          eqToHom (by simp only [attachmentTerm, dite_eq_left hq])
    · have hb := r.isLt
      have he : r = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
      subst r
      exact eqToHom (by simp [attachmentTerm]) ≫ attachFace K V p ⟨q.val, hq⟩ α ≫
        eqToHom (by simp only [attachmentTerm, dite_eq_left hq])
  · have hb := q.isLt
    have he : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
    subst q
    by_cases hr : r.val < n + 1
    · exact eqToHom (by simp only [attachmentTerm, dite_eq_left hr]) ≫
        attachLift K hs V ⟨r.val, hr⟩ α ≫ eqToHom (by simp [attachmentTerm])
    · have hb := r.isLt
      have he : r = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
      subst r
      exact eqToHom (by simp [attachmentTerm]) ≫ attachEnd K hs V p α ≫
        eqToHom (by simp [attachmentTerm])

/-- The top-to-old epi case is the normalization formula. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachmentMap_epi
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    attachmentMap K hs V p ⟨n + 1, Nat.lt_succ_self _⟩
      ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩ σ =
        eqToHom (by simp [attachmentTerm, q.isLt]) ≫ attachEpi K hs V q σ hσ ≫
          eqToHom (by simp [attachmentTerm]) := by
  classical
  simp [attachmentMap, q.isLt, attachLift_epi K hs V q σ hσ]

private theorem eqToHom_component_iso {A B : FormalCoproduct.{w} D} (h : A = B)
    (i : A.I) : IsIso ((eqToHom h).φ i) := by
  subst B
  change IsIso (𝟙 _)
  infer_instance

/-- Every component of a top degeneracy is invertible. Source: Stacks 0DAU and 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachmentMap_epi_component_iso
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ)
    (i : (attachmentTerm K V ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩).I) :
    IsIso ((attachmentMap K hs V p ⟨n + 1, Nat.lt_succ_self _⟩
      ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩ σ).φ i) := by
  rw [attachmentMap_epi K hs V p q σ hσ]
  have {A B : FormalCoproduct.{w} D} (h : A = B) (j : A.I) :
      IsIso ((eqToHom h).φ j) := eqToHom_component_iso h j
  have (j : (term K q).I) : IsIso ((attachEpi K hs V q σ hσ).φ j) := by
    dsimp [attachEpi, denormalize]
    have := hs.2 q (normalization K hs q j)
    infer_instance
  change IsIso ((_ ≫ _ ≫ _ : _ ⟶ _))
  infer_instance

/-- The explicit operators preserve identities. Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
theorem attachmentMap_id
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} D) n) (hs : IsSplit K)
    (V : FormalCoproduct.{w} D) (p : BoundaryCone K V) (q : Fin (n + 2)) :
    attachmentMap K hs V p q q (𝟙 _) = 𝟙 _ := by
  classical
  by_cases hq : q.val < n + 1
  · simp only [attachmentMap, dite_eq_left hq]
    have hmap : operator K (q := ⟨q.val, hq⟩) (r := ⟨q.val, hq⟩) (𝟙 _) = 𝟙 _ := by
      exact K.map_id _
    rw [hmap]
    simp
  · have hb := q.isLt
    have he : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
    subst q
    have hepi : Epi (𝟙 (SimplexCategory.mk (n + 1))) := inferInstance
    simp [attachmentMap, attachEnd, hepi]

end CategoryTheory.FormalSplitAttachment
