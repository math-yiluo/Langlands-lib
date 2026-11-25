/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
import Mathlib.AlgebraicGeometry.LimitsOver

/-! Explicit simplicial attachment and its refinement map.

Source: Stacks, Hypercoverings, 0DAV and 01GJ. The epi--mono identities adapt
`SiteHypercoverAttachmentOperators` and `SiteHypercoverAttachmentComposition`,
using actual splitting cofans in place of formal-family component choices.
(auxiliary; not a blueprint node)
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.SchemeSplitAttachment

variable {X : Scheme.{u}} {n : ℕ}

local instance {I : Type} : HasCoproductsOfShape I X.Etale := by
  dsimp [Scheme.Etale]
  infer_instance

abbrev degree
    (q : Fin (n + 1)) : SimplexCategory.Truncated n :=
  ⟨SimplexCategory.mk q.val, Nat.le_of_lt_succ q.isLt⟩
abbrev term (U : TruncatedFiniteSplitEtaleHypercover X n)
    (q : Fin (n + 1)) :=
  U.simplicial.obj (op (degree q))
def operator (U : TruncatedFiniteSplitEtaleHypercover X n)
    {q r : Fin (n + 1)} (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    term U r ⟶ term U q :=
  U.simplicial.map (SimplexCategory.Truncated.Hom.tr α _ _).op

abbrev Labels (n q : ℕ) := Σ r : Fin (n + 1),
  {σ : SimplexCategory.mk q ⟶ SimplexCategory.mk r.val // Epi σ}
def attachedFamily (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale) : X.Etale :=
  V ⨿ ∐ (fun a : Labels n (n + 1) ↦ U.N a.1)
def oldInclusion (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (a : Labels n (n + 1)) : U.N a.1 ⟶ attachedFamily U V :=
  Sigma.ι (fun a : Labels n (n + 1) ↦ U.N a.1) a ≫ coprod.inr

def precomposeLabel {q r : ℕ} (a : Labels n r)
    (σ : SimplexCategory.mk q ⟶ SimplexCategory.mk r) (hσ : Epi σ) : Labels n q :=
  ⟨a.1, ⟨σ ≫ a.2.val, by have := a.2.property; exact epi_comp _ _⟩⟩

noncomputable def attachEpi (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    term U q ⟶ attachedFamily U V :=
  Cofan.IsColimit.desc (U.splitting (op (degree q)))
    (fun a ↦ oldInclusion U V (precomposeLabel a σ hσ))

theorem attachEpi_fac (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q : Fin (n + 1)) (a : Labels n q.val)
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    (U.inclusion a.1 ≫ operator U a.2.val) ≫ attachEpi U V q σ hσ =
      oldInclusion U V (precomposeLabel a σ hσ) :=
  Cofan.IsColimit.fac (U.splitting (op (degree q))) _ a

theorem attachEpi_oldEpi (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q r : Fin (n + 1))
    (θ : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) (hθ : Epi θ)
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hσ : Epi σ) :
    operator U θ ≫ attachEpi U V r σ hσ =
      attachEpi U V q (σ ≫ θ) (epi_comp σ θ) := by
  apply Cofan.IsColimit.hom_ext (U.splitting (op (degree q)))
  intro a
  change (U.inclusion a.1 ≫ operator U a.2.val) ≫
    (operator U θ ≫ attachEpi U V r σ hσ) =
      (U.inclusion a.1 ≫ operator U a.2.val) ≫ attachEpi U V q (σ ≫ θ) _
  have hcomp : operator U a.2.val ≫ operator U θ = operator U (θ ≫ a.2.val) := by
    dsimp [operator]
    rw [← U.simplicial.map_comp]
    rfl
  rw [← Category.assoc, Category.assoc (U.inclusion a.1), hcomp]
  have hh := attachEpi_fac U V r (precomposeLabel a θ hθ) σ hσ
  dsimp only [precomposeLabel] at hh
  rw [hh, attachEpi_fac U V q a (σ ≫ θ)]
  congr 1

noncomputable def attachFace (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q : Fin (n + 1)) (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) :
    attachedFamily U V ⟶ term U q :=
  coprod.desc (b ≫ Q.π (degree q) α) (Sigma.desc
    (fun a : Labels n (n + 1) ↦ U.inclusion a.1 ≫ operator U (α ≫ a.2.val)))

theorem oldInclusion_face (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q : Fin (n + 1)) (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1))
    (a : Labels n (n + 1)) :
    oldInclusion U V a ≫ attachFace U V Q b q α =
      U.inclusion a.1 ≫ operator U (α ≫ a.2.val) := by
  simp [oldInclusion, attachFace, Category.assoc]

theorem attachFace_naturality (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q r : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachFace U V Q b r β ≫ operator U α = attachFace U V Q b q (α ≫ β) := by
  apply coprod.hom_ext
  · simp only [attachFace, coprod.inl_desc_assoc, coprod.inl_desc]
    change (b ≫ Q.π (degree r) β) ≫ U.simplicial.map
      (SimplexCategory.Truncated.Hom.tr α _ _).op = _
    rw [Category.assoc, Q.naturality]
    rfl
  · apply Sigma.hom_ext
    intro a
    have hc := oldInclusion_face U V Q b r β a
    have hc' := oldInclusion_face U V Q b q (α ≫ β) a
    change (oldInclusion U V a ≫ attachFace U V Q b r β) ≫ operator U α =
      oldInclusion U V a ≫ attachFace U V Q b q (α ≫ β)
    rw [hc, hc']
    dsimp [operator]
    rw [Category.assoc, ← U.simplicial.map_comp]
    congr 2

theorem attachEpi_face (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q r : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ)
    (α : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEpi U V q σ hσ ≫ attachFace U V Q b r α = operator U (α ≫ σ) := by
  apply Cofan.IsColimit.hom_ext (U.splitting (op (degree q)))
  intro a
  change (U.inclusion a.1 ≫ operator U a.2.val) ≫ _ = _
  rw [← Category.assoc, attachEpi_fac, oldInclusion_face]
  dsimp [operator, precomposeLabel]
  rw [Category.assoc, ← U.simplicial.map_comp]
  congr 2

noncomputable def attachLift
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) :
    term U q ⟶ attachedFamily U V :=
  let r : Fin (n + 1) := ⟨(image α).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι α)) q.isLt⟩
  operator U (q := r) (image.ι α) ≫
    attachEpi U V r (factorThruImage α) inferInstance


theorem attachLift_factor_mono
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val)
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) (hι : Mono ι)
    (hfac : ρ ≫ ι = α) :
    attachLift U V q α = operator U ι ≫ attachEpi U V r ρ hρ := by
  have : StrongEpi ρ := strongEpi_of_epi ρ
  let u := image.isoStrongEpiMono ρ ι hfac
  let t : Fin (n + 1) := ⟨(image α).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι α)) q.isLt⟩
  have h1 : operator U ι = operator U (q := t) (r := q) (image.ι α) ≫
      operator U (q := r) (r := t) u.hom := by
    dsimp [operator]
    rw [← U.simplicial.map_comp]
    change U.simplicial.map _ = U.simplicial.map
      (SimplexCategory.Truncated.Hom.tr (u.hom ≫ image.ι α) _ _).op
    rw [image.isoStrongEpiMono_hom_comp_ι]
  have h2 : ρ ≫ u.hom = factorThruImage α := by
    apply (cancel_mono (image.ι α)).mp
    simp [Category.assoc, u, hfac]
  rw [h1, Category.assoc, attachEpi_oldEpi U V t r u.hom inferInstance ρ hρ]
  simp only [h2]
  rfl


theorem attachLift_factor
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q r : Fin (n + 1))
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) :
    attachLift U V q (ρ ≫ ι) = operator U ι ≫ attachEpi U V r ρ hρ := by
  let t : Fin (n + 1) := ⟨(image ι).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι ι)) q.isLt⟩
  rw [attachLift_factor_mono U V q t (ρ ≫ ι) (ρ ≫ factorThruImage ι)
    (epi_comp _ _) (image.ι ι) inferInstance (by rw [Category.assoc, image.fac])]
  rw [← attachEpi_oldEpi U V t r (factorThruImage ι) inferInstance ρ hρ,
    ← Category.assoc]
  congr 1
  dsimp [operator]
  rw [← U.simplicial.map_comp]
  change U.simplicial.map (SimplexCategory.Truncated.Hom.tr
    (factorThruImage ι ≫ image.ι ι) _ _).op = _
  rw [image.fac]


theorem attachLift_naturality
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk q.val) :
    attachLift U V q (α ≫ β) = operator U β ≫ attachLift U V r α := by
  let t : Fin (n + 1) := ⟨(image α).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_mono (image.ι α)) r.isLt⟩
  have hf : α ≫ β = factorThruImage α ≫ (image.ι α ≫ β) := by
    rw [← Category.assoc, image.fac]
  rw [hf, attachLift_factor U V q t (factorThruImage α) inferInstance]
  have hc : operator U (q := t) (r := q) (image.ι α ≫ β) =
      operator U β ≫ operator U (q := t) (r := r) (image.ι α) := by
    dsimp [operator]
    rw [← U.simplicial.map_comp]
    rfl
  rw [hc, Category.assoc]
  rfl


theorem attachLift_epi
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    attachLift U V q σ = attachEpi U V q σ hσ := by
  rw [attachLift_factor_mono U V q q σ σ hσ (𝟙 _) inferInstance (Category.comp_id σ)]
  have hi : operator U (q := q) (r := q) (𝟙 _) = 𝟙 _ := U.simplicial.map_id _
  rw [hi, Category.id_comp]


theorem attachLift_face
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q r : Fin (n + 1))
    (β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val)
    (α : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachLift U V q β ≫ attachFace U V Q b r α = operator U (α ≫ β) := by
  unfold attachLift
  dsimp only
  rw [Category.assoc, attachEpi_face]
  dsimp [operator]
  rw [← U.simplicial.map_comp]
  change U.simplicial.map (SimplexCategory.Truncated.Hom.tr
    ((α ≫ factorThruImage β) ≫ image.ι β) _ _).op = _
  rw [Category.assoc, image.fac]


noncomputable def attachEnd
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1)) :
    attachedFamily U V ⟶ attachedFamily U V := by
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
    attachFace U V Q b r (image.ι α) ≫
      attachEpi U V r (factorThruImage α) inferInstance


theorem attachEnd_factor_mono
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1))
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) (hι : Mono ι)
    (hfac : ρ ≫ ι = α) :
    attachEnd U V Q b α = attachFace U V Q b r ι ≫ attachEpi U V r ρ hρ := by
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
  have h1 : attachFace U V Q b r ι = attachFace U V Q b t (image.ι α) ≫
      operator U (q := r) (r := t) u.hom := by
    rw [attachFace_naturality]
    congr 1
    exact (image.isoStrongEpiMono_hom_comp_ι ρ ι hfac).symm
  have h2 : ρ ≫ u.hom = factorThruImage α := by
    apply (cancel_mono (image.ι α)).mp
    simp [Category.assoc, u, hfac]
  rw [h1, Category.assoc, attachEpi_oldEpi U V t r u.hom inferInstance ρ hρ]
  simp only [h2, attachEnd, dite_eq_right hα]
  rfl


theorem attachEnd_factor
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (r : Fin (n + 1))
    (ρ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val) (hρ : Epi ρ)
    (ι : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd U V Q b (ρ ≫ ι) = attachFace U V Q b r ι ≫ attachEpi U V r ρ hρ := by
  let t : Fin (n + 1) := ⟨(image ι).len,
    lt_of_le_of_lt (SimplexCategory.len_le_of_epi (factorThruImage ι)) r.isLt⟩
  rw [attachEnd_factor_mono U V Q b t (ρ ≫ ι) (ρ ≫ factorThruImage ι)
    (epi_comp _ _) (image.ι ι) inferInstance (by rw [Category.assoc, image.fac])]
  rw [← attachEpi_oldEpi U V t r (factorThruImage ι) inferInstance ρ hρ,
    ← Category.assoc, attachFace_naturality, image.fac]


theorem attachEnd_face
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q : Fin (n + 1))
    (β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd U V Q b β ≫ attachFace U V Q b q α = attachFace U V Q b q (α ≫ β) := by
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


theorem attachLift_end
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1))
    (β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) :
    attachLift U V q (α ≫ β) = attachLift U V q β ≫ attachEnd U V Q b α := by
  classical
  unfold attachEnd
  split_ifs with hα
  · have he : α = 𝟙 _ := SimplexCategory.eq_id_of_epi α
    subst α
    simp
  · dsimp only
    rw [← Category.assoc, attachLift_face, ← attachLift_factor]
    rw [← Category.assoc, image.fac]


theorem attachEnd_lift
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (r : Fin (n + 1))
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd U V Q b (α ≫ β) = attachFace U V Q b r β ≫ attachLift U V r α := by
  unfold attachLift
  dsimp only
  rw [← Category.assoc, attachFace_naturality, ← attachEnd_factor]
  rw [← Category.assoc, image.fac]


theorem attachEnd_comp
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (α β : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd U V Q b (α ≫ β) = attachEnd U V Q b β ≫ attachEnd U V Q b α := by
  classical
  conv_rhs => rhs; unfold attachEnd
  split_ifs with hα
  · have he : α = 𝟙 _ := SimplexCategory.eq_id_of_epi α
    subst α
    simp
  · dsimp only
    rw [← Category.assoc, attachEnd_face, ← attachEnd_factor]
    rw [← Category.assoc, image.fac]


def attachmentTerm
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale)
    (q : Fin (n + 2)) : X.Etale :=
  if hq : q.val < n + 1 then term U ⟨q.val, hq⟩ else attachedFamily U V


@[irreducible] noncomputable def attachmentMap
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q r : Fin (n + 2)) (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    attachmentTerm U V r ⟶ attachmentTerm U V q := by
  classical
  by_cases hq : q.val < n + 1
  · by_cases hr : r.val < n + 1
    · exact eqToHom (by simp only [attachmentTerm, dite_eq_left hr]) ≫
        operator U (q := ⟨q.val, hq⟩) (r := ⟨r.val, hr⟩) α ≫
          eqToHom (by simp only [attachmentTerm, dite_eq_left hq])
    · have hb := r.isLt
      have he : r = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
      subst r
      exact eqToHom (by simp [attachmentTerm]) ≫ attachFace U V Q b ⟨q.val, hq⟩ α ≫
        eqToHom (by simp only [attachmentTerm, dite_eq_left hq])
  · have hb := q.isLt
    have he : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
    subst q
    by_cases hr : r.val < n + 1
    · exact eqToHom (by simp only [attachmentTerm, dite_eq_left hr]) ≫
        attachLift U V ⟨r.val, hr⟩ α ≫ eqToHom (by simp [attachmentTerm])
    · have hb := r.isLt
      have he : r = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
      subst r
      exact eqToHom (by simp [attachmentTerm]) ≫ attachEnd U V Q b α ≫
        eqToHom (by simp [attachmentTerm])


theorem attachmentMap_epi
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    attachmentMap U V Q b ⟨n + 1, Nat.lt_succ_self _⟩
      ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩ σ =
        eqToHom (by simp [attachmentTerm, q.isLt]) ≫ attachEpi U V q σ hσ ≫
          eqToHom (by simp [attachmentTerm]) := by
  classical
  simp [attachmentMap, q.isLt, attachLift_epi U V q σ hσ]

theorem attachmentMap_id
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q : Fin (n + 2)) :
    attachmentMap U V Q b q q (𝟙 _) = 𝟙 _ := by
  classical
  by_cases hq : q.val < n + 1
  · simp only [attachmentMap, dite_eq_left hq]
    have hmap : operator U (q := ⟨q.val, hq⟩) (r := ⟨q.val, hq⟩) (𝟙 _) = 𝟙 _ := by
      exact U.simplicial.map_id _
    rw [hmap]
    simp
  · have hb := q.isLt
    have he : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp; omega)
    subst q
    have hepi : Epi (𝟙 (SimplexCategory.mk (n + 1))) := inferInstance
    simp [attachmentMap, attachEnd, hepi]

private theorem transport_attachment_equality
    (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale) (q s : Fin (n + 2))
    {A B : X.Etale} (hs : attachmentTerm U V s = A)
    (hq : attachmentTerm U V q = B) {f g : A ⟶ B} (h : f = g) :
    eqToHom hs ≫ f ≫ eqToHom hq.symm =
      eqToHom hs ≫ g ≫ eqToHom hq.symm := by rw [h]


theorem attachmentMap_comp
    (U : TruncatedFiniteSplitEtaleHypercover X n) (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M)
    (q r s : Fin (n + 2))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val)
    (β : SimplexCategory.mk r.val ⟶ SimplexCategory.mk s.val) :
    attachmentMap U V Q b q s (α ≫ β) =
      attachmentMap U V Q b r s β ≫ attachmentMap U V Q b q r α := by
  classical
  have htop (a : Fin (n + 2)) (ha : ¬ a.val < n + 1) :
      a = ⟨n + 1, Nat.lt_succ_self _⟩ := by
    have hb := a.isLt
    exact Fin.ext (by dsimp; omega)
  by_cases hq : q.val < n + 1
  · by_cases hr : r.val < n + 1
    · by_cases hss : s.val < n + 1
      · have hc : operator U (q := ⟨q.val, hq⟩) (r := ⟨s.val, hss⟩) (α ≫ β) =
            operator U (q := ⟨r.val, hr⟩) (r := ⟨s.val, hss⟩) β ≫
              operator U (q := ⟨q.val, hq⟩) (r := ⟨r.val, hr⟩) α := by
          dsimp [operator]
          rw [← U.simplicial.map_comp]
          rfl
        simpa [attachmentMap, attachmentTerm, hq, hr, hss, Category.assoc] using
          transport_attachment_equality U V q s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm, hq]) hc
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, hq, hr, Category.assoc] using
          transport_attachment_equality U V q ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm, hq])
            ((attachFace_naturality U V Q b ⟨q.val, hq⟩ ⟨r.val, hr⟩ α β).symm)
    · have he := htop r hr
      subst r
      by_cases hss : s.val < n + 1
      · simpa [attachmentMap, attachmentTerm, hq, hss, Category.assoc] using
          transport_attachment_equality U V q s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm, hq])
            ((attachLift_face U V Q b ⟨s.val, hss⟩ ⟨q.val, hq⟩ β α).symm)
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, hq, Category.assoc] using
          transport_attachment_equality U V q ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm, hq])
            ((attachEnd_face U V Q b ⟨q.val, hq⟩ β α).symm)
  · have he := htop q hq
    subst q
    by_cases hr : r.val < n + 1
    · by_cases hss : s.val < n + 1
      · simpa [attachmentMap, attachmentTerm, hr, hss, Category.assoc] using
          transport_attachment_equality U V ⟨n + 1, Nat.lt_succ_self _⟩ s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm])
            (attachLift_naturality U V ⟨s.val, hss⟩ ⟨r.val, hr⟩ α β)
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, hr, Category.assoc] using
          transport_attachment_equality U V ⟨n + 1, Nat.lt_succ_self _⟩ ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm])
            (attachEnd_lift U V Q b ⟨r.val, hr⟩ α β)
    · have he := htop r hr
      subst r
      by_cases hss : s.val < n + 1
      · simpa [attachmentMap, attachmentTerm, hss, Category.assoc] using
          transport_attachment_equality U V ⟨n + 1, Nat.lt_succ_self _⟩ s
            (by simp [attachmentTerm, hss]) (by simp [attachmentTerm])
            (attachLift_end U V Q b ⟨s.val, hss⟩ α β)
      · have he := htop s hss
        subst s
        simpa [attachmentMap, attachmentTerm, Category.assoc] using
          transport_attachment_equality U V ⟨n + 1, Nat.lt_succ_self _⟩ ⟨n + 1, Nat.lt_succ_self _⟩
            (by simp [attachmentTerm]) (by simp [attachmentTerm])
            (attachEnd_comp U V Q b α β)

/-- The explicit new truncated functor, with all composition cases proved above.
Source: Stacks 0DAV.
(auxiliary; not a blueprint node) -/
noncomputable def attachedSimplicial (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M) :
    SimplicialObject.Truncated X.Etale (n + 1) where
  obj Δ := attachmentTerm U V ⟨Δ.unop.obj.len, Nat.lt_succ_of_le Δ.unop.property⟩
  map {Δ Δ'} f := attachmentMap U V Q b
    ⟨Δ'.unop.obj.len, Nat.lt_succ_of_le Δ'.unop.property⟩
    ⟨Δ.unop.obj.len, Nat.lt_succ_of_le Δ.unop.property⟩ f.unop.hom
  map_id Δ := attachmentMap_id U V Q b _
  map_comp := by
    intro Δ Δ' Δ'' f g
    exact attachmentMap_comp U V Q b
      ⟨Δ''.unop.obj.len, Nat.lt_succ_of_le Δ''.unop.property⟩
      ⟨Δ'.unop.obj.len, Nat.lt_succ_of_le Δ'.unop.property⟩
      ⟨Δ.unop.obj.len, Nat.lt_succ_of_le Δ.unop.property⟩ g.unop.hom f.unop.hom

theorem attachedSimplicial_restrict (U : TruncatedFiniteSplitEtaleHypercover X n)
    (V : X.Etale)
    (Q : ReplacementBoundary U) (b : V ⟶ Q.M) :
    (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).obj
      (attachedSimplicial U V Q b) = U.simplicial := by
  apply CategoryTheory.Functor.hext
  · intro Δ
    simp [attachedSimplicial, attachmentTerm, term, degree,
      Nat.lt_succ_of_le Δ.unop.property]
  · intro Δ Δ' f
    simp [attachedSimplicial, attachmentMap, attachmentTerm, term, degree, operator,
      Nat.lt_succ_of_le Δ.unop.property, Nat.lt_succ_of_le Δ'.unop.property]
    rfl

noncomputable def topRefinement {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n)
    (V : X.Etale) (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1)))) :
    attachedFamily A.U V ⟶ K.obj (op (SimplexCategory.mk (n + 1))) :=
  coprod.desc g (Sigma.desc (fun a : Labels n (n + 1) ↦
    A.U.inclusion a.1 ≫ A.f.app (op (degree a.1)) ≫ K.map a.2.val.op))

theorem old_naturality {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n)
    (q r : Fin (n + 1))
    (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    operator A.U α ≫ A.f.app (op (degree q)) =
      A.f.app (op (degree r)) ≫ K.map α.op :=
  A.f.naturality (SimplexCategory.Truncated.Hom.tr α _ _).op

theorem attachFace_refinement {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (Q : ReplacementBoundary A.U) (b : V ⟶ Q.M)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (hcomp : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op)
    (q : Fin (n + 1)) (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk (n + 1)) :
    attachFace A.U V Q b q α ≫ A.f.app (op (degree q)) =
      topRefinement A V g ≫ K.map α.op := by
  apply coprod.hom_ext
  · simpa [attachFace, topRefinement, Category.assoc] using hcomp (degree q) α
  · apply Sigma.hom_ext
    intro a
    change (oldInclusion A.U V a ≫ attachFace A.U V Q b q α) ≫ _ = _
    rw [oldInclusion_face, Category.assoc, old_naturality]
    simp only [topRefinement, Category.assoc, coprod.inr_desc_assoc,
      Sigma.ι_comp_desc_assoc]
    rw [← K.map_comp]
    rfl

theorem attachEpi_refinement {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (q : Fin (n + 1))
    (σ : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) (hσ : Epi σ) :
    attachEpi A.U V q σ hσ ≫ topRefinement A V g =
      A.f.app (op (degree q)) ≫ K.map σ.op := by
  apply Cofan.IsColimit.hom_ext (A.U.splitting (op (degree q)))
  intro a
  change (A.U.inclusion a.1 ≫ operator A.U a.2.val) ≫ _ = _
  rw [← Category.assoc, attachEpi_fac]
  change oldInclusion A.U V (precomposeLabel a σ hσ) ≫ topRefinement A V g =
    (A.U.inclusion a.1 ≫ operator A.U a.2.val) ≫
      (A.f.app (op (degree q)) ≫ K.map σ.op)
  simp only [oldInclusion, topRefinement, Category.assoc, coprod.inr_desc,
    Sigma.ι_comp_desc, precomposeLabel]
  rw [← Category.assoc (operator A.U a.2.val), old_naturality]
  rw [Category.assoc, ← K.map_comp]
  rfl

theorem attachLift_refinement {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (q : Fin (n + 1)) (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk q.val) :
    attachLift A.U V q α ≫ topRefinement A V g =
      A.f.app (op (degree q)) ≫ K.map α.op := by
  unfold attachLift
  dsimp only
  rw [Category.assoc, attachEpi_refinement, ← Category.assoc, old_naturality]
  rw [Category.assoc, ← K.map_comp]
  change _ ≫ K.map (factorThruImage α ≫ image.ι α).op = _
  rw [image.fac]

theorem attachEnd_refinement {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (Q : ReplacementBoundary A.U) (b : V ⟶ Q.M)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (hcomp : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op)
    (α : SimplexCategory.mk (n + 1) ⟶ SimplexCategory.mk (n + 1)) :
    attachEnd A.U V Q b α ≫ topRefinement A V g =
      topRefinement A V g ≫ K.map α.op := by
  classical
  unfold attachEnd
  split_ifs with hα
  · have he : α = 𝟙 _ := SimplexCategory.eq_id_of_epi α
    subst α
    simp
  · dsimp only
    rw [Category.assoc, attachEpi_refinement, ← Category.assoc,
      attachFace_refinement A V Q b g hcomp]
    rw [Category.assoc, ← K.map_comp]
    change _ ≫ K.map (factorThruImage α ≫ image.ι α).op = _
    rw [image.fac]

noncomputable def refinementComponent {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (q : Fin (n + 2)) : attachmentTerm A.U V q ⟶ K.obj (op (SimplexCategory.mk q.val)) := by
  classical
  by_cases hq : q.val < n + 1
  · exact eqToHom (by simp [attachmentTerm, hq]) ≫ A.f.app (op (degree ⟨q.val, hq⟩))
  · have he : q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := q.isLt; dsimp; omega)
    subst q
    exact eqToHom (by simp [attachmentTerm]) ≫ topRefinement A V g

theorem refinement_naturality {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (Q : ReplacementBoundary A.U) (b : V ⟶ Q.M)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (hcomp : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op)
    (q r : Fin (n + 2)) (α : SimplexCategory.mk q.val ⟶ SimplexCategory.mk r.val) :
    attachmentMap A.U V Q b q r α ≫ refinementComponent A V g q =
      refinementComponent A V g r ≫ K.map α.op := by
  classical
  have htop
    (q : Fin (n + 2)) (hq : ¬ q.val < n + 1) :
      q = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := q.isLt; dsimp; omega)
  by_cases hq : q.val < n + 1
  · by_cases hr : r.val < n + 1
    · simpa [attachmentMap, refinementComponent, hq, hr, Category.assoc] using
        congrArg (fun t ↦ eqToHom (by simp [attachmentTerm, hr]) ≫ t)
          (old_naturality A ⟨q.val, hq⟩ ⟨r.val, hr⟩ α)
    · have he := htop r hr
      subst r
      simpa [attachmentMap, refinementComponent, hq, Category.assoc] using
        congrArg (fun t ↦ eqToHom (by simp [attachmentTerm]) ≫ t)
          (attachFace_refinement A V Q b g hcomp ⟨q.val, hq⟩ α)
  · have he := htop q hq
    subst q
    by_cases hr : r.val < n + 1
    · simpa [attachmentMap, refinementComponent, hr, Category.assoc] using
        congrArg (fun t ↦ eqToHom (by simp [attachmentTerm, hr]) ≫ t)
          (attachLift_refinement A V g ⟨r.val, hr⟩ α)
    · have he := htop r hr
      subst r
      simpa [attachmentMap, refinementComponent, Category.assoc] using
        congrArg (fun t ↦ eqToHom (by simp [attachmentTerm]) ≫ t)
          (attachEnd_refinement A V Q b g hcomp α)

/-- The refinement determined by g and the old refinement on degenerate summands.
Source: Stacks 01GJ.
(auxiliary; not a blueprint node) -/
noncomputable def attachedRefinement {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (Q : ReplacementBoundary A.U) (b : V ⟶ Q.M)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (hcomp : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op) :
    attachedSimplicial A.U V Q b ⟶ (SimplicialObject.truncation (n + 1)).obj K where
  app Δ := refinementComponent A V g
    ⟨Δ.unop.obj.len, Nat.lt_succ_of_le Δ.unop.property⟩
  naturality := by
    intro Δ Δ' f
    exact refinement_naturality A V Q b g hcomp
      ⟨Δ'.unop.obj.len, Nat.lt_succ_of_le Δ'.unop.property⟩
      ⟨Δ.unop.obj.len, Nat.lt_succ_of_le Δ.unop.property⟩ f.unop.hom

theorem attachedRefinement_restrict {K : SimplicialObject X.Etale}
    (A : FiniteSplitReplacementStage K n) (V : X.Etale)
    (Q : ReplacementBoundary A.U) (b : V ⟶ Q.M)
    (g : V ⟶ K.obj (op (SimplexCategory.mk (n + 1))))
    (hcomp : ∀ (Δ : SimplexCategory.Truncated n)
      (θ : Δ.obj ⟶ SimplexCategory.mk (n + 1)),
      b ≫ Q.π Δ θ ≫ A.f.app (op Δ) = g ≫ K.map θ.op) :
    (SimplicialObject.Truncated.trunc X.Etale (n + 1) n).map
        (attachedRefinement A V Q b g hcomp) =
      eqToHom (attachedSimplicial_restrict A.U V Q b) ≫ A.f := by
  ext Δ
  change refinementComponent A V g
    ⟨Δ.unop.obj.len, Nat.lt_succ_of_le (Δ.unop.property.trans (Nat.le_succ n))⟩ = _
  simp only [refinementComponent, dite_eq_left (Nat.lt_succ_of_le Δ.unop.property),
    NatTrans.comp_app, eqToHom_app]

end AlgebraicGeometry.SchemeSplitAttachment
