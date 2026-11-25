/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import WeilConjectures.AlgebraicGeometry.LocalizingPrincipalCoverGluing

/-! # The affine-basis sheaf condition for a localizing module presheaf

Source: Stacks Project, Tag 01HV, with Tags 009N and 009Q.
(blueprint: lem-pc-affine-localizing-presheaf-basis-sheaf).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem affineBasis_coverDense (T : Scheme.{u}) :
    ((Subtype.mono_coe T.affineOpens).functor).IsCoverDense
      (Opens.grothendieckTopology T) := by
  let G := (Subtype.mono_coe T.affineOpens).functor
  have hGB : Opens.IsBasis (Set.range G.obj) := by
    convert T.isBasis_affineOpens using 1
    ext U
    constructor
    · rintro ⟨⟨U, hU⟩, rfl⟩
      exact hU
    · intro hU
      exact ⟨⟨U, hU⟩, rfl⟩
  exact (TopCat.Opens.coverDense_iff_isBasis G).2 hGB

set_option backward.isDefEq.respectTransparency false in
private theorem principalCover_refinement
    (T : Scheme.{u}) (W : T.affineOpens) (S : Sieve W)
    (hS : S ∈ ((Subtype.mono_coe T.affineOpens).functor).inducedTopology
      (Opens.grothendieckTopology T) W) :
    ∃ s : Set Γ(T, W.1), (⨆ a : s, T.basicOpen a.val) = W.val ∧
      Presieve.ofArrows (fun a : s ↦ T.affineBasicOpen (U := W) a.val)
        (fun a ↦ homOfLE (T.affineBasicOpen_le a.val)) ≤ S.arrows := by
  let G := (Subtype.mono_coe T.affineOpens).functor
  let K := Opens.grothendieckTopology T
  let : G.IsCoverDense K := affineBasis_coverDense T
  let : G.Full := ⟨fun f ↦ ⟨homOfLE f.le, Subsingleton.elim _ _⟩⟩
  let : G.LocallyCoverDense K := Functor.locallyCoverDense_of_isCoverDense G K
  have hcover := (G.mem_inducedTopology_iff_of_isCoverDense
    K S).mp hS
  let s : Set Γ(T, W.1) := {a | S (homOfLE (T.affineBasicOpen_le (V := W) a))}
  refine ⟨s, le_antisymm (iSup_le fun a ↦ T.basicOpen_le a.val) ?_, ?_⟩
  · intro x hx
    obtain ⟨V, f, ⟨U, g, i, hg, _⟩, hxV⟩ := hcover x hx
    obtain ⟨a, ha, hxa⟩ := W.property.exists_basicOpen_le ⟨x, i.le hxV⟩ hx
    have hmem : a ∈ s := by
      exact S.downward_closed hg (homOfLE ha)
    exact Opens.mem_iSup.mpr ⟨⟨a, hmem⟩, hxa⟩
  · intro V f hf
    obtain ⟨a⟩ := hf
    exact a.property

/-- The underlying abelian-group presheaf satisfies the sheaf condition on the
site of affine opens when all affine-to-principal restrictions are localizations.
Source: Stacks Project, Tag 01HV, and Tags 009N/009Q.
(blueprint: lem-pc-affine-localizing-presheaf-basis-sheaf).

Proof: For an affine W, identify W with Spec Gamma(W). The restriction from
P(W) to each principal D(a) is the numerator map of a localization by hypothesis.
The localization universal property therefore gives a unique isomorphism with
sections of the associated module sheaf of P(W) on D(a). For inclusions of
principal opens these isomorphisms commute with restriction: both composites
are linear over Gamma(W) and agree on P(W), so localization uniqueness applies.
Consequently P on the principal basis of W satisfies unique gluing, as does the
associated module sheaf (01HV). In particular it is separated on that basis.
For any affine V contained in W, use the principal basis of V and the same
argument with V in place of W to detect equality and glue sections. To glue a
compatible family for an affine covering sieve on W, refine it by principal
opens of W. Glue on these principal opens, then obtain a section of P(W).
Its restriction to each affine member V agrees with the given section: cover
V by principal opens contained in the principal refinement and use the
separatedness already established for V. The same refinement proves uniqueness.
The induced topology consists exactly of sieves whose image covers W, so this
proves its sheaf condition. Empty covers are included: localization at zero
forces P of the empty affine open to be zero. No affine-intersection assumption
on the ambient scheme is used; all refinements take place inside an affine. -/
theorem isSheaf_affineBasis_of_localizing
    (T : Scheme.{u}) (P : _root_.PresheafOfModules.{u} T.ringCatSheaf.obj)
    (hP : ∀ (W : T.Opens), IsAffineOpen W → ∀ a : Γ(T, W),
      IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom) :
    CategoryTheory.Presheaf.IsSheaf
      (((Subtype.mono_coe T.affineOpens).functor).inducedTopology
        (Opens.grothendieckTopology T))
      (((Subtype.mono_coe T.affineOpens).functor).op ⋙ P.presheaf) := by
  let G := (Subtype.mono_coe T.affineOpens).functor
  let J := G.inducedTopology (Opens.grothendieckTopology T)
  let Q := (G.op ⋙ P.presheaf) ⋙ CategoryTheory.forget AddCommGrpCat.{u}
  apply (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget
    (J := J) (P' := G.op ⋙ P.presheaf) (CategoryTheory.forget AddCommGrpCat.{u})).mpr
  apply (CategoryTheory.isSheaf_iff_isSheaf_of_type J Q).mpr
  have hsep : Presieve.IsSeparated J Q := by
    intro W S hS
    obtain ⟨s, hs, hle⟩ := principalCover_refinement T W S hS
    have hR := isSheafFor_principalCover_of_localizing T P W (hP W.val W.property) s hs
    intro x t₁ t₂ ht₁ ht₂
    exact hR.isSeparatedFor (x.restrict hle) t₁ t₂
      (Presieve.isAmalgamation_restrict hle x t₁ ht₁)
      (Presieve.isAmalgamation_restrict hle x t₂ ht₂)
  intro W S hS
  obtain ⟨s, hs, hle⟩ := principalCover_refinement T W S hS
  let R := Presieve.ofArrows (fun a : s ↦ T.affineBasicOpen (U := W) a.val)
    (fun a ↦ homOfLE (T.affineBasicOpen_le a.val))
  have hR : Presieve.IsSheafFor Q R :=
    isSheafFor_principalCover_of_localizing T P W (hP W.val W.property) s hs
  have hgen : Sieve.generate R ≤ S := (Sieve.generate_le_iff R S).mpr hle
  have hcov : Sieve.generate R ∈ J W := by
    let K := Opens.grothendieckTopology T
    let : G.IsCoverDense K := affineBasis_coverDense T
    let : G.Full := ⟨fun f ↦ ⟨homOfLE f.le, Subsingleton.elim _ _⟩⟩
    let : G.LocallyCoverDense K := Functor.locallyCoverDense_of_isCoverDense G K
    apply (G.mem_inducedTopology_iff_of_isCoverDense K (Sieve.generate R)).mpr
    intro x hx
    change x ∈ W.val at hx
    rw [← hs] at hx
    obtain ⟨a, hxa⟩ := Opens.mem_iSup.mp hx
    refine ⟨T.basicOpen a.val, homOfLE (T.basicOpen_le a.val), ?_, hxa⟩
    exact ⟨T.affineBasicOpen (U := W) a.val,
      homOfLE (T.affineBasicOpen_le a.val), 𝟙 _,
      Sieve.le_generate R _ _ (Presieve.ofArrows.mk a), Subsingleton.elim _ _⟩
  exact Presieve.isSheafFor_subsieve_aux Q hgen
    ((Presieve.isSheafFor_iff_generate R).mp hR)
    (fun _ f _ ↦ hsep _ (J.pullback_stable f hcov))

end AlgebraicGeometry.Scheme.Modules
