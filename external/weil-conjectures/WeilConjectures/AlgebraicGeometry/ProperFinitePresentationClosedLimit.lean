/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope

/-! # Proper schemes as limits of proper finitely presented schemes

Source: Stacks Project, Limits, Lemma 09ZR
(blueprint: lem-weil-pbc-proper-closed-in-proper-fp).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A proper scheme over a qcqs base is a directed inverse limit of proper finitely
presented schemes over that base, with closed immersions as transitions and projections.
In particular it embeds as a closed subscheme of a proper finitely presented scheme.

Source: Stacks Project, Limits, Lemma 09ZR
(blueprint: lem-weil-pbc-proper-closed-in-proper-fp).

Proof:
1. Properness gives finite type and separatedness. By
   theorem-nagata-s-compactification-theorem--1 (01ZJ), embed X into a separated finitely
   presented S-scheme Y. Both X and Y are qcqs by
   lem-weil-pbc-qcqs-morphism-permanence.
2. Apply lem-weil-pbc-chow-finite-type (0202) to Y: obtain a proper surjective
   Y' → Y and an immersion Y' → projective space over S. The latter space is proper
   over S by lemma-nagata-projective-space-base-change-proper.
3. By lemma-nagata-closed-subscheme-fp-system (09ZP), express X as the inverse limit
   of the closed subschemes Xᵢ of Y defined by finite-type subideals of its ideal.
   Zero and sums make this a nonempty directed set. Every Xᵢ is finitely presented
   over S by lem-weil-pbc-proper-fp-permanence, and all transitions and projections
   are closed immersions. They are affine by lem-weil-pbc-closed-immersion-finite,
   so this is the limit of lem-weil-pbc-limit-affine-transition.
4. Pull back Xᵢ and X to Y', obtaining X'ᵢ and X'. Base change preserves closed
   immersions by lem-weil-pbc-proper-fp-permanence. Limits of sets commute with
   fibre products; directedness makes the constant factors stay constant. Thus
   the compatible maps X' → X'ᵢ form a limiting cone by Yoneda.
5. The scheme X' is proper over S by base change and composition. Its immersion
   into projective space is proper by lem-weil-pbc-proper-over-separated and hence
   closed by lem-weil-pbc-proper-immersion-closed.
6. Apply lem-weil-pbc-eventually-closed-immersion (0A0N) to X'ᵢ in projective space.
   The needed qcqs and finite-type properties follow from steps 1–4 and
   lem-weil-pbc-qcqs-morphism-permanence. From some stage onward these immersions
   are closed; closure under composition is lem-weil-pbc-closed-immersion-comp.
7. These X'ᵢ are proper over S. Their maps onto Xᵢ are surjective by
   lem-weil-pbc-surjective-base-change. By lem-weil-pbc-image-universally-closed
   (03GN), Xᵢ is universally closed over S. Its separatedness and finite type from
   step 3 therefore make it proper.
8. Restrict to the nonempty directed upper tail, which is cofinal and preserves
   the limit. Every stage now has all the asserted properties. Any stage supplies
   the finitely presented proper envelope in the final clause. -/
theorem exists_proper_finitePresentation_closedImmersion_limit
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    (∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u}) (p : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (π : (Functor.const Iᵒᵖ).obj X ⟶ D),
      (∀ i : Iᵒᵖ, IsProper (p.app i) ∧ LocallyOfFinitePresentation (p.app i) ∧
        QuasiCompact (p.app i) ∧ QuasiSeparated (p.app i)) ∧
      (∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsClosedImmersion (D.map a)) ∧
      (∀ i : Iᵒᵖ, IsClosedImmersion (π.app i) ∧ π.app i ≫ p.app i = f) ∧
      Nonempty (IsLimit (Cone.mk X π))) ∧
    (∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ S),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧
        QuasiCompact g ∧ QuasiSeparated g ∧ i ≫ g = f) := by
  obtain ⟨Y, i, g, hi, hg, hfp, hqc, hqs, hw⟩ :=
    exists_proper_finitePresentation_closedImmersion_envelope f
  have := hi
  have := hg
  have := hfp
  have := hqc
  have := hqs
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  refine ⟨?_, Y, i, g, hi, hg, hfp, hqc, hqs, hw⟩
  let p : i.ker.fgSubDiagram ⟶ (Functor.const _).obj S :=
    { app J := (J.unop : Y.IdealSheafData).subschemeι ≫ g
      naturality := by
        intro J J' a
        simp }
  let π := (Functor.const _).map i.toImage ≫ i.ker.fgSubCone.π
  refine ⟨i.ker.FGSub, inferInstance, inferInstance, inferInstance,
    i.ker.fgSubDiagram, p, π, ?_, ?_, ?_, ?_⟩
  · intro J
    change IsProper ((J.unop : Y.IdealSheafData).subschemeι ≫ g) ∧
      LocallyOfFinitePresentation ((J.unop : Y.IdealSheafData).subschemeι ≫ g) ∧
      QuasiCompact ((J.unop : Y.IdealSheafData).subschemeι ≫ g) ∧
      QuasiSeparated ((J.unop : Y.IdealSheafData).subschemeι ≫ g)
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  · intro J J' a
    infer_instance
  · intro J
    constructor
    · change IsClosedImmersion (i.toImage ≫ i.ker.fgSubCone.π.app J)
      infer_instance
    · change (i.toImage ≫ i.ker.fgSubCone.π.app J) ≫
        (J.unop : Y.IdealSheafData).subschemeι ≫ g = f
      simpa using hw
  · exact ⟨i.ker.isLimitFgSubCone.ofIsoLimit
      (Cone.ext (asIso i.toImage).symm fun J ↦ by simp [π])⟩

end AlgebraicGeometry
