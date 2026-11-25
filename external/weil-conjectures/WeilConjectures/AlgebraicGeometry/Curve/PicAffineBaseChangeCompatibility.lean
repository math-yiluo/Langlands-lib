/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.AlgebraicGeometry.BaseChangeCurve
import WeilConjectures.AlgebraicGeometry.Curve.PicRestrictionBoundary
import WeilConjectures.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport

/-! # Compatibility of the affine Picard quotient with field extension

Source: `literature/stacks-project/etale-cohomology.tex`, Tags 03RQ and 01JF
(blueprint: lem-sc-pic-affine-base-change-compatibility).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The affine Picard quotient description is compatible with extension of algebraically closed
fields.  The proof uses base change of the compactification, the boundary restriction theorem,
and the Jacobian base-change compatibility.

Source: Stacks Tags 03RQ and 01JF, and the affine case of
`proposition-cohomology-smooth-affine-curve` (blueprint:
lem-sc-pic-affine-base-change-compatibility).
-/
theorem pic_affine_base_change_compatibility
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [hsm' : SmoothOfRelativeDimension 1
      (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g]
    (P₀ : closedPoints c.Z) (hP₀ : P₀.val ∉ Set.range c.i.base) :
    IsConnectedCurve (CategoryTheory.Limits.pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ∧
      Smooth (CategoryTheory.Limits.pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ∧
      IsConnectedCurve (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g ∧
      Smooth (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g ∧
      IsProper (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g ∧
      IsOpenImmersion (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i ∧
      (Set.range (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base)ᶜ.Finite ∧
      Function.Surjective (Scheme.Pic.mapHom c.i) ∧
      (Scheme.Pic.mapHom c.i).ker = Subgroup.closure
        {L | ∃ P : closedPoints c.Z, P.val ∉ Set.range c.i.base ∧
          L = @Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P} ∧
      Function.Surjective (Scheme.Pic.mapHom
        (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i) ∧
      (Scheme.Pic.mapHom (Compactification.baseChange c
        (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i).ker = Subgroup.closure
        {L | ∃ P : closedPoints (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
          P.val ∉ Set.range (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base ∧
          L = @Scheme.Pic.ofClosedPoint k' _
            (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z
            ⟨(Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g⟩ hsm' P} ∧
      ∃ (G : Subgroup c.Z.Pic) (_ : (G : Set c.Z.Pic) = c.g.picZero)
        (Λ : Subgroup G) (e : (G ⧸ Λ) ≃* C.Pic)
        (G' : Subgroup (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.Pic)
        (_ : (G' : Set (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.Pic) =
          (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g.picZero)
        (Λ' : Subgroup G')
        (e' : (G' ⧸ Λ') ≃* (CategoryTheory.Limits.pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Pic)
        (j : c.Z.Pic →* (Compactification.baseChange c
          (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z.Pic)
        (hj : ∀ L : G, j L.val ∈ G'),
        Subgroup.map G.subtype Λ = Subgroup.closure
          {L | ∃ P : closedPoints c.Z, P.val ∉ Set.range c.i.base ∧
            L = @Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P /
              @Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P₀} ∧
        ∀ L : G, e (QuotientGroup.mk L) = Scheme.Pic.mapHom c.i L.val ∧
        Subgroup.map G'.subtype Λ' = Subgroup.closure
          {L | ∃ P Q : closedPoints (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z,
            P.val ∉ Set.range (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base ∧
            Q.val ∉ Set.range (Compactification.baseChange c
              (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i.base ∧
            L = @Scheme.Pic.ofClosedPoint k' _
              (Compactification.baseChange c
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z
              ⟨(Compactification.baseChange c
                (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g⟩ hsm' P /
              @Scheme.Pic.ofClosedPoint k' _
                (Compactification.baseChange c
                  (Spec.map (CommRingCat.ofHom (algebraMap k k')))).Z
                ⟨(Compactification.baseChange c
                  (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g⟩ hsm' Q} ∧
        ∀ L : G', e' (QuotientGroup.mk L) = Scheme.Pic.mapHom
          (Compactification.baseChange c
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).i L.val ∧
        (∃ ej : Λ ≃* Λ', ∀ L : Λ, (ej L : _) = j L.val) ∧
        ∀ L : c.Z.Pic, j L = Scheme.Pic.mapHom
          (CategoryTheory.Limits.pullback.fst c.g
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))) L ∧
        ∀ L : G, e' (QuotientGroup.mk ⟨j L.val, hj L⟩) =
          Scheme.Pic.mapHom (CategoryTheory.Limits.pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
            (e (QuotientGroup.mk L)) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let c' := c.baseChange b
  have hC := baseChange_curve (k' := k') f
  have hZ := baseChange_curve (k' := k') c.g
  have : IsConnectedCurve (pullback.snd f b) := hC.2.2.2.2.2 inferInstance
  have : Smooth (pullback.snd f b) := hC.2.2.1 inferInstance
  have : IsAffine (pullback f b) := hC.2.2.2.2.1 inferInstance
  have : IsConnectedCurve c'.g := hZ.2.2.2.2.2 inferInstance
  have : Smooth c'.g := hZ.2.2.1 inferInstance
  have : IsProper c'.g := c'.isProper
  have : IsOpenImmersion c'.i := c'.isOpenImmersion
  have : ConnectedSpace c'.Z := IsConnectedCurve.connectedSpace (f := c'.g)
  have : IsLocallyNoetherian c'.Z := LocallyOfFiniteType.isLocallyNoetherian c'.g
  have : IsRegular c'.Z := IsRegular.of_smooth c'.g
  have : IrreducibleSpace c'.Z := IsRegular.irreducibleSpace c'.Z
  have : CompactSpace c'.Z := (quasiCompact_iff_compactSpace c'.g).mp inferInstance
  have : IsNoetherian c'.Z := ⟨⟩
  have hne : (Set.range c'.i.base).Nonempty := by
    have : Nonempty ↥(pullback f b) :=
      (IsConnectedCurve.connectedSpace (f := pullback.snd f b)).toNonempty
    exact Set.range_nonempty _
  have hfin : (Set.range c'.i.base)ᶜ.Finite :=
    c'.i.isOpenEmbedding.isOpen_range.finite_compl_of_topologicalKrullDim_le_one
      (IsCurve.krullDim_le_one (f := c'.g)) hne
  obtain ⟨hs, hk, hq⟩ := Scheme.Hom.pic_restriction_boundary f c
  obtain ⟨hs', hk', hq'⟩ := Scheme.Hom.pic_restriction_boundary (pullback.snd f b) c'
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hfin, hs, hk, hs', hk', ?_⟩
  obtain ⟨G, hG, Λ, hΛ, e, he⟩ := hq P₀ hP₀
  obtain ⟨Q₀, hQ₀, ht⟩ := pic_boundary_base_change_transport (k' := k') f c P₀ hP₀
  obtain ⟨G', hG', Λ', hΛ', e', he'⟩ := hq' Q₀ hQ₀
  obtain ⟨hj, ej, hej⟩ := ht G hG Λ hΛ G' hG' Λ' hΛ'
  have hΛall : Subgroup.map G'.subtype Λ' = Subgroup.closure
      {M | ∃ P Q : closedPoints c'.Z, P.val ∉ Set.range c'.i.base ∧
        Q.val ∉ Set.range c'.i.base ∧
        M = @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' P /
          @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' Q} := by
    rw [hΛ']
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro M ⟨P, hP, rfl⟩
      exact Subgroup.subset_closure ⟨P, Q₀, hP, hQ₀, rfl⟩
    · rw [Subgroup.closure_le]
      rintro M ⟨P, Q, hP, hQ, rfl⟩
      have hPmem := Subgroup.subset_closure (k :=
        {M | ∃ R : closedPoints c'.Z, R.val ∉ Set.range c'.i.base ∧
          M = @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' R /
            @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' Q₀}) ⟨P, hP, rfl⟩
      have hQmem := Subgroup.subset_closure (k :=
        {M | ∃ R : closedPoints c'.Z, R.val ∉ Set.range c'.i.base ∧
          M = @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' R /
            @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' Q₀}) ⟨Q, hQ, rfl⟩
      convert Subgroup.div_mem _ hPmem hQmem using 1
      simp only [SetLike.mem_coe, div_div_div_cancel_right]
  refine ⟨G, hG, Λ, e, G', hG', Λ', e',
    Scheme.Pic.mapHom (pullback.fst c.g b), hj, hΛ, ?_⟩
  intro L
  refine ⟨he L, hΛall, ?_⟩
  intro L'
  refine ⟨he' L', ⟨ej, hej⟩, ?_⟩
  intro M
  refine ⟨rfl, ?_⟩
  intro N
  rw [he', he]
  simp only [Scheme.Pic.mapHom_apply]
  rw [← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp,
    Compactification.baseChange_i_fst]

end AlgebraicGeometry
