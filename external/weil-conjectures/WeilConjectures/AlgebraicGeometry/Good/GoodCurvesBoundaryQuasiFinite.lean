/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The boundary of fibrewise nonempty opens in good curves

Source: Stacks Project, More on Etale Cohomology, Tag 0GKX,
lemma-constant-shriek-rel-dim-1, the second boundary Zprime, using Tag 0GK7
(blueprint: lem-weil-pbc-good-curves-boundary-quasifinite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map to the base from the reduced closed complement of the open union
of the `O i` in the coproduct of the `C i`. The open union is the supremum of the open
images of `u i` followed by the coprojections. Its complement carries the reduced
induced closed structure given by the existing vanishing-ideal construction.
Source: Stacks Project, Tag 0GKX, second boundary Zprime; Tags 01J3 and 01J4
(blueprint: lem-weil-pbc-good-curves-boundary-quasifinite). -/
noncomputable def goodCurvesBoundaryMap
    {I : Type u} (B : Scheme.{u}) (T C O : I → Scheme.{u})
    (t : ∀ i, T i ⟶ B) (b : ∀ i, C i ⟶ T i) (u : ∀ i, O i ⟶ C i)
    [∀ i, IsOpenImmersion (u i)] :
    (Scheme.IdealSheafData.vanishingIdeal
      (⨆ i, (u i ≫ Sigma.ι C i).opensRange).compl).subscheme ⟶ B :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⨆ i, (u i ≫ Sigma.ι C i).opensRange).compl).subschemeι ≫
      Sigma.desc (fun i ↦ b i ≫ t i)

set_option backward.isDefEq.respectTransparency false in
/-- Coproducts of proper maps remain proper over the coproduct of their bases. -/
private theorem proper_sigmaMap
    {I : Type u} (C T : I → Scheme.{u}) (b : ∀ i, C i ⟶ T i)
    [∀ i, IsProper (b i)] : IsProper (Sigma.desc (fun j ↦ b j ≫ Sigma.ι T j)) := by
  have hpb (i : I) : IsPullback (Sigma.ι C i) (b i)
      (Sigma.desc (fun j ↦ b j ≫ Sigma.ι T j)) (Sigma.ι T i) := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback
    · simp
    · ext x
      obtain ⟨k, z, rfl⟩ := (sigmaOpenCover C).exists_eq x
      change (∃ w, Sigma.ι T i w =
        Sigma.desc (fun j ↦ b j ≫ Sigma.ι T j) (Sigma.ι C k z)) ↔
        ∃ w, Sigma.ι C i w = Sigma.ι C k z
      have heq : Sigma.desc (fun j ↦ b j ≫ Sigma.ι T j) (Sigma.ι C k z) =
          Sigma.ι T k (b k z) := by
        rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
        rfl
      rw [heq]
      constructor
      · rintro ⟨w, hw⟩
        have hik : i = k := congrArg Sigma.fst ((sigmaι_eq_iff T i k w (b k z)).mp hw)
        subst k
        exact ⟨z, rfl⟩
      · rintro ⟨w, hw⟩
        have hik : i = k := congrArg Sigma.fst ((sigmaι_eq_iff C i k w z).mp hw)
        subst k
        exact ⟨b i z, rfl⟩
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (sigmaOpenCover T)
  intro i
  change IsProper (pullback.snd (Sigma.desc (fun j ↦ b j ≫ Sigma.ι T j)) (Sigma.ι T i))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)
    (hpb i).isoPullback.hom, (hpb i).isoPullback_hom_snd]
  infer_instance

/-- Source: Stacks Project, Tag 0GKX, the assertion that the second boundary Zprime
is quasi-finite, with the good-curves hypotheses of Tag 0GK7 made explicit
(blueprint: lem-weil-pbc-good-curves-boundary-quasifinite).

Proof plan:
1. Each finite `t i` is proper (lem-weil-pbc-finite-proper), so `b i ≫ t i` is
   proper (lem-weil-pbc-proper-composition).
2. Their finite coproduct is proper: finite type follows by combining finite affine
   covers; separatedness is checked on the pieces `C i ×[B] C j` of the diagonal,
   empty off the equal-index pieces; universal closedness follows from a finite union
   of closed images after any base change (lem-weil-pbc-scheme-coproduct-family).
3. The reduced complement is a closed immersion
   (lem-weil-pbc-reduced-induced-closed-subscheme), hence its map to `B` is proper
   (lem-weil-pbc-closed-immersion-proper). It is separated and of finite type.
   Over the locally Noetherian base it is locally of finite presentation
   (pqf-lem-lft-fp-locnoeth); properness also gives quasi-compactness and a
   quasi-compact diagonal, hence quasi-separatedness.
4. Each fibre of `b i` is proper and smooth over its residue field
   (lem-weil-pbc-proper-base-change, sbc-lem-smooth-criterion). It is Noetherian
   (lem-weil-pbc-finite-type-over-noetherian), and regular by the smooth-field
   criterion applied to the identity field extension
   (lem-weil-pbc-geometric-regularity-smooth-field-criterion). Geometric connectedness
   gives connectedness; nonemptiness and regularity give irreducibility
   (rem-pc-regular-normal). No perfection of the residue field is needed.
5. The open fibre is nonempty. On an irreducible scheme of dimension at most one,
   every point outside it is closed (lem-sc-scheme-sober,
   lem-sc-dim-one-point-outside-open-closed). Its closed complement is finite
   by Noetherianity (lem-sc-noetherian-closed-points-finite). In dimension zero
   the complement is empty.
6. For any point of `B`, each `t i` has a finite fibre (pqf-lem-finite-qf,
   pqf-lem-qf-finitefibres). The boundary fibre is the disjoint union of the finite
   complements from step 5 over these points and over the finite set `I`.
   The fibre homeomorphism (def-pc-scheme-fibre) and the image of the reduced
   closed immersion justify this set-level decomposition; reduction need not commute
   with base change.
7. Finite type and finite fibres imply quasi-finiteness (pqf-lem-qf-finitefibres).
   The other conclusions were obtained in step 3. Empty `I`, `B` or `T i`
   contribute no points and are permitted throughout. -/
theorem good_curves_boundary_quasiFinite
    {I : Type u} [Finite I] (B : Scheme.{u}) [IsLocallyNoetherian B] [CompactSpace B]
    (T C O : I → Scheme.{u})
    (t : ∀ i, T i ⟶ B) (b : ∀ i, C i ⟶ T i) (u : ∀ i, O i ⟶ C i)
    [∀ i, IsFinite (t i)] [∀ i, Etale (t i)]
    [∀ i, Smooth (b i)] [∀ i, IsProper (b i)]
    [∀ i, IsOpenImmersion (u i)]
    (hC : ∀ (i : I) (s : T i), Nonempty ((b i).fiber s) ∧
      GeometricallyConnected ((b i).fiberToSpecResidueField s) ∧
      topologicalKrullDim ((b i).fiber s) ≤ 1)
    (hO : ∀ (i : I) (s : T i), Nonempty ((u i ≫ b i).fiber s)) :
    IsSeparated (goodCurvesBoundaryMap B T C O t b u) ∧
    Scheme.Hom.IsQuasiFinite (goodCurvesBoundaryMap B T C O t b u) ∧
    LocallyOfFinitePresentation (goodCurvesBoundaryMap B T C O t b u) ∧
    QuasiCompact (goodCurvesBoundaryMap B T C O t b u) ∧
    QuasiSeparated (goodCurvesBoundaryMap B T C O t b u) := by
  classical
  let v := Sigma.desc (fun i ↦ b i ≫ Sigma.ι T i)
  have hv : IsProper v := proper_sigmaMap C T b
  have heq : Sigma.desc (fun i ↦ b i ≫ t i) = v ≫ Sigma.desc t := by
    ext i
    simp [v]
  have hp : IsProper (Sigma.desc (fun i ↦ b i ≫ t i)) := by
    rw [heq]
    infer_instance
  have hpZ : IsProper (goodCurvesBoundaryMap B T C O t b u) := by
    unfold goodCurvesBoundaryMap
    infer_instance
  have hfin (i : I) (s : T i) :
      {x : C i | b i x = s ∧ x ∉ Set.range (u i)}.Finite := by
    have hg : GeometricallyConnected ((b i).fiberToSpecResidueField s) := (hC i s).2.1
    have hc : ConnectedSpace ((b i).fiber s) :=
      GeometricallyConnected.connectedSpace_of_subsingleton
        ((b i).fiberToSpecResidueField s)
    have hs : Smooth ((b i).fiberToSpecResidueField s) :=
      (smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField
        (b i)).mp inferInstance |>.2.2 s
    have hl : IsLocallyNoetherian ((b i).fiber s) :=
      LocallyOfFiniteType.isLocallyNoetherian ((b i).fiberToSpecResidueField s)
    have hr : IsRegular ((b i).fiber s) :=
      IsRegular.of_smooth ((b i).fiberToSpecResidueField s)
    have hi : IsIntegral ((b i).fiber s) := IsRegular.isIntegral _
    have hn : IsNoetherian ((b i).fiber s) := ⟨⟩
    let U : Set ((b i).fiber s) := (b i).fiberι s ⁻¹' Set.range (u i)
    have hU : IsOpen U := (u i).isOpenEmbedding.isOpen_range.preimage
      ((b i).fiberι s).continuous
    have hne : U.Nonempty := by
      obtain ⟨o⟩ := hO i s
      have ho : (u i ≫ b i) ((u i ≫ b i).fiberι s o) = s :=
        ((u i ≫ b i).fiberHomeo s o).2
      let x := ((b i).fiberHomeo s).symm
        ⟨u i ((u i ≫ b i).fiberι s o), ho⟩
      refine ⟨x, ?_⟩
      change (b i).fiberι s x ∈ Set.range (u i)
      rw [Scheme.Hom.fiberι_fiberHomeo_symm]
      exact Set.mem_range_self _
    have hE := hU.finite_compl_of_topologicalKrullDim_le_one (hC i s).2.2 hne
    refine (hE.image ((b i).fiberι s)).subset ?_
    intro x (hx : b i x = s ∧ x ∉ Set.range (u i))
    refine ⟨((b i).fiberHomeo s).symm ⟨x, hx.1⟩, ?_, ?_⟩
    · change (b i).fiberι s (((b i).fiberHomeo s).symm ⟨x, hx.1⟩) ∉ Set.range (u i)
      simpa using hx.2
    · exact (b i).fiberι_fiberHomeo_symm s ⟨x, hx.1⟩
  have hfib : ∀ y : B, ((goodCurvesBoundaryMap B T C O t b u) ⁻¹' {y}).Finite := by
    intro y
    let E : Set (∐ C : Scheme.{u}) := ⋃ i, ⋃ s ∈ (t i) ⁻¹' {y},
      (fun x : C i ↦ Sigma.ι C i x) '' {x : C i | b i x = s ∧ x ∉ Set.range (u i)}
    have hE : E.Finite := Set.finite_iUnion fun i ↦
      ((t i).finite_preimage_singleton y).biUnion fun s _ ↦ (hfin i s).image _
    let j := (Scheme.IdealSheafData.vanishingIdeal
      (⨆ i, (u i ≫ Sigma.ι C i).opensRange).compl).subschemeι
    refine (hE.preimage j.isClosedEmbedding.injective.injOn).subset ?_
    intro z hz
    obtain ⟨i, x, hx⟩ := (sigmaOpenCover C).exists_eq (j z)
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨b i x,
      Set.mem_iUnion.mpr ⟨?_, x, ⟨rfl, ?_⟩, hx⟩⟩⟩
    · have hy : goodCurvesBoundaryMap B T C O t b u z = y := hz
      change Sigma.desc (fun i ↦ b i ≫ t i) (j z) = y at hy
      rw [← hx] at hy
      change Sigma.desc (fun i ↦ b i ≫ t i) (Sigma.ι C i x) = y at hy
      rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc] at hy
      exact hy
    · intro hxU
      obtain ⟨o, rfl⟩ := hxU
      have hzU : j z ∉ (⨆ i, (u i ≫ Sigma.ι C i).opensRange :
          (∐ C).Opens) := by
        have hj : Set.range j =
            ((⨆ i, (u i ≫ Sigma.ι C i).opensRange).compl : Set (∐ C : Scheme.{u})) := by
          simp [j]
        have := hj ▸ Set.mem_range_self z
        exact this
      apply hzU
      apply (le_iSup (fun i ↦ (u i ≫ Sigma.ι C i).opensRange) i)
      change j z ∈ Set.range (u i ≫ Sigma.ι C i)
      exact ⟨o, (Scheme.Hom.comp_apply _ _ _).trans hx⟩
  refine ⟨inferInstance, ⟨inferInstance, inferInstance, ?_⟩,
    inferInstance, inferInstance, inferInstance⟩
  intro x
  have hd := (goodCurvesBoundaryMap B T C O t b u).discreteTopology_fiber_and_quasiFiniteAt
    (goodCurvesBoundaryMap B T C O t b u x) (hfib _)
  have : DiscreteTopology ((goodCurvesBoundaryMap B T C O t b u).fiber
      (goodCurvesBoundaryMap B T C O t b u x)) := hd.2.1
  exact isOpen_discrete _

end AlgebraicGeometry
