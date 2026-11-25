/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# The dimension of the source of a morphism with bounded fibres

For a morphism `g : X ⟶ Y` locally of finite type over a locally noetherian scheme, the
codimension of a point `x` is at most the codimension of `g x` plus the dimension of the fibre
through `x` (Stacks `00OM`, the height inequality for a prime lying over another). Consequently,
if all fibres have dimension at most `d`, then `dim X ≤ dim Y + d`, and more generally
`dim g⁻¹(Z) ≤ dim Z + d` for a closed subset `Z ⊆ Y` over which the fibres have dimension at most
`d`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.coheight_le_coheight_add_topologicalKrullDim`: the codimension
  inequality at a point.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le_add`: `dim X ≤ dim Y + d`.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_preimage_le`: `dim g⁻¹(Z) ≤ dim Z + d`.
- `AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_preimage_singleton_le_of_smooth`:
  the fibres of a morphism smooth of relative dimension `d` have dimension at most `d`.
-/

@[expose] public section

open CategoryTheory Order Topology

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- **Codimension along a morphism.** For `g : X ⟶ Y` locally of finite type over a locally
noetherian scheme, the codimension of a point `x` is at most that of `g x` plus the dimension of
the fibre through `x`. On affine neighbourhoods this is the height inequality
`ht 𝔓 ≤ ht 𝔭 + ht (𝔓 / 𝔭B)` (Stacks `00OM`), and the primes of `B / 𝔭B` below `𝔓` all lie over
`𝔭`, so they are points of the fibre. -/
theorem Scheme.Hom.coheight_le_coheight_add_topologicalKrullDim (g : X ⟶ Y)
    [LocallyOfFiniteType g] [IsLocallyNoetherian Y] (x : X) :
    (coheight x : WithBot ℕ∞) ≤ coheight (g x) + topologicalKrullDim (g ⁻¹' {g x}) := by
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show g x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ g ⁻¹ᵁ V from hxV)
  have : IsAffine U := hU
  have : IsAffine V := hV
  have := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherianRing Γ(U, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  have : IsNoetherianRing Γ(V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  let gUV := g.resLE V U hUV
  let x' : (U : Scheme) := ⟨x, hxU⟩
  let s := (U : Scheme).isoSpec.hom x'
  let t := (V : Scheme).isoSpec.hom (gUV x')
  let φ := gUV.appTop
  have hnat : (U : Scheme).isoSpec.hom ≫ Spec.map φ = gUV ≫ (V : Scheme).isoSpec.hom :=
    Scheme.isoSpec_hom_naturality gUV
  have hst : t = Spec.map φ s := by
    simp only [t, s, ← Scheme.Hom.comp_apply, hnat]
  have hgx : V.ι (gUV x') = g x := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
    rfl
  have hcx : coheight x = coheight s := by
    rw [show coheight s = coheight x' from coheight_eq_of_isOpenImmersion _]
    exact coheight_eq_of_isOpenImmersion U.ι (x := x')
  have hcy : coheight (g x) = coheight t := by
    rw [show coheight t = coheight (gUV x') from coheight_eq_of_isOpenImmersion _, ← hgx]
    exact coheight_eq_of_isOpenImmersion V.ι
  let := φ.hom.toAlgebra
  have hts : t.asIdeal = s.asIdeal.comap φ.hom := by rw [hst]; rfl
  have : s.asIdeal.LiesOver t.asIdeal := ⟨hts⟩
  have h := Ideal.height_le_height_add_of_liesOver t.asIdeal s.asIdeal
  rw [hcx, hcy, ← idealHeight_eq_coheight, ← idealHeight_eq_coheight]
  set I := t.asIdeal.map (algebraMap Γ(V, ⊤) Γ(U, ⊤)) with hI
  have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hIs : I ≤ s.asIdeal := Ideal.map_le_iff_le_comap.mpr hts.le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ s.asIdeal := by
    rw [Ideal.mk_ker]; exact hIs
  have hP : (s.asIdeal.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective hmk hker
  let pb : PrimeSpectrum (Γ(U, ⊤) ⧸ I) := ⟨_, hP⟩
  -- the fibre bound
  have key : ((s.asIdeal.map (Ideal.Quotient.mk I)).height : WithBot ℕ∞) ≤
      topologicalKrullDim (g ⁻¹' {g x}) := by
    rw [show s.asIdeal.map (Ideal.Quotient.mk I) = pb.asIdeal from rfl,
      PrimeSpectrum.height_eq_orderHeight, height_eq_krullDim_Iic, topologicalKrullDim]
    -- the point of the fibre attached to a prime below `pb`
    have hmem (q : Set.Iic pb) : g (U.ι ((U : Scheme).isoSpec.inv
        (PrimeSpectrum.comap (Ideal.Quotient.mk I) q.1))) = g x := by
      set Q := PrimeSpectrum.comap (Ideal.Quotient.mk I) q.1
      have hQ : Spec.map φ Q = t := by
        refine PrimeSpectrum.ext ?_
        refine le_antisymm ?_ ?_
        · rw [hts]
          refine Ideal.comap_mono ?_
          have : q.1.asIdeal ≤ pb.asIdeal := q.2
          refine (Ideal.comap_mono this).trans ?_
          rw [Ideal.comap_map_of_surjective' _ hmk, sup_le_iff]
          exact ⟨le_rfl, hker⟩
        · change t.asIdeal ≤ (Q.asIdeal).comap (algebraMap Γ(V, ⊤) Γ(U, ⊤))
          rw [← Ideal.map_le_iff_le_comap]
          change I ≤ Ideal.comap (Ideal.Quotient.mk I) q.1.asIdeal
          exact fun a ha ↦ Ideal.mem_comap.mpr (by
            rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact zero_mem _)
      have hinv : (U : Scheme).isoSpec.inv ≫ gUV = Spec.map φ ≫ (V : Scheme).isoSpec.inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc, hnat, Category.assoc, Iso.hom_inv_id,
          Category.comp_id]
      have e1 : g (U.ι ((U : Scheme).isoSpec.inv Q)) =
          (gUV ≫ V.ι) ((U : Scheme).isoSpec.inv Q) := by
        rw [Scheme.Hom.resLE_comp_ι]; rfl
      have e2 : gUV ((U : Scheme).isoSpec.inv Q) = (V : Scheme).isoSpec.inv (Spec.map φ Q) := by
        rw [← Scheme.Hom.comp_apply, hinv, Scheme.Hom.comp_apply]
      rw [e1, Scheme.Hom.comp_apply, e2, hQ, ← hgx]
      congr 1
      change ((V : Scheme).isoSpec.hom ≫ (V : Scheme).isoSpec.inv) (gUV x') = _
      rw [Iso.hom_inv_id]
      rfl
    let pt (q : Set.Iic pb) : g ⁻¹' {g x} := ⟨_, hmem q⟩
    let C (q : Set.Iic pb) : (TopologicalSpace.IrreducibleCloseds (g ⁻¹' {g x}))ᵒᵈ :=
      OrderDual.toDual ⟨closure {pt q}, isIrreducible_singleton.closure, isClosed_closure⟩
    refine (krullDim_le_of_strictMono C fun a b hab ↦ ?_).trans_eq krullDim_orderDual
    have hspec : pt a ⤳ pt b := by
      refine (IsInducing.subtypeVal.specializes_iff).mp ?_
      change U.ι _ ⤳ U.ι _
      refine Specializes.map (Specializes.map ?_ (Scheme.Hom.continuous _))
        (Scheme.Hom.continuous _)
      rw [← PrimeSpectrum.le_iff_specializes]
      exact Ideal.comap_mono (f := Ideal.Quotient.mk I) (show a.1.asIdeal ≤ b.1.asIdeal from hab.le)
    refine OrderDual.toDual_lt_toDual.mpr ?_
    refine lt_of_le_of_ne (SetLike.coe_subset_coe.mp (show closure {pt b} ⊆ closure {pt a} from
      specializes_iff_closure_subset.mp hspec)) fun heq ↦ hab.ne ?_
    have hcl : closure {pt b} = closure {pt a} := congrArg SetLike.coe heq
    have h1 : pt a = pt b := (inseparable_iff_closure_eq.mpr hcl.symm).eq
    have h2 := congrArg Subtype.val h1
    have h3 := U.ι.isOpenEmbedding.injective h2
    have h4 := (U : Scheme).isoSpec.inv.isOpenEmbedding.injective h3
    exact Subtype.ext (PrimeSpectrum.comap_injective_of_surjective _ hmk h4)
  calc ((s.asIdeal.height : ℕ∞) : WithBot ℕ∞)
      ≤ ((t.asIdeal.height + (s.asIdeal.map (Ideal.Quotient.mk
          (t.asIdeal.map (algebraMap Γ(V, ⊤) Γ(U, ⊤))))).height : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast h
    _ ≤ _ := by
        rw [WithBot.coe_add]
        exact add_le_add le_rfl key

/-- **Dimension of the source.** If the fibres of a morphism `g : X ⟶ Y` locally of finite type
over a locally noetherian scheme have dimension at most `d`, then `dim X ≤ dim Y + d`. -/
theorem Scheme.Hom.topologicalKrullDim_le_add (g : X ⟶ Y) [LocallyOfFiniteType g]
    [IsLocallyNoetherian Y] (d : WithBot ℕ∞) (h : ∀ y, topologicalKrullDim (g ⁻¹' {y}) ≤ d) :
    topologicalKrullDim X ≤ topologicalKrullDim Y + d := by
  let := specializationOrder X
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  exact (g.coheight_le_coheight_add_topologicalKrullDim x).trans
    (add_le_add (coheight_le_topologicalKrullDim _) (h _))

/-- **Dimension of a preimage.** If the fibres of a morphism `f : X ⟶ Y` locally of finite type
over a locally noetherian scheme have dimension at most `d` over a closed subset `Z ⊆ Y`, then
`dim f⁻¹(Z) ≤ dim Z + d`. -/
theorem Scheme.Hom.topologicalKrullDim_preimage_le (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] {Z : Set Y} (hZ : IsClosed Z) (d : WithBot ℕ∞)
    (h : ∀ y ∈ Z, topologicalKrullDim (f ⁻¹' {y}) ≤ d) :
    topologicalKrullDim (f ⁻¹' Z) ≤ topologicalKrullDim Z + d := by
  let J := Scheme.IdealSheafData.vanishingIdeal ⟨Z, hZ⟩
  have hJ : Set.range J.subschemeι = Z := by
    rw [J.range_subschemeι]
    simp [J]
  have := LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
  let P := Limits.pullback f J.subschemeι
  have hP : Set.range (Limits.pullback.fst f J.subschemeι) = f ⁻¹' Z := by
    rw [Scheme.Pullback.range_fst, hJ]
  have hfst := (Limits.pullback.fst f J.subschemeι).isClosedEmbedding.isEmbedding
  rw [← hP, ← hfst.topologicalKrullDim_eq_range, ← hJ,
    ← J.subschemeι.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range]
  refine (Limits.pullback.snd f J.subschemeι).topologicalKrullDim_le_add d fun z ↦ ?_
  refine le_trans ?_ (h (J.subschemeι z) (hJ ▸ Set.mem_range_self z))
  let r : (Limits.pullback.snd f J.subschemeι) ⁻¹' {z} → f ⁻¹' {J.subschemeι z} :=
    fun p ↦ ⟨Limits.pullback.fst f J.subschemeι p.1, by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, Limits.pullback.condition,
        Scheme.Hom.comp_apply, show _ = z from p.2]; rfl⟩
  refine IsInducing.topologicalKrullDim_le (f := r)
    (.of_comp (g := Subtype.val) (by fun_prop) continuous_subtype_val ?_)
  exact hfst.isInducing.comp IsInducing.subtypeVal

/-- The fibres of a morphism smooth of relative dimension `d` have dimension at most `d`. -/
theorem Scheme.Hom.topologicalKrullDim_preimage_singleton_le_of_smooth
    (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f] (y : Y) :
    topologicalKrullDim (f ⁻¹' {y}) ≤ d := by
  rw [← (f.fiberHomeo y).isHomeomorph.topologicalKrullDim_eq]
  have : SmoothOfRelativeDimension d (f.fiberToSpecResidueField y) :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    MorphismProperty.pullback_snd _ _ ‹_›
  exact topologicalKrullDim_le_of_smoothOfRelativeDimension (K := Y.residueField y)
    (f.fiberToSpecResidueField y) d

end AlgebraicGeometry
