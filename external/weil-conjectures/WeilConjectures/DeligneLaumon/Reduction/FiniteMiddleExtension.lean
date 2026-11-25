/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.DeligneLaumon.Reduction.CompactSupport
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.WeilSheaf.CurveEndpoints
public import WeilConjectures.WeilSheaf.Finiteness
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.LowerStarComp
public import WeilConjectures.WeilSheaf.MiddleExtension

/-!
# The finite direct image of a lisse sheaf on a smooth affine curve is a middle extension

Let `C` be a smooth affine curve over `k₀`, not necessarily geometrically connected, let
`f : C ⟶ 𝔸¹_{k₀}` be a finite morphism over `k₀` and `E` a lisse Weil sheaf on `C`. By generic
lissity `f_* E` is lisse on a dense open `j : V ⟶ 𝔸¹`. The preimage `f⁻¹V` is dense in `C`
because `C` has no isolated points, so `E ≅ j'_* j'^* E` for the inclusion `j' : f⁻¹V ⟶ C`
(blueprint: `lemma-boundary-stalk--2`), and with `f' : f⁻¹V ⟶ V` the restriction of `f`,

`f_* E ≅ f_* j'_* j'^* E ≅ (f ∘ j')_* j'^* E = (j ∘ f')_* j'^* E ≅ j_* f'_* j'^* E`.

Hence `R⁰f₀! E ≅ f_* E` is the direct image `j_* H` of the lisse sheaf `H = f'_* j'^* E`, and the
endpoint estimates on `𝔸¹` of `WeilConjectures.WeilSheaf.CurveEndpoints` apply to it.

## Main statements

- `AlgebraicGeometry.dense_preimage_of_isIntegralHom`: the preimage of a nonempty open of a
  smooth irreducible curve under an integral morphism from a smooth curve is dense.
- `AlgebraicGeometry.WeilSheaf.exists_lowerStar_iso_directImage_of_isFinite` and
  `AlgebraicGeometry.WeilSheaf.exists_higherLowerShriek_zero_iso_directImage_of_isFinite`: the
  finite direct image of a lisse sheaf on a smooth affine curve is a middle extension.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_higherLowerShriek_zero`
  and `AlgebraicGeometry.WeilSheaf.isPureOfWeightOver_compactlySupportedCohomology_two_of_isFinite`:
  the endpoint estimates for `R⁰f₀! E` on `𝔸¹`.
-/

@[expose] public section

universe u

open CategoryTheory Topology


namespace AlgebraicGeometry

open scoped ProEtale

section Density

/-- In a scheme smooth of relative dimension one over a field, a point `a` with a proper
specialization `a ⤳ b` has no proper generalization: a chain `η ⤳ a ⤳ b` of distinct points
would give `b` codimension at least two. -/
theorem eq_of_specializes_of_specializes_of_smoothOfRelativeDimension_one {K : Type*} [Field K]
    {Y : Scheme} (q : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 q] {η a b : Y}
    (hηa : η ⤳ a) (hab : a ⤳ b) (hne : a ≠ b) : η = a := by
  by_contra h
  have hfin (y : Y) : Order.coheight y < ⊤ :=
    (coheight_le_of_smoothOfRelativeDimension q 1 y).trans_lt (ENat.natCast_lt_top 1)
  have ha := Order.coheight_strictAnti (⟨hab, fun h' ↦ hne (hab.antisymm h').eq⟩ : b < a)
    (hfin a)
  have hη := Order.coheight_strictAnti (⟨hηa, fun h' ↦ h (hηa.antisymm h').eq⟩ : a < η)
    (hfin η)
  have : Order.coheight a = 0 := Order.lt_one_iff.1
    (by exact_mod_cast ha.trans_le (coheight_le_of_smoothOfRelativeDimension q 1 b))
  rw [this] at hη
  exact not_lt_zero hη

/-- Let `f : X ⟶ Y` be an integral morphism of schemes smooth of relative dimension one over a
field, with `Y` irreducible. Then the preimage of a nonempty open `V ⊆ Y` is dense in `X`. A
nonempty open `W ⊆ X` missing `f⁻¹V` contains a proper specialization `y ⤳ x` (it has dimension
one); its image `f y ⤳ f x` is again proper, the fibres of `f` admitting no proper
specializations, so `f y` is the generic point of `Y`, which lies in `V`. -/
theorem dense_preimage_of_isIntegralHom {K : Type*} [Field K] {X Y : Scheme}
    (p : X ⟶ Spec (.of K)) (q : Y ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 p]
    [SmoothOfRelativeDimension 1 q] [IrreducibleSpace Y] (f : X ⟶ Y) [IsIntegralHom f]
    {V : Set Y} (hV : IsOpen V) (hne : V.Nonempty) : Dense (f.base ⁻¹' V) := by
  rw [dense_iff_inter_open]
  intro W hW ⟨x₀, hx₀⟩
  by_contra hWV
  let W' : X.Opens := ⟨W, hW⟩
  have : Nonempty W' := ⟨⟨x₀, hx₀⟩⟩
  have : SmoothOfRelativeDimension 1 (W'.ι ≫ p) := by
    rw [show 1 = 0 + 1 from rfl]
    infer_instance
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (W'.ι ≫ p) 1
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints] at hdim
  obtain ⟨a, b, hba, hab⟩ := Order.krullDim_pos_iff.1 (by rw [hdim]; exact zero_lt_one)
  have hyx : f (W'.ι b) ⤳ f (W'.ι a) := (hba.map W'.ι.continuous).map f.continuous
  have hne' : f (W'.ι b) ≠ f (W'.ι a) := fun h ↦ hab (by
    obtain rfl := W'.ι.isOpenEmbedding.injective
      (f.eq_of_specializes_of_apply_eq_of_isIntegralHom (hba.map W'.ι.continuous) h)
    exact specializes_rfl)
  have hη := eq_of_specializes_of_specializes_of_smoothOfRelativeDimension_one q
    ((genericPoint_spec Y).specializes (Set.mem_univ _)) hyx hne'
  have hηV : genericPoint Y ∈ V := ((genericPoint_spec Y).mem_open_set_iff hV).2 (by simpa)
  exact hWV ⟨W'.ι b, by simp [W'], by rw [Set.mem_preimage, ← hη]; exact hηV⟩

end Density

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The affine line over a field is a Noetherian scheme. -/
instance AffineSpace.isNoetherian_affineLine (K : Type u) [Field K] :
    IsNoetherian 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of K)) :=
  have := LocallyOfFiniteType.isLocallyNoetherian (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of K)) ↘
    Spec (CommRingCat.of K))
  {}

namespace WeilSheaf

variable {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]

/-- The composition isomorphism `ψ_* φ_* F ≅ (φ ≫ ψ)_* F` of pushforwards of Weil sheaves. -/
noncomputable def lowerStarCompObjIso (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ] [QuasiCompact ψ]
    [QuasiSeparated ψ] [LocallyOfFiniteType ψ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) :
    (lowerStar ψ).obj ((lowerStar φ).obj F) ≅ (lowerStar (φ ≫ ψ)).obj F :=
  ObjectProperty.isoMk _ ((ProEtaleWeilSheaf.lowerStarCompIso k₀ l φ ψ).app F.obj)

/-- The pushforward of Weil sheaves only depends on the morphism. -/
noncomputable def lowerStarCongrObjIso {φ φ' : X ⟶ Y} (h : φ = φ')
    [φ.IsOver (Spec (CommRingCat.of k₀))] [φ'.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ] [QuasiCompact φ']
    [QuasiSeparated φ'] [LocallyOfFiniteType φ']
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) :
    (lowerStar φ).obj F ≅ (lowerStar φ').obj F := by
  subst h
  exact Iso.refl _

/-- For a proper morphism `φ` the degree-zero direct image with compact support `R⁰φ₀! F` is
the direct image `φ_* F` (blueprint: `prop-functor-package`, clause 3). -/
noncomputable def higherLowerShriekZeroObjIsoLowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [IsProper φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l X) :
    (higherLowerShriek k₀ l φ 0).obj F ≅ (lowerStar φ).obj F :=
  (WeilComplex.homologySheaf 0).mapIso
      (WeilComplex.derivedLowerShriekObjIsoDerivedLowerStar φ (toComplex.obj F)) ≪≫
    homologySheafZeroDerivedLowerStarIso φ F

/-- **The finite direct image of a lisse sheaf on a smooth affine curve is a middle extension.**
Let `C` be a smooth affine curve over `k₀`, `f : C ⟶ 𝔸¹_{k₀}` a finite morphism over `k₀` and `E`
a lisse Weil sheaf on `C`. There are a dense open `V ⊆ 𝔸¹` and a lisse Weil sheaf `H` on `V` with
`f_* E ≅ j_* H` for the inclusion `j : V ⟶ 𝔸¹`; if `E` is punctually `ι`-pure of weight `w`, then
so is `H`. Here `V` is a lisse locus of `f_* E`, and `H = f'_* j'^* E` for the restriction
`f' : f⁻¹V ⟶ V` of `f` and the inclusion `j' : f⁻¹V ⟶ C`, using `E ≅ j'_* j'^* E`
(blueprint: `lemma-boundary-stalk--2`). -/
theorem exists_lowerStar_iso_directImage_of_isFinite {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    (f : C ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))) [IsFinite f]
    [f.IsOver (Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C) (hE : E.IsLisse) :
    ∃ (V : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))).Opens)
      (_ : Dense (V : Set 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))))
      (H : WeilSheaf k₀ l V), H.IsLisse ∧
      Nonempty ((lowerStar f).obj E ≅ (directImage V.ι).obj H) ∧
      ∀ (ι : PadicAlgCl l →+* ℂ) (w : ℝ), E.IsPunctuallyPureOfWeight ι w →
        H.IsPunctuallyPureOfWeight ι w := by
  have := SmoothOfRelativeDimension.smooth 1 (C ↘ Spec (CommRingCat.of k₀))
  have : IsNoetherian C :=
    have := LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k₀))
    {}
  have hA := AffineSpace.smoothOfRelativeDimension_one_of_isOpenImmersion
    (k := k₀) (𝟙 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))
  rw [Category.id_comp] at hA
  obtain ⟨V, hV, hlis⟩ := exists_dense_isLisse_upperStar ((lowerStar f).obj E)
  have hff : f ∣_ V ≫ V.ι = (f ⁻¹ᵁ V).ι ≫ f := morphismRestrict_ι f V
  have : (f ∣_ V).IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    rw [← comp_over V.ι, morphismRestrict_ι_assoc, comp_over f, comp_over (f ⁻¹ᵁ V).ι]⟩
  have hdense : Dense (Set.range (f ⁻¹ᵁ V).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact dense_preimage_of_isIntegralHom (C ↘ Spec (CommRingCat.of k₀))
      (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)) f V.isOpen
      hV.nonempty
  obtain ⟨eE⟩ := IsLisse.nonempty_iso_directImage_upperStar (f ⁻¹ᵁ V).ι hdense hE
  let H := (lowerStar (f ∣_ V)).obj ((upperStar (f ⁻¹ᵁ V).ι).obj E)
  let e : (lowerStar f).obj E ≅ (directImage V.ι).obj H :=
    (lowerStar f).mapIso eE ≪≫ lowerStarCompObjIso (f ⁻¹ᵁ V).ι f _ ≪≫
      lowerStarCongrObjIso hff.symm _ ≪≫ (lowerStarCompObjIso (f ∣_ V) V.ι _).symm
  refine ⟨V, hV, H, ?_, ⟨e⟩, fun ι w hw ↦ ?_⟩
  · have h₂ : ((upperStar V.ι).obj ((directImage V.ι).obj H)).IsLisse :=
      hlis.of_iso ((upperStar V.ι).mapIso e)
    have h₃ : ProEtale.IsAdicLisseSheaf
        ((Scheme.Hom.geometricFiberMap V.ι (comp_over V.ι _))^*ᵃ[l].obj
          ((Scheme.Hom.geometricFiberMap V.ι (comp_over V.ι _))_*ᵃ[l].obj H.obj.carrier)) := h₂
    exact ProEtale.IsAdicLisseSheaf.of_iso
      (asIso ((ProEtale.adicUpperStarLowerStarAdjunction l
        (Scheme.Hom.geometricFiberMap V.ι (comp_over V.ι _))).counit.app H.obj.carrier)) h₃
  · have : QuasiCompact (V.toScheme ↘ Spec (CommRingCat.of k₀)) := by
      rw [← comp_over V.ι]
      infer_instance
    exact IsPunctuallyPureOfWeight.of_mono (higherLowerShriekZeroObjIsoLowerStar (f ∣_ V) _).inv
      ((hw.upperStar (f ⁻¹ᵁ V).ι).higherLowerShriek_zero_of_quasiFinite (f ∣_ V))

/-- **The degree-zero direct image with compact support of a lisse sheaf along a finite morphism
to the affine line is a middle extension.** For `f` and `E` as in
`AlgebraicGeometry.WeilSheaf.exists_lowerStar_iso_directImage_of_isFinite`, there are a dense
open `V ⊆ 𝔸¹` and a lisse Weil sheaf `H` on `V` with `R⁰f₀! E ≅ j_* H`, `f` being proper; if `E`
is punctually `ι`-pure of weight `w`, then so is `H`. -/
theorem exists_higherLowerShriek_zero_iso_directImage_of_isFinite {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    (f : C ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))) [IsFinite f]
    [f.IsOver (Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C) (hE : E.IsLisse) :
    ∃ (V : (𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))).Opens)
      (_ : Dense (V : Set 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))) (H : WeilSheaf k₀ l V),
      H.IsLisse ∧ Nonempty ((higherLowerShriek k₀ l f 0).obj E ≅ (directImage V.ι).obj H) ∧
      ∀ (ι : PadicAlgCl l →+* ℂ) (w : ℝ), E.IsPunctuallyPureOfWeight ι w →
        H.IsPunctuallyPureOfWeight ι w := by
  obtain ⟨V, hV, H, hH, ⟨e⟩, hpure⟩ := exists_lowerStar_iso_directImage_of_isFinite f E hE
  exact ⟨V, hV, H, hH, ⟨higherLowerShriekZeroObjIsoLowerStar f E ≪≫ e⟩, hpure⟩

/-- **Vanishing of `H_c^0` of a finite direct image on the affine line.** For a finite morphism
`f : C ⟶ 𝔸¹_{k₀}` over `k₀` from a smooth affine curve and a lisse Weil sheaf `E` on `C`,
`H_c^0(𝔸¹, R⁰f₀! E) = 0`: `R⁰f₀! E` is the middle extension `j_* H` of a lisse sheaf on a dense
open of the smooth geometrically connected affine curve `𝔸¹`
(`AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero`). -/
theorem subsingleton_compactlySupportedCohomology_higherLowerShriek_zero {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    (f : C ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))) [IsFinite f]
    [f.IsOver (Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C) (hE : E.IsLisse) :
    Subsingleton (((higherLowerShriek k₀ l f 0).obj E).compactlySupportedCohomology 0).carrier := by
  obtain ⟨V, hV, H, hH, ⟨e⟩, -⟩ := exists_higherLowerShriek_zero_iso_directImage_of_isFinite f E hE
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have hA := AffineSpace.smoothOfRelativeDimension_one_of_isOpenImmersion
    (k := k₀) (𝟙 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))
  have hA' := AffineSpace.geometricallyConnected_of_isOpenImmersion
    (k := k₀) (𝟙 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))
  rw [Category.id_comp] at hA hA'
  have h := subsingleton_compactlySupportedCohomology_directImage_zero V.ι H hH
  obtain ⟨e'⟩ := nonempty_equiv_compactlySupportedCohomology_of_iso e 0
  exact e'.toLinearEquiv.toEquiv.subsingleton

/-- **Purity of `H_c^2` of a finite direct image on the affine line.** For a finite morphism
`f : C ⟶ 𝔸¹_{k₀}` over `k₀` from a smooth affine curve and a lisse Weil sheaf `E` on `C`,
punctually `ι`-pure of weight `0`, `H_c^2(𝔸¹, R⁰f₀! E)` is `ι`-pure of weight `2`: `R⁰f₀! E` is
the middle extension `j_* H` of a lisse sheaf on a dense open of `𝔸¹`, punctually pure of
weight `0`
(`AlgebraicGeometry.isPureOfWeightOver_compactlySupportedCohomology_directImage_two`). -/
theorem isPureOfWeightOver_compactlySupportedCohomology_two_of_isFinite
    (ι : PadicAlgCl l →+* ℂ) {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k₀))] [IsAffine C]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    (f : C ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀))) [IsFinite f]
    [f.IsOver (Spec (CommRingCat.of k₀))] (E : WeilSheaf k₀ l C) (hE : E.IsLisse)
    (hpure : E.IsPunctuallyPureOfWeight ι 0) :
    (((higherLowerShriek k₀ l f 0).obj E).compactlySupportedCohomology 2).IsPureOfWeightOver
      k₀ ι 2 := by
  obtain ⟨V, hV, H, hH, ⟨e⟩, hHpure⟩ :=
    exists_higherLowerShriek_zero_iso_directImage_of_isFinite f E hE
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have hA := AffineSpace.smoothOfRelativeDimension_one_of_isOpenImmersion
    (k := k₀) (𝟙 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))
  have hA' := AffineSpace.geometricallyConnected_of_isOpenImmersion
    (k := k₀) (𝟙 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k₀)))
  rw [Category.id_comp] at hA hA'
  have h := isPureOfWeightOver_compactlySupportedCohomology_directImage_two V.ι H ι hH
    (hHpure ι 0 hpure)
  rw [zero_add] at h
  obtain ⟨e'⟩ := nonempty_equiv_compactlySupportedCohomology_of_iso e 2
  exact FrobeniusModule.IsPureOfWeight.of_equiv e' h

end WeilSheaf

end AlgebraicGeometry
