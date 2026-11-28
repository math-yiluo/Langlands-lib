import Langlands.AlgebraicGeometry.HenselianBirationalSolution.ChartCocycle
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict

/-! # Gluing the translates of `Y`

For a family `τ : ι → Translation m`, copies of `Y` indexed by `ι` are glued along the transition
maps `chartTrans (τ i) (τ j)`: a point `x` of the `i`-th copy lying in `chartOverlap (τ i) (τ j)`
is identified with the point `chartTrans (τ i) (τ j) x` of the `j`-th copy. The `i`-th copy is
thought of as the translate `τ i (Y)`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

open P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict.AlgebraicGeometry.Scheme.GlueData
  (MkCore)

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

variable {S Y : Scheme.{u}} {g : Y ⟶ S} {m : BirationalGroupLaw g}
  [IsReduced Y] [Smooth g] [IsSeparated g] [IsNoetherian Y] [Surjective g] [QuasiCompact g]
  (H : GlueHyp m) {ι : Type u} (τ : ι → Translation m)

namespace Glue

/-- The overlap of the `i`-th and `j`-th charts, in the `i`-th chart. -/
abbrev V (i j : ι) : Y.Opens := Translation.chartOverlap (τ i) (τ j) H

/-- The transition map from the `i`-th to the `j`-th chart. -/
abbrev ψ (i j : ι) : (V H τ i j).toScheme ⟶ Y := Translation.chartTrans (τ i) (τ j) H

theorem range_ψ (i j : ι) : Set.range (ψ H τ i j) ⊆ Set.range (V H τ j i).ι := by
  rw [Scheme.Opens.range_ι, Translation.range_chartTrans_eq]

/-- The transition map as a map of overlaps. -/
def t (i j : ι) : (V H τ i j).toScheme ⟶ (V H τ j i).toScheme :=
  IsOpenImmersion.lift _ _ (range_ψ H τ i j)

@[reassoc (attr := simp)]
theorem t_ι (i j : ι) : t H τ i j ≫ (V H τ j i).ι = ψ H τ i j :=
  IsOpenImmersion.lift_fac _ _ _

theorem t_inter (i j k : ι) :
    (V H τ i j).ι ⁻¹ᵁ (V H τ i k) ≤ t H τ i j ⁻¹ᵁ ((V H τ j i).ι ⁻¹ᵁ (V H τ j k)) := by
  intro x hx
  change (V H τ j i).ι (t H τ i j x) ∈ V H τ j k
  rw [← Scheme.Hom.comp_apply, t_ι]
  let w : (Translation.commonOverlap (τ i) (τ j) (τ k) H).toScheme :=
    ⟨(V H τ i j).ι x, x.2, hx⟩
  have hw : Y.homOfLE (inf_le_left : Translation.commonOverlap (τ i) (τ j) (τ k) H ≤ _) w =
      x := by
    apply (V H τ i j).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  have := Translation.cocA_mem (τ i) (τ j) (τ k) H w
  rwa [Translation.cocA, Scheme.Hom.comp_apply, hw] at this

theorem cocycle (i j k : ι) :
    (t H τ i j).resLE ((V H τ j i).ι ⁻¹ᵁ (V H τ j k)) ((V H τ i j).ι ⁻¹ᵁ (V H τ i k))
        (t_inter H τ i j k) ≫
      (Y.restrictRestrictComm (V H τ j i) (V H τ j k)).hom ≫
        ((V H τ j k).ι ⁻¹ᵁ (V H τ j i)).ι ≫ t H τ j k ≫ (V H τ k j).ι =
    (Y.restrictRestrictComm (V H τ i j) (V H τ i k)).hom ≫
      ((V H τ i k).ι ⁻¹ᵁ (V H τ i j)).ι ≫ t H τ i k ≫ (V H τ k i).ι := by
  have hσ : (Y.restrictRestrictComm (V H τ i j) (V H τ i k)).hom ≫
      ((V H τ i k).ι ⁻¹ᵁ (V H τ i j)).ι ≫ (V H τ i k).ι =
        ((V H τ i j).ι ⁻¹ᵁ (V H τ i k)).ι ≫ (V H τ i j).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hσ' : (Y.restrictRestrictComm (V H τ j i) (V H τ j k)).hom ≫
      ((V H τ j k).ι ⁻¹ᵁ (V H τ j i)).ι ≫ (V H τ j k).ι =
        ((V H τ j i).ι ⁻¹ᵁ (V H τ j k)).ι ≫ (V H τ j i).ι :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  obtain ⟨y, hy1, hy2⟩ := Translation.chartCocycle (τ i) (τ j) (τ k) H
    ((V H τ i j).ι ⁻¹ᵁ (V H τ i k)).ι
    ((Y.restrictRestrictComm (V H τ i j) (V H τ i k)).hom ≫
      ((V H τ i k).ι ⁻¹ᵁ (V H τ i j)).ι)
    (by rw [Category.assoc, hσ])
  have hr : (t H τ i j).resLE ((V H τ j i).ι ⁻¹ᵁ (V H τ j k)) ((V H τ i j).ι ⁻¹ᵁ (V H τ i k))
        (t_inter H τ i j k) ≫
      (Y.restrictRestrictComm (V H τ j i) (V H τ j k)).hom ≫
        ((V H τ j k).ι ⁻¹ᵁ (V H τ j i)).ι = y := by
    rw [← cancel_mono (V H τ j k).ι, hy1, Category.assoc, Category.assoc, hσ',
      Scheme.Hom.resLE_comp_ι_assoc, t_ι]
  calc _ = ((t H τ i j).resLE ((V H τ j i).ι ⁻¹ᵁ (V H τ j k))
          ((V H τ i j).ι ⁻¹ᵁ (V H τ i k)) (t_inter H τ i j k) ≫
        (Y.restrictRestrictComm (V H τ j i) (V H τ j k)).hom ≫
          ((V H τ j k).ι ⁻¹ᵁ (V H τ j i)).ι) ≫ (t H τ j k ≫ (V H τ k j).ι) := by
        simp only [Category.assoc]
    _ = y ≫ ψ H τ j k := by rw [hr, t_ι]
    _ = _ := by
        rw [hy2]
        have := t_ι H τ i k
        simp only [ψ] at this
        rw [← this, Category.assoc]

/-- The gluing datum. -/
def core : MkCore.{u} where
  J := ι
  U _ := Y
  V := V H τ
  t := t H τ
  V_id i := Translation.chartOverlap_self (τ i) H
  t_id i := by
    rw [← cancel_mono (V H τ i i).ι, t_ι, Category.id_comp]
    exact Translation.chartTrans_self (τ i) H
  t_inter := t_inter H τ
  cocycle := cocycle H τ

/-- The glued scheme. -/
abbrev glued : Scheme.{u} := (core H τ).glueData.glued

/-- The `i`-th chart `Y ⟶ glued`. -/
abbrev chart (i : ι) : Y ⟶ glued H τ := (core H τ).glueData.ι i

instance (i : ι) : IsOpenImmersion (chart H τ i) :=
  Scheme.GlueData.ι_isOpenImmersion (core H τ).glueData i

/-- Gluing condition: `x` in the `i`-th chart is `ψ i j x` in the `j`-th chart. -/
@[reassoc]
theorem ψ_chart (i j : ι) : ψ H τ i j ≫ chart H τ j = (V H τ i j).ι ≫ chart H τ i := by
  rw [← t_ι, Category.assoc]
  exact MkCore.t_ι_ι (core H τ) i j

theorem preimage_chart (i j : ι) : chart H τ i ⁻¹ᵁ (chart H τ j).opensRange = V H τ i j :=
  MkCore.preimage_opensRange (core H τ) i j

theorem exists_chart (x : glued H τ) : ∃ i y, chart H τ i y = x :=
  (core H τ).glueData.ι_jointly_surjective x

theorem desc_cond {Z : Scheme.{u}} (f : ι → (Y ⟶ Z))
    (hf : ∀ i j, (V H τ i j).ι ≫ f i = ψ H τ i j ≫ f j) (i j : ι) :
    (V H τ i j).ι ≫ f i = (t H τ i j ≫ (V H τ j i).ι) ≫ f j := by
  rw [t_ι]
  exact hf i j

/-- Morphisms out of the glued scheme from compatible morphisms on the charts. -/
def desc {Z : Scheme.{u}} (f : ι → (Y ⟶ Z))
    (hf : ∀ i j, (V H τ i j).ι ≫ f i = ψ H τ i j ≫ f j) : glued H τ ⟶ Z :=
  Multicoequalizer.desc (core H τ).glueData.diagram Z f
    (fun ij => desc_cond H τ f hf ij.1 ij.2)

@[reassoc (attr := simp)]
theorem chart_desc {Z : Scheme.{u}} (f : ι → (Y ⟶ Z))
    (hf : ∀ i j, (V H τ i j).ι ≫ f i = ψ H τ i j ≫ f j) (i : ι) :
    chart H τ i ≫ desc H τ f hf = f i :=
  Multicoequalizer.π_desc _ _ _ _ _

theorem hom_ext {Z : Scheme.{u}} {f₁ f₂ : glued H τ ⟶ Z}
    (h : ∀ i, chart H τ i ≫ f₁ = chart H τ i ≫ f₂) : f₁ = f₂ :=
  Multicoequalizer.hom_ext _ _ _ h

/-- Two points of charts with the same image in the glued scheme are related by a transition
map. -/
theorem exists_of_chart_eq {T : Scheme.{u}} (i j : ι) (a b : T ⟶ Y)
    (hab : a ≫ chart H τ i = b ≫ chart H τ j) :
    ∃ w : T ⟶ (V H τ i j).toScheme, w ≫ (V H τ i j).ι = a ∧ w ≫ ψ H τ i j = b := by
  have hl := (core H τ).glueData.vPullbackConeIsLimit i j
  refine ⟨PullbackCone.IsLimit.lift hl a b hab, ?_, ?_⟩
  · exact PullbackCone.IsLimit.lift_fst hl a b hab
  · have := PullbackCone.IsLimit.lift_snd hl a b hab
    rw [← t_ι]
    exact this

/-- The structure morphism of the glued scheme. -/
def toBase : glued H τ ⟶ S :=
  desc H τ (fun _ => g) (fun i j => (Translation.chartTrans_comp_g (τ i) (τ j) H).symm)

@[reassoc (attr := simp)]
theorem chart_toBase (i : ι) : chart H τ i ≫ toBase H τ = g :=
  chart_desc _ _ _ _ i

set_option backward.isDefEq.respectTransparency false in
instance : Smooth (toBase H τ) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth) (core H τ).glueData.openCover
  intro i
  change Smooth (chart H τ i ≫ toBase H τ)
  rw [chart_toBase]
  infer_instance

instance : IsLocallyNoetherian (glued H τ) := by
  rw [isLocallyNoetherian_iff_openCover (core H τ).glueData.openCover]
  intro i
  change IsLocallyNoetherian Y
  infer_instance

end Glue

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
