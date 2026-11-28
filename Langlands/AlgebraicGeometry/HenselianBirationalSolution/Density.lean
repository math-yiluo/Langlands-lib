import Langlands.AlgebraicGeometry.FibreDenseOpenPullback
import Langlands.AlgebraicGeometry.FibreGenericPoints
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Density in the fibres of a morphism

Elementary properties of `FibreGenerizationDense`: generizations inside fibres lift along every
base change, so fibrewise density is stable under base change; it is stable under finite
intersections of open sets and under preimages by open immersions over the base.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

noncomputable section

namespace Langlands.AlgebraicGeometry.HenselianBirationalSolution

/-- A morphism of fields is flat. -/
theorem flat_specMap_of_field {K L : CommRingCat.{u}} (hK : IsField K) (φ : K ⟶ L) :
    Flat (Spec.map φ) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  let := hK.toField
  let := φ.hom.toAlgebra
  change Module.Flat K L
  infer_instance

/-- Generizations inside a fibre lift along any base change: in a pullback square, a generization
`y` of `fst x'` in the fibre of `f` through `fst x'` is the image of a generization of `x'` in the
fibre of `snd` through `x'`. -/
theorem exists_generization_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x' : P) (y : X)
    (hy : y ⤳ fst x') (hfy : f y = f (fst x')) :
    ∃ y' : P, y' ⤳ x' ∧ fst y' = y ∧ snd y' = snd x' := by
  set y₀ := snd x' with hy₀
  have hpb := isPullback_fiberToSpecResidueField_of_isPullback h y₀
  have hφι0 : ∀ e₁ e₂, pullback.map snd (Y.fromSpecResidueField y₀) f
      (Z.fromSpecResidueField (g y₀)) fst (Spec.map (g.residueFieldMap y₀)) g e₁ e₂ ≫
      f.fiberι (g y₀) = snd.fiberι y₀ ≫ fst := fun _ _ => pullback.lift_fst _ _ _
  set φ : snd.fiber y₀ ⟶ f.fiber (g y₀) := pullback.map snd (Y.fromSpecResidueField y₀) f
      (Z.fromSpecResidueField (g y₀)) fst (Spec.map (g.residueFieldMap y₀)) g h.w.symm
      (by simp) with hφdef
  have hφι : φ ≫ f.fiberι (g y₀) = snd.fiberι y₀ ≫ fst := hφι0 _ _
  have hflat : Flat (Spec.map (g.residueFieldMap y₀)) :=
    flat_specMap_of_field (Field.toIsField (Z.residueField (g y₀))) _
  have : Flat φ := MorphismProperty.of_isPullback hpb.flip hflat
  have hgen : GeneralizingMap φ := Flat.generalizingMap φ
  -- the point `x'` in its fibre
  let x₁ : snd.fiber y₀ := snd.asFiber x'
  have hx₁ : snd.fiberι y₀ x₁ = x' := snd.fiberι_asFiber x'
  -- the point `y` in the fibre of `f` over `g y₀`
  have hfx : f (fst x') = g y₀ := by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  have hyfib : y ∈ f ⁻¹' {g y₀} := by simpa [hfx] using hfy
  let y₁ : f.fiber (g y₀) := (f.fiberHomeo (g y₀)).symm ⟨y, hyfib⟩
  have hy₁ : f.fiberι (g y₀) y₁ = y := f.fiberι_fiberHomeo_symm _ _
  have hφx₁ : f.fiberι (g y₀) (φ x₁) = fst x' := by
    rw [← Scheme.Hom.comp_apply, hφι, Scheme.Hom.comp_apply, hx₁]
  have hspec : y₁ ⤳ φ x₁ := by
    rw [← (f.fiberι (g y₀)).isEmbedding.specializes_iff, hy₁, hφx₁]
    exact hy
  obtain ⟨z, hz, hφz⟩ := hgen hspec
  refine ⟨snd.fiberι y₀ z, ?_, ?_, ?_⟩
  · rw [← hx₁]
    exact hz.map (snd.fiberι y₀).continuous
  · rw [← Scheme.Hom.comp_apply, ← hφι, Scheme.Hom.comp_apply, hφz, hy₁]
  · exact (snd.fiberHomeo y₀ z).2

/-- Fibrewise density is stable under base change, for the canonical pullback. -/
theorem fibreGenerizationDense_pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    {W : Set X} (hW : FibreGenerizationDense f W) :
    FibreGenerizationDense (pullback.snd f g) (pullback.fst f g ⁻¹' W) :=
  FibreGenerizationDense.preimage_of_isPullback (IsPullback.of_hasPullback f g) hW

/-- The intersection of an open fibrewise dense set with a fibrewise dense set is fibrewise
dense. -/
theorem FibreGenerizationDense.inter {X S : Scheme.{u}} {q : X ⟶ S} {W₁ W₂ : Set X}
    (h₁ : FibreGenerizationDense q W₁) (h₂ : FibreGenerizationDense q W₂) (hW₁ : IsOpen W₁) :
    FibreGenerizationDense q (W₁ ∩ W₂) := by
  intro x
  obtain ⟨y, hy, hqy, hyx⟩ := h₁ x
  obtain ⟨z, hz, hqz, hzy⟩ := h₂ y
  exact ⟨z, ⟨hW₁.stableUnderGeneralization hzy hy, hz⟩, hqz.trans hqy, hzy.trans hyx⟩

/-- Fibrewise density is monotone. -/
theorem FibreGenerizationDense.mono {X S : Scheme.{u}} {q : X ⟶ S} {W₁ W₂ : Set X}
    (h : FibreGenerizationDense q W₁) (hle : W₁ ⊆ W₂) : FibreGenerizationDense q W₂ := by
  intro x
  obtain ⟨y, hy, hqy, hyx⟩ := h x
  exact ⟨y, hle hy, hqy, hyx⟩

/-- The whole space is fibrewise dense. -/
theorem fibreGenerizationDense_univ {X S : Scheme.{u}} (q : X ⟶ S) :
    FibreGenerizationDense q Set.univ :=
  fun x => ⟨x, trivial, rfl, specializes_rfl⟩

/-- Preimages of fibrewise dense sets under open immersions over the base are fibrewise dense. -/
theorem FibreGenerizationDense.preimage_of_isOpenImmersion {X X' S : Scheme.{u}}
    {q : X ⟶ S} {q' : X' ⟶ S} (e : X' ⟶ X) [IsOpenImmersion e] (he : e ≫ q = q')
    {W : Set X} (hW : FibreGenerizationDense q W) : FibreGenerizationDense q' (e ⁻¹' W) := by
  intro x
  obtain ⟨y, hyW, hqy, hyx⟩ := hW (e x)
  have hyr : y ∈ Set.range e :=
    e.isOpenEmbedding.isOpen_range.stableUnderGeneralization hyx ⟨x, rfl⟩
  obtain ⟨x', rfl⟩ := hyr
  refine ⟨x', hyW, ?_, (e.isOpenEmbedding.toIsEmbedding.specializes_iff).mp hyx⟩
  rw [← he, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hqy]

/-- A fibrewise dense set meets every nonempty fibre. -/
theorem FibreGenerizationDense.exists_mem {X S : Scheme.{u}} {q : X ⟶ S} {W : Set X}
    (h : FibreGenerizationDense q W) (x : X) : ∃ y ∈ W, q y = q x := by
  obtain ⟨y, hy, hqy, -⟩ := h x
  exact ⟨y, hy, hqy⟩

/-- If `W` is fibrewise dense and the preimage of `D` is dense, then `W` meets that preimage in a
dense set, provided `W` is open. -/
theorem FibreGenerizationDense.dense_inter_preimage {X S : Scheme.{u}} {q : X ⟶ S} {W : Set X}
    (h : FibreGenerizationDense q W) {D : Set S} (hD : Dense (q ⁻¹' D)) :
    Dense (W ∩ q ⁻¹' D) := by
  rw [dense_iff_inter_open]
  intro N hN ⟨x, hx⟩
  obtain ⟨z, hzN, hzD⟩ := hD.inter_open_nonempty N hN ⟨x, hx⟩
  obtain ⟨y, hyW, hqy, hyz⟩ := h z
  refine ⟨y, hN.stableUnderGeneralization hyz hzN, hyW, ?_⟩
  change q y ∈ D
  rw [hqy]
  exact hzD

end Langlands.AlgebraicGeometry.HenselianBirationalSolution
