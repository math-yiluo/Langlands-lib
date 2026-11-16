import Langlands.GroupScheme.Descent.FiniteCoefficientHomModel
import Langlands.GroupScheme.Reductive.DirectLimitReductiveStatement
import Langlands.GroupScheme.NormalQuotientReductiveGluing
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleDescentBridge
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone

/-! # Reductive monomorphisms over finite coefficient rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of A))} {f : G ⟶ H}

private theorem inclusion_spec_comp (B C : Subalgebra R A) (hBC : B ≤ C) :
    Spec.algebraMap C A ≫
        Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hBC).toRingHom) =
      Spec.algebraMap B A := by
  rw [Spec.algebraMap, Spec.algebraMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- Enlarge along the actual inclusion into any finite coefficient subalgebra. -/
def SimultaneousHomModel.enlargeTo (D : SimultaneousHomModel R A f)
    (C : Subalgebra R A) (hC : C.FG) (hDC : D.coefficients ≤ C) : SimultaneousHomModel R A f where
  coefficients := C
  finite := hC
  source := (baseChange
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom))).obj D.source
  target := (baseChange
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom))).obj D.target
  sourceAffine := by
    let := D.sourceAffine
    change IsAffineHom (pullback.snd D.source.X.hom _)
    infer_instance
  sourceSmooth := by
    let := D.sourceSmooth
    change Smooth (pullback.snd D.source.X.hom _)
    infer_instance
  targetSeparated := by
    let := D.targetSeparated
    change IsSeparated (pullback.snd D.target.X.hom _)
    infer_instance
  targetFinitePresentation := by
    let := D.targetFinitePresentation
    change LocallyOfFinitePresentation (pullback.snd D.target.X.hom _)
    infer_instance
  targetQuasiCompact := by
    let := D.targetQuasiCompact
    change QuasiCompact (pullback.snd D.target.X.hom _)
    infer_instance
  hom := (baseChange
    (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom))).map D.hom
  sourceIso := D.sourceIso ≪≫
    (pullbackComparison
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom))
      (Spec.algebraMap C A) (Spec.algebraMap D.coefficients A)
      (inclusion_spec_comp D.coefficients C hDC) D.source).symm
  targetIso := D.targetIso ≪≫
    (pullbackComparison
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom))
      (Spec.algebraMap C A) (Spec.algebraMap D.coefficients A)
      (inclusion_spec_comp D.coefficients C hDC) D.target).symm
  comm := by
    let b := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom)
    let cG := pullbackComparison b (Spec.algebraMap C A)
      (Spec.algebraMap D.coefficients A)
      (inclusion_spec_comp D.coefficients C hDC) D.source
    let cH := pullbackComparison b (Spec.algebraMap C A)
      (Spec.algebraMap D.coefficients A)
      (inclusion_spec_comp D.coefficients C hDC) D.target
    change (D.sourceIso ≪≫ cG.symm).hom ≫
        (baseChange (Spec.algebraMap C A)).map ((baseChange b).map D.hom) =
      f ≫ (D.targetIso ≪≫ cH.symm).hom
    apply (cancel_mono cH.hom).mp
    have hn : (baseChange (Spec.algebraMap C A)).map ((baseChange b).map D.hom) ≫
        cH.hom = cG.hom ≫ (baseChange (Spec.algebraMap D.coefficients A)).map D.hom :=
      pullbackComparison_naturality _ _ _ _ D.hom
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, hn,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
    exact D.comm

/-- A coefficient enlargement preserves scheme monicity. -/
theorem SimultaneousHomModel.enlargeTo_mono (D : SimultaneousHomModel R A f)
    (C : Subalgebra R A) (hC : C.FG) (hDC : D.coefficients ≤ C)
    [Mono D.hom.hom.hom.left] :
    Mono (D.enlargeTo C hC hDC).hom.hom.hom.left := by
  have : Mono D.hom.hom.hom := Over.mono_of_mono_left D.hom.hom.hom
  have : Mono ((Over.pullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom))).map
        D.hom.hom.hom) := by infer_instance
  exact inferInstanceAs (Mono ((Over.forget _).map
    ((Over.pullback
      (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hDC).toRingHom))).map
        D.hom.hom.hom)))

open Langlands.AlgebraicGeometry.NoetherianApproximation

private def coefficientStages (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    FGIndex R A →o Subalgebra R A where
  toFun i := i.1
  monotone' _ _ h := h

private theorem coefficientStages_cover (a : A) :
    ∃ i : FGIndex R A, a ∈ coefficientStages R A i := by
  classical
  refine ⟨⟨Algebra.adjoin R ↑({a} : Finset A), Subalgebra.fg_adjoin_finset _⟩, ?_⟩
  exact Algebra.subset_adjoin (by simp)

open P2MW.S_AlgebraicGeometry_SubalgebraStages_nonempty_isLimit_cone.LimBC

/-- The direct-limit reductivity premise makes any simultaneous model reductive
after enlargement while retaining all its coefficients. -/
theorem SimultaneousHomModel.exists_reductive_extension
    (hLimit : DirectLimitReductiveStatement.{u}) (D : SimultaneousHomModel R A f)
    (hG : IsReductive G) :
    ∃ (C : Subalgebra R A) (hC : C.FG) (hDC : D.coefficients ≤ C),
      IsReductive (D.enlargeTo C hC hDC).source := by
  let S := coefficientStages R A
  let i₀ : FGIndex R A := ⟨D.coefficients, D.finite⟩
  let := D.sourceSmooth
  let := D.sourceAffine
  obtain ⟨hc⟩ := nonempty_isColimit_ringCocone S coefficientStages_cover
  have hG' : IsReductive
      ((baseChange (Spec.map ((ringCocone S).ι.app i₀))).obj D.source) :=
    IsReductive.of_iso D.sourceIso.symm hG
  obtain ⟨i₁, hi₁, hred⟩ :=
    (hLimit (FGIndex R A) (ringDiagram S) (ringCocone S) hc i₀ D.source).2.1.mp hG'
  refine ⟨i₁.1, i₁.2, hi₁, ?_⟩
  exact hred i₁ hi₁ le_rfl

/-- An existing monic model acquires a reductive source after enlargement. -/
theorem SimultaneousHomModel.exists_reductive_mono_extension
    (hLimit : DirectLimitReductiveStatement.{u}) (D : SimultaneousHomModel R A f)
    (hG : IsReductive G) [Mono D.hom.hom.hom.left] :
    ∃ E : SimultaneousHomModel R A f, D.coefficients ≤ E.coefficients ∧
      IsReductive E.source ∧ Mono E.hom.hom.hom.left := by
  obtain ⟨C, hC, hDC, hred⟩ := D.exists_reductive_extension hLimit hG
  exact ⟨D.enlargeTo C hC hDC, hDC, hred, D.enlargeTo_mono C hC hDC⟩

/-- Explicit descent premises give a simultaneous reductive monic model
containing any prescribed finite set of coefficients. -/
theorem exists_reductiveMonoModel (hHom : HomGeneralStatement.{u})
    (hMono : Langlands.AlgebraicGeometry.FiniteCoefficient.MonomorphismStatement.{u})
    (hLimit : DirectLimitReductiveStatement.{u}) (f : G ⟶ H)
    (hG : IsReductive G) [IsSeparated H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [QuasiCompact H.X.hom]
    [Mono f.hom.hom.left] (s : Finset A) :
    ∃ E : SimultaneousHomModel R A f, (s : Set A) ⊆ E.coefficients ∧
      IsReductive E.source ∧ Mono E.hom.hom.hom.left := by
  let := hG.smooth
  let := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, hs⟩ := exists_homModel (R := R) (A := A) hHom f s
  let := D.sourceAffine
  let := D.sourceSmooth
  let := D.targetSeparated
  obtain ⟨T, hT, -, hm⟩ := hMono D.coefficients A D.source.X D.target.X D.hom.hom.hom
    D.mono_over_algebra ∅
  let D' := D.enlarge T hT
  have : Mono D'.hom.hom.hom.left := hm
  obtain ⟨E, hDE, hred, hmono⟩ := D'.exists_reductive_mono_extension hLimit hG
  refine ⟨E, ?_, hred, hmono⟩
  intro x hx
  exact hDE (T.algebraMap_mem ⟨x, hs hx⟩)

end Langlands.GroupScheme.Descent.FiniteCoefficient
