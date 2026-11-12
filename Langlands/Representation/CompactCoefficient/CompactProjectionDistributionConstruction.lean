import Langlands.Representation.CompactCoefficient.CompactProjectionDistributionStatement
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Langlands.Representation.CompactCoefficient.ConditionalProjection
import Langlands.Representation.Hecke.CommonInvarianceProof

/-! # Constructing the compact-representation Hecke projectors -/

noncomputable section

universe u v w

open CategoryTheory MeasureTheory Langlands.HarmonicAnalysis

namespace Langlands.Renard.CompactRepresentation

namespace ProjectionDistribution

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Left translation on compactly supported locally constant functions. -/
def testRepresentation : Representation ℂ G (SchwartzBruhat G) where
  toFun g := (Hecke.TestFunction.leftTranslate g).toLinearMap
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_assoc]

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The left regular action on test functions is smooth. -/
theorem testRepresentation_isSmooth : IsSmooth (testRepresentation (G := G)) := by
  classical
  intro f
  obtain ⟨K, -, -, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  refine ⟨K, ?_⟩
  intro k
  exact ((Hecke.TestFunction.mem_biInvariant_iff _ _ f).mp (hK f (by simp))).1 k

/-- The smooth left regular representation on actual test functions. -/
abbrev testSmoothRep : SmoothRep.{0, u, u} ℂ G :=
  SmoothRep.of testRepresentation testRepresentation_isSmooth

variable [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Compact open subgroups are cofinal among open subgroups. -/
theorem compactOpenCofinal (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ U := by
  obtain ⟨K, hKU, hK, -⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ U
  exact ⟨K, hK, hKU⟩

/-- The intrinsic compact-isotypic projector, available in every carrier universe. -/
def projector (D : IrreducibleCompactCoefficientRep.{u, v} G)
    (A : SmoothRep.{0, u, w} ℂ G) : A.representation.IntertwiningMap A.representation :=
  CompactCoefficientClass.isotypicProjectorOfIsCompl (CompactCoefficientClass.ofRep D)
    (CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation
      μ compactOpenCofinal (CompactCoefficientClass.ofRep D) A)

/-- Naturality holds even when the two carriers have different universes. -/
theorem projector_natural (D : IrreducibleCompactCoefficientRep.{u, v} G)
    {A : SmoothRep.{0, u, w} ℂ G} {B : SmoothRep ℂ G}
    (f : A.representation.IntertwiningMap B.representation) (a : A) :
    f (projector μ D A a) = projector μ D B (f a) :=
  CompactCoefficientClass.isotypicProjectorOfIsCompl_natural _ _ _ f a

/-- On the chosen irreducible, its isotypic projection is the identity. -/
theorem projector_self (D : IrreducibleCompactCoefficientRep.{u, v} G) (a : D.obj) :
    projector μ D D.obj a = a := by
  have ha : a ∈ CompactCoefficientClass.isotypicSubrepresentation
      (CompactCoefficientClass.ofRep D) D.obj :=
    CompactCoefficientClass.range_le_isotypicSubrepresentation D rfl
      (Representation.IntertwiningMap.id D.obj.representation) ⟨a, rfl⟩
  exact Submodule.projection_apply_of_mem_left _ ha

/-- On an inequivalent irreducible, the projection vanishes. -/
theorem projector_other (D : IrreducibleCompactCoefficientRep.{u, v} G)
    (A : SmoothRep.{0, u, v} ℂ G) (hA : A.IsIrreducible) (hAD : IsEmpty (A ≅ D.obj))
    (a : A) : projector μ D A a = 0 := by
  have hzero : CompactCoefficientClass.isotypicSubrepresentation
      (CompactCoefficientClass.ofRep D) A = ⊥ := by
    rw [CompactCoefficientClass.isotypicSubrepresentation_eq_iSup_range D rfl]
    apply le_antisymm _ bot_le
    refine iSup_le fun f => ?_
    let := D.property.1
    let := hA
    have hf : f = 0 := by
      rcases Representation.IsIrreducible.bijective_or_eq_zero f with hf | hf
      · exact (hAD.false ((SmoothRep.mkIso (f.ofBijective hf)).symm)).elim
      · exact hf
    rintro _ ⟨x, rfl⟩
    rw [hf]
    exact (⊥ : Subrepresentation A.representation).toSubmodule.zero_mem
  have ha : projector μ D A a ∈ CompactCoefficientClass.isotypicSubrepresentation
      (CompactCoefficientClass.ofRep D) A := by
    have hmem : projector μ D A a ∈ (projector μ D A).range := ⟨a, rfl⟩
    simpa only [projector, CompactCoefficientClass.isotypicProjectorOfIsCompl_range]
      using hmem
  rwa [hzero] at ha

/-- Applying a test function to a fixed vector is a left-regular intertwiner. -/
def actionVector (A : SmoothRep.{0, u, w} ℂ G) (a : A) :
    testSmoothRep.representation.IntertwiningMap A.representation :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (LinearMap.applyₗ a ∘ₗ Hecke.integratedAction μ A.representation A.isSmooth)
    (fun g f => Hecke.integratedAction_leftTranslate μ A.representation A.isSmooth g f a)

/-- Project `e_K` inside the actual smooth left regular representation. -/
def element (D : IrreducibleCompactCoefficientRep.{u, v} G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) : Hecke.HeckeAlgebra μ :=
  (Hecke.HeckeAlgebra.toTestFunction μ).symm
    (projector μ D testSmoothRep
      (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)))

/-- Its action on every representation is the intrinsic projector followed by `e_K`. -/
theorem action_element (D : IrreducibleCompactCoefficientRep.{u, v} G)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (A : SmoothRep.{0, u, w} ℂ G) (a : A) :
    Hecke.heckeAction μ A.representation A.isSmooth (element μ D K hK) a =
      projector μ D A
        (Hecke.heckeAction μ A.representation A.isSmooth
          (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) a) := by
  simpa only [element, Hecke.heckeAction_apply, LinearEquiv.apply_symm_apply,
      actionVector, LinearMap.intertwiningMap_of_isIntertwiningMap,
      Representation.IntertwiningMap.coe_mk, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
    using projector_natural μ D (actionVector μ A a)
      (Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.normalizedIndicator μ K hK))

/-- The constructed Hecke element has precisely the prescribed irreducible actions. -/
theorem exists_element (τ : SmoothRep.{0, u, v} ℂ G) (hτ : τ.IsIrreducible)
    (hc : HasCompactSmoothDualCoefficients τ.representation)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    ∃ e : Hecke.HeckeAlgebra μ,
      Hecke.heckeAction μ τ.representation τ.isSmooth e =
        Hecke.heckeAction μ τ.representation τ.isSmooth
          (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) ∧
      ∀ ρ : SmoothRep.{0, u, v} ℂ G, ρ.IsIrreducible → IsEmpty (ρ ≅ τ) →
        Hecke.heckeAction μ ρ.representation ρ.isSmooth e = 0 := by
  let D : IrreducibleCompactCoefficientRep.{u, v} G := ⟨τ, hτ, hc⟩
  refine ⟨element μ D K hK, ?_, ?_⟩
  · ext a
    rw [action_element, projector_self]
  · intro ρ hρ hρτ
    ext a
    exact (action_element μ D K hK ρ a).trans (projector_other μ D ρ hρ hρτ _)

end ProjectionDistribution

end Langlands.Renard.CompactRepresentation
