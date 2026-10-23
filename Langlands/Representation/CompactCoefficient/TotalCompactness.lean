import Langlands.Representation.CompactCoefficient.Isotypic
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Category.Subquotients
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-! Compactness and exhaustion of the intrinsic total compact-isotypic part. -/

noncomputable section

namespace Langlands

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Vectors whose coefficients against every smooth functional have compact support. -/
def compactCoefficientVectors {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {v | ∀ ℓ : Module.Dual ℂ V, IsSmoothVector ρ.dual ℓ →
    HasCompactSupport (matrixCoefficient ρ ℓ v)}
  zero_mem' := by
    intro ℓ _
    have h : matrixCoefficient ρ ℓ 0 = 0 := by ext; simp [matrixCoefficient]
    rw [h]
    exact HasCompactSupport.zero
  add_mem' := by
    intro v w hv hw ℓ hℓ
    simpa [matrixCoefficient, Pi.add_def] using (hv ℓ hℓ).add (hw ℓ hℓ)
  smul_mem' := by
    intro a v hv ℓ hℓ
    have h : matrixCoefficient ρ ℓ (a • v) =
        (fun _ : G => a) • matrixCoefficient ρ ℓ v := by
      ext; simp [matrixCoefficient]
    rw [h]
    exact HasCompactSupport.smul_left (hv ℓ hℓ)

/-- The image of a compact-coefficient representation consists of compact-coefficient vectors. -/
theorem range_le_compactCoefficientVectors
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (hρ : HasCompactSmoothDualCoefficients ρ) :
    LinearMap.range f.toLinearMap ≤ compactCoefficientVectors σ := by
  rintro _ ⟨v, rfl⟩ ℓ hℓ
  change HasCompactSupport (matrixCoefficient σ ℓ (f v))
  rw [matrixCoefficient_intertwining f]
  exact hρ v (dualIntertwining f ℓ)
    (isSmoothVector_map (dualIntertwining f) hℓ)

section Extension

variable [IsTopologicalGroup G]
  (hcof : ∀ K : OpenSubgroup G,
    ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
  (A : SmoothRep.{0, uG, uV} ℂ G)

include hcof in
/-- Compact coefficients of ambient vectors give compact coefficients on a smooth
subrepresentation, by extending its smooth functionals. -/
theorem hasCompactSmoothDualCoefficients_subrepresentation_of_le
    (S : Subrepresentation A.representation)
    (hS : S.toSubmodule ≤ compactCoefficientVectors A.representation) :
    HasCompactSmoothDualCoefficients S.toRepresentation := by
  intro v ℓ hℓ
  let f : S.toRepresentation.IntertwiningMap A.representation :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  obtain ⟨m, hm⟩ :=
    contragredientMap_surjective_of_injective_of_compact_cofinal hcof
      (isSmooth_of_injective f Subtype.val_injective A.isSmooth) A.isSmooth f
      Subtype.val_injective ⟨ℓ, hℓ⟩
  have hdual : dualIntertwining f m.val = ℓ := congrArg Subtype.val hm
  have hc := hS v.property m.val m.property
  change HasCompactSupport (matrixCoefficient A.representation m.val (f v)) at hc
  rw [matrixCoefficient_intertwining f, hdual] at hc
  exact hc

include hcof in
/-- Compact smooth-dual coefficients pass to every actual smooth subrepresentation. -/
theorem hasCompactSmoothDualCoefficients_subrepresentation
    (hA : HasCompactSmoothDualCoefficients A.representation)
    (S : Subrepresentation A.representation) :
    HasCompactSmoothDualCoefficients S.toRepresentation :=
  hasCompactSmoothDualCoefficients_subrepresentation_of_le hcof A S
    (fun v _ => hA v)

namespace CompactCoefficientClass

omit [IsTopologicalGroup G] in
/-- Every vector in the total intrinsic isotypic part has compact ambient coefficients. -/
theorem totalIsotypicSubrepresentation_le_compactCoefficientVectors :
    (totalIsotypicSubrepresentation.{uG, uW} A).toSubmodule ≤
      compactCoefficientVectors A.representation := by
  rw [totalIsotypicSubrepresentation_eq_iSup_range]
  simp only [Subrepresentation.toSubmodule_iSup]
  exact iSup₂_le fun D f => range_le_compactCoefficientVectors f D.property.2

include hcof in
/-- The total intrinsic compact-isotypic part has compact smooth-dual coefficients. -/
theorem totalIsotypicSubrepresentation_hasCompactSmoothDualCoefficients :
    HasCompactSmoothDualCoefficients
      (totalIsotypicSubrepresentation.{uG, uW} A).toRepresentation :=
  hasCompactSmoothDualCoefficients_subrepresentation_of_le hcof A _
    (totalIsotypicSubrepresentation_le_compactCoefficientVectors A)

end CompactCoefficientClass
end Extension

namespace CompactCoefficientClass

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
  (A : SmoothRep.{0, uG, uV} ℂ G)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- An atomic actual subrepresentation is irreducible. -/
private theorem irreducible_subrepresentation_of_isAtom
    (S : Subrepresentation A.representation) (hS : IsAtom S) :
    (SmoothRep.subrepresentation A S).IsIrreducible := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.representation)
  let N := e S
  let j : (SmoothRep.subrepresentation A S).representation.asModule →ₗ[MonoidAlgebra ℂ G] N :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (SmoothRep.hom (SmoothRep.subtype A S))).codRestrict N (fun v => v.property)
  have hj : Function.Bijective j :=
    ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
      fun v => ⟨⟨v.val, v.property⟩, rfl⟩⟩
  apply (Representation.irreducible_iff_isSimpleModule_asModule _).mpr
  exact (j.isSimpleModule_iff_of_bijective hj).mpr
    (isSimpleModule_iff_isAtom.mpr ((e.isAtom_iff S).mpr hS))

include μ in
/-- Every compact-coefficient smooth object is exhausted by its total intrinsic
isotypic part, with representatives in its own carrier universe. -/
theorem totalIsotypicSubrepresentation_eq_top_of_compactCoefficients
    (hA : HasCompactSmoothDualCoefficients A.representation) :
    totalIsotypicSubrepresentation.{uG, uV} A = ⊤ := by
  have hcof : ∀ K : OpenSubgroup G,
      ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLK, hL, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ K
    exact ⟨L, hL, hLK⟩
  have hatoms : sSup {S : Subrepresentation A.representation | IsAtom S} = ⊤ :=
    CompactCoefficientSemisimplicity.sSup_atoms_eq_top_of_separating fun S _ hv =>
      CompactCoefficientSemisimplicity.exists_intertwiner_separating
        μ A.representation A.isSmooth hA S hv
  apply top_unique
  rw [← hatoms]
  refine sSup_le fun S hS => ?_
  let D : IrreducibleCompactCoefficientRep.{uG, uV} G :=
    ⟨SmoothRep.subrepresentation A S,
      irreducible_subrepresentation_of_isAtom A S hS,
      hasCompactSmoothDualCoefficients_subrepresentation hcof A hA S⟩
  let f : D.obj.representation.IntertwiningMap A.representation :=
    SmoothRep.hom (SmoothRep.subtype A S)
  have hSf : S ≤ f.range := fun v hv => ⟨⟨v, hv⟩, rfl⟩
  exact hSf.trans ((range_le_isotypicSubrepresentation D rfl f).trans
    (isotypicSubrepresentation_le_totalIsotypicSubrepresentation A (ofRep D)))

end CompactCoefficientClass
end Langlands
