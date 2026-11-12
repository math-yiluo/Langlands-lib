import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedStructuralFibres
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricComponentApproximation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitModelExistenceQuasiSeparatedReduction
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationLimitModelProof
import Langlands.AlgebraicGeometry.ConstructibleAffineLimit

/-! # The connected-fibre locus and structural limit descent -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}}

/-- The locus where the canonical geometric fibre is nonempty and connected. -/
def connectedFibreLocus (X : AlgebraicSpace S) : Set S :=
  {p | schemeGeometricFibreComponentCount X p = 1}

/-- Over every scheme base, count one tests the actual nonempty geometric fibres. -/
theorem hasGeometricallyConnectedFibres_structural_iff_schemeComponentCount
    (X : AlgebraicSpace S)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    HasGeometricallyConnectedFibres (structuralMorphism X) ↔
      ∀ p, schemeGeometricFibreComponentCount X p = 1 := by
  constructor
  · intro h p
    let := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj
      (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
    exact (componentCount_eq_one_iff_connectedSpace _).mpr
      ((hasGeometricallyConnectedFibres_structural_iff X).mp h
        (AlgebraicClosure (S.residueField p))
        (SchemeFiberGeometry.componentCountGeometricPoint p))
  · intro h
    apply (hasGeometricallyConnectedFibres_iff_algClosed (structuralMorphism X)).mpr
    intro K _ _ s y
    let p := s (IsLocalRing.closedPoint K)
    obtain ⟨U, a, ha, hs, hUl, hUq⟩ := hX
    let := hUl
    let := hUq
    let := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s))
    let := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj
      (Over.mk (SchemeFiberGeometry.componentCountGeometricPoint p)))
    have hc : ENat.card (@_root_.ConnectedComponents
        (Points (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk s))) (pointTopology _)) = 1 :=
      (ENat.card_congr (GeometricComponentTransport.geometricFibreEquiv X a ha hs s p rfl)).trans
        (h p)
    let := pointTopology (Limits.pullback (hom (structuralMorphism X)) y)
    exact (Points.isoHomeomorph (structuralFibreIso X y)).connectedSpace_iff.mp
      ((componentCount_eq_one_iff_connectedSpace _).mp hc)

/-- After an arbitrary scheme base change, the criterion is pulled back on ordinary points. -/
theorem hasGeometricallyConnectedFibres_structural_baseChange_iff
    (g : T ⟶ S) (X : AlgebraicSpace S)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    HasGeometricallyConnectedFibres (structuralMorphism (baseChange g X)) ↔
      ∀ q, schemeGeometricFibreComponentCount X (g q) = 1 := by
  rw [hasGeometricallyConnectedFibres_structural_iff_schemeComponentCount
    (baseChange g X) (hX.baseChange (g := g))]
  obtain ⟨U, a, ha, hs, hUl, hUq⟩ := hX
  let := hUl
  let := hUq
  simp_rw [schemeGeometricFibreComponentCount_baseChange g X a ha hs]

/-- The good geometric-component locus is constructible over every affine scheme base. -/
theorem isConstructible_schemeComponentCount_affine [IsAffine S]
    (X : AlgebraicSpace S) (hqs : IsQuasiSeparated X)
    (hfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (n : ℕ) :
    IsConstructible {p : S | schemeGeometricFibreComponentCount X p = n} := by
  have hcons : GeometricFibreComponentsConstructibleStatement.{u} :=
    geometricFibreComponentsConstructible_of_limitModels
      (SpaceLimitModelExistenceQuasiSeparatedReduction.spaceLimitModelExistenceQuasiSeparated_of_relation
        EtaleEquivalenceRelation.limitModelExistence)
  let X' := baseChange S.isoSpec.inv X
  have hfp' : FinitePresentationOverRing Γ(S, ⊤) X' := hfp.baseChange
  have hc : IsConstructible
      {q : Spec Γ(S, ⊤) | schemeGeometricFibreComponentCount X' q = n} :=
    hcons Γ(S, ⊤) X' hqs.baseChange hfp' n
  obtain ⟨U, a, ha, hs, hUl, hUq⟩ := hfp
  let := hUl
  let := hUq
  have he :
      S.isoSpec.hom ⁻¹' {q : Spec Γ(S, ⊤) | schemeGeometricFibreComponentCount X' q = n} =
        {p : S | schemeGeometricFibreComponentCount X p = n} := by
    ext p
    change schemeGeometricFibreComponentCount (baseChange S.isoSpec.inv X)
        (S.isoSpec.hom p) = n ↔ schemeGeometricFibreComponentCount X p = n
    rw [schemeGeometricFibreComponentCount_baseChange S.isoSpec.inv X a ha hs,
      ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  rw [← he]
  exact S.isoSpec.hom.isConstructible_preimage hc

/-- Geometrically connected nonempty structural fibres descend along arbitrary
cofiltered limits of affine schemes. -/
theorem structuralConnectedFibres_iff_eventually
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I) (X : AlgebraicSpace (D.obj i))
    (hqs : IsQuasiSeparated X)
    (hfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X) :
    HasGeometricallyConnectedFibres (structuralMorphism (baseChange (c.π.app i) X)) ↔
      ∃ (j : I) (g : j ⟶ i),
        HasGeometricallyConnectedFibres (structuralMorphism (baseChange (D.map g) X)) := by
  have {j k : I} (g : j ⟶ k) : IsAffineHom (D.map g) := inferInstance
  let s : Set (D.obj i) := connectedFibreLocus X
  have hs : IsConstructible s := isConstructible_schemeComponentCount_affine X hqs hfp 1
  have H (T : Scheme.{u}) (g : T ⟶ D.obj i) :
      HasGeometricallyConnectedFibres (structuralMorphism (baseChange g X)) ↔
        g ⁻¹' s = Set.univ := by
    rw [hasGeometricallyConnectedFibres_structural_baseChange_iff g X hfp]
    exact Set.eq_univ_iff_forall.symm
  rw [H]
  exact (SchemeFiberGeometry.preimage_eq_univ_iff_exists_map_of_isConstructible
    D c hc i s hs).trans (by
      constructor
      · rintro ⟨j, g, hg⟩
        exact ⟨j, g, (H _ _).mpr hg⟩
      · rintro ⟨j, g, hg⟩
        exact ⟨j, g, (H _ _).mp hg⟩)

end Langlands.AlgebraicGeometry.AlgebraicSpace
