import Langlands.AlgebraicGeometry.SectionComponentNoetherianReduction
import Langlands.AlgebraicGeometry.SectionComponentConstructibility
import Langlands.AlgebraicGeometry.ConstructibleGenerizations
import Langlands.AlgebraicGeometry.GenericComponentSplittingAssembly
import Langlands.AlgebraicGeometry.FiniteSeparableGenericCoverProof
import Langlands.AlgebraicGeometry.GeometricIrreducibilityProof
import Langlands.AlgebraicGeometry.GeometricallyConnectedClosedCoverProof
import Langlands.AlgebraicGeometry.FiniteSeparableComponentSplittingProof
import Langlands.AlgebraicGeometry.SectionComponentNoetherianGenerization

/-! # Assembly of section-component openness -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry

namespace SchemeFiberGeometry

/-- Field splitting and the constructed generic cover give Noetherian generic
constancy of geometric connectedness. -/
theorem noetherianGeometricallyConnectedFiberGenericConstancy_of_fieldSplitting
    (hsplit : FiniteSeparableComponentSplitting.{u}) :
    NoetherianGeometricallyConnectedFiberGenericConstancy.{u} :=
  noetherianGeometricallyConnectedFiberGenericConstancy_of_generic_splitting
    (finiteTypeFiniteEtaleGenericComponentSplitting_of_fieldSplitting_and_cover
      hsplit finiteSeparableGenericCover)
    finiteTypeGeometricallyIrreducibleGenericSpreading
    ComponentIncidence.finiteClosedGeometricallyConnectedCoverCriterion

end SchemeFiberGeometry

namespace SectionComponent

/-- Generic constancy obtained from field splitting gives constructibility of the
actual section-selected component union. -/
theorem noetherianComponentConstructibility_of_fieldSplitting
    (hsplit : SchemeFiberGeometry.FiniteSeparableComponentSplitting.{u}) :
    NoetherianComponentConstructibilityStatement.{u} :=
  noetherianComponentConstructibility_of_genericConstancy
    (SchemeFiberGeometry.noetherianGeometricallyConnectedFiberGenericConstancy_of_fieldSplitting
      hsplit)

/-- Constructibility and pointwise generization give the exact Noetherian
indexed-fibre neighbourhood assertion needed for approximation. -/
theorem noetherianFiberwiseOpenness_of_constructibility_of_generizations
    (hconstruct : NoetherianComponentConstructibilityStatement.{u})
    (hgen : ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian X]
      (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
      (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) (x : X),
      GeometricallyReduced (f.fiberToSpecResidueField (f x)) →
        x ∈ componentSet f e he →
          ∀ z : X, z ⤳ x → z ∈ componentSet f e he) :
    NoetherianFiberwiseOpennessStatement.{u} := by
  intro R _ X f e he hflat hlfp hqc hqs x hred hx
  let := hflat
  let := hlfp
  let := hqc
  let := hqs
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f }
  exact mem_interior_of_isConstructible_of_generizations
    (hconstruct X (Spec R) f e he) (hgen f e he x hred hx)

/-- The exact indexed-fibre Noetherian neighbourhood assertion. -/
theorem noetherianFiberwiseOpenness : NoetherianFiberwiseOpennessStatement.{u} := by
  apply noetherianFiberwiseOpenness_of_constructibility_of_generizations
    (noetherianComponentConstructibility_of_fieldSplitting
      SchemeFiberGeometry.finiteSeparableComponentSplitting)
  intro X Y _ f _ _ e he x hred hx z hzx
  let := hred
  exact mem_componentSet_of_specializes_of_geometricallyReduced_fiber f e he x hx hzx

/-- For a flat finitely presented geometrically reduced morphism, the actual
union of fibre connected components meeting its section is open. -/
theorem flatFinitePresentationOpenness : FlatFinitePresentationOpennessStatement.{u} :=
  flatFinitePresentationOpenness_of_noetherianFiberwise noetherianFiberwiseOpenness

end SectionComponent

end Langlands.AlgebraicGeometry
