import Langlands.Geometry.Building.PointwiseFixerSetStabilizer
import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRadicalImage
import Langlands.BruhatTits.IntegralModels.UnramifiedUpstairsRadicalRootGenerationStatement
import Langlands.BruhatTits.IntegralModels.DepthZeroReduction
import Langlands.Geometry.Building.ChamberClosureOrbit

/-! # Chamber fixation by the depth-zero reduction kernel -/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.IntegerValuationBuildingData

variable {k : Type u} [Field k]
  {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- If a subgroup acts transitively on the chambers presented through `y`, and the
kernel of a homomorphism on it stabilizes one of them, then that kernel stabilizes
all of them: it is normal in the subgroup. -/
theorem kernel_stabilizes_of_transitive
    {Q : Type v} [Group Q] (P : Subgroup (rationalPoints G)) (q : P →* Q)
    {y : B.ReducedBuilding} {Y₀ : Set B.ReducedBuilding}
    (hY₀ : B.HasChamberClosurePresentation Y₀ y)
    (hker : ∀ g : P, q g = 1 → ((g : rationalPoints G) • ·) '' Y₀ = Y₀)
    (htrans : ∀ Y Y' : Set B.ReducedBuilding,
      B.HasChamberClosurePresentation Y y → B.HasChamberClosurePresentation Y' y →
        ∃ h : P, Y' = ((h : rationalPoints G) • ·) '' Y)
    (Y : Set B.ReducedBuilding) (hY : B.HasChamberClosurePresentation Y y)
    (g : P) (hg : q g = 1) :
    ((g : rationalPoints G) • ·) '' Y = Y := by
  obtain ⟨h, rfl⟩ := htrans Y₀ Y hY₀ hY
  have hconj : q (h⁻¹ * g * h) = 1 := by
    rw [map_mul, map_mul, hg, mul_one, map_inv, inv_mul_cancel]
  have hfix := hker (h⁻¹ * g * h) hconj
  calc ((g : rationalPoints G) • ·) '' (((h : rationalPoints G) • ·) '' Y₀)
      = ((h : rationalPoints G) • ·) ''
          ((((h⁻¹ * g * h : P) : rationalPoints G) • ·) '' Y₀) := by
        rw [Set.image_image, Set.image_image]
        congr 1
        funext z
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, smul_inv_smul]
    _ = ((h : rationalPoints G) • ·) '' Y₀ := by rw [hfix]

/-- Every apartment point has a chamber of the standard apartment through it,
presented with the identity element. -/
theorem exists_standard_chamberClosurePresentation (x : B.Apartment) :
    ∃ x₀ : B.Apartment, (∀ ψ ∈ B.affineRoots, ψ x₀ ≠ 0) ∧
      x ∈ AffineRootSystem.facetClosure B.affineRoots x₀ ∧
      B.HasChamberClosurePresentation
        (B.apartmentMap '' AffineRootSystem.facet B.affineRoots x₀) (B.apartmentMap x) := by
  obtain ⟨x₀, hregular, hclosure⟩ :=
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs
      B.hasOppositeFactorPairs).exists_regularPoint_closure x
  refine ⟨x₀, hregular, hclosure, 1, x₀, x, hregular, ?_, hclosure, one_smul _ _⟩
  simp only [one_smul]

end Langlands.Geometry.Building.IntegerValuationBuildingData

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)

/-- Given the full radical generation statement, the radical preimage of a smooth
model at an apartment point `x` fixes pointwise the image of every facet whose
closure contains `x`. -/
theorem unramifiedRadicalPreimage_le_zeroFixer_facet
    (hRad : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    {x x₀ : C.Apartment} (hx : x ∈ AffineRootSystem.facetClosure C.affineRoots x₀)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G) (hN : N.IsSmooth)
    (hNpts : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))
    {U : GroupScheme
      (Spec (CommRingCat.of (IsLocalRing.ResidueField (fixedFieldIntegers F))))}
    (i : U ⟶ N.specialFibre) (hi : IsUnipotentRadical i) :
    ((rationalPoints.map i).range.comap N.reduction).map N.integralPointMap ≤
      E.zeroPoints ⊓
        C.pointwiseFixer (C.apartmentMap '' AffineRootSystem.facet C.affineRoots x₀) := by
  obtain ⟨H, -, hH, hgen⟩ := hRad F G C E
  rw [hgen {x} (Set.singleton_nonempty x)
    ⟨x, Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self _ x)⟩
    N hN hNpts U i hi]
  exact unramifiedIncidentGeneratedGroup_le_zeroFixer C E {x}
    (AffineRootSystem.facet C.affineRoots x₀) (AffineRootSystem.isFacet_facet _ x₀)
    ⟨AffineRootSystem.isFacet_facet _ x, x₀, rfl,
      AffineRootSystem.facet_subset_facetClosure_iff.mpr hx⟩
    (Set.singleton_nonempty x)
    (Set.singleton_subset_iff.mpr (AffineRootSystem.mem_facet_self _ x)) le_rfl H hH

section Reduction

variable {D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G}
  (Q : SpecialFibreQuotientData D)

/-- Given the radical generation statement, the kernel of the depth-zero reduction
of a neutral model at an apartment point `x` fixes pointwise the image of every
facet whose closure contains `x`. -/
theorem parahoricReduction_ker_le_zeroFixer_facet
    (hRad : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    {x x₀ : C.Apartment} (hx : x ∈ AffineRootSystem.facetClosure C.affineRoots x₀)
    (hD : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection)
    (g : D.neutral.integralPoints) (hg : Q.parahoricReduction g = 1) :
    (g : rationalPoints G) ∈ E.zeroPoints ⊓
      C.pointwiseFixer (C.apartmentMap '' AffineRootSystem.facet C.affineRoots x₀) := by
  have hmem : g ∈ Q.parahoricReduction.ker := hg
  rw [Q.ker_parahoricReduction hQ, Subgroup.mem_subgroupOf] at hmem
  exact unramifiedRadicalPreimage_le_zeroFixer_facet C E hRad hx D.neutral D.neutral_smooth
    hD Q.radicalInclusion hrad hmem

/-- Given the radical generation statement and transitivity of the neutral
integral points on the chambers presented through an apartment point `x`, every
element of the kernel of a homomorphism factoring the depth-zero reduction
stabilizes each chamber presented through `x`. -/
theorem parahoricReduction_ker_stabilizes_presented
    (hRad : UnramifiedUpstairsRadicalRootGenerationStatement.{u})
    (x : C.Apartment)
    (hD : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))
    (hrad : IsUnipotentRadical Q.radicalInclusion)
    (hQ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion)
      Q.projection)
    {M : Type v} [Group M] (q : D.neutral.integralPoints →* M)
    (hq : ∀ g, q g = 1 → Q.parahoricReduction g = 1)
    (htrans : ∀ Y Y' : Set C.ReducedBuilding,
      C.HasChamberClosurePresentation Y (C.apartmentMap x) →
      C.HasChamberClosurePresentation Y' (C.apartmentMap x) →
        ∃ h ∈ E.zeroPoints ⊓ C.fixer (C.apartmentMap x), (h • ·) '' Y = Y')
    (Y : Set C.ReducedBuilding) (hY : C.HasChamberClosurePresentation Y (C.apartmentMap x))
    (g : D.neutral.integralPoints) (hg : q g = 1) :
    ((g : rationalPoints G) • ·) '' Y = Y := by
  obtain ⟨x₀, -, hx, hY₀⟩ := C.exists_standard_chamberClosurePresentation x
  refine C.kernel_stabilizes_of_transitive D.neutral.integralPoints q hY₀ ?_ ?_ Y hY g hg
  · intro g' hg'
    exact C.smul_image_eq_of_mem_pointwiseFixer
      (parahoricReduction_ker_le_zeroFixer_facet C E Q hRad hx hD hrad hQ g' (hq g' hg')).2
  · intro Y₁ Y₂ h₁ h₂
    obtain ⟨h, ⟨hh0, hhy⟩, himage⟩ := htrans Y₁ Y₂ h₁ h₂
    have hmem : h ∈ D.neutral.integralPoints := by
      rw [hD]
      refine ⟨hh0, C.apartment.mem_pointwiseFixer.2 ?_⟩
      rintro z ⟨a, ha, rfl⟩
      rw [Set.mem_singleton_iff.1 ha]
      exact C.mem_fixer.1 hhy
    exact ⟨⟨h, hmem⟩, himage.symm⟩

end Reduction

end Langlands.BruhatTits.IntegralModels

namespace Langlands.BruhatTits.IntegralModels

/-- Conditional chamber fixation by the depth-zero reduction kernel. Assume the upstairs
radical-generation statement. Let `D` be relative component model data over the fixed-field
integers whose neutral integral points are `E`'s zero subgroup intersected with the pointwise
fixer of `{apartmentMap x}`, and let `Q` be a reductive quotient datum for `D` with unipotent
radical and fppf projection. Let `q` be a homomorphism on the neutral integral points whose
kernel lies in that of `Q.parahoricReduction`, and assume that chambers presented through
`apartmentMap x` are permuted transitively by `E`'s zero subgroup intersected with the fixer of
`apartmentMap x`. Then every element of the kernel of `q` maps every chamber presented through
`apartmentMap x` onto itself. -/
def UnramifiedRadicalChamberFixationStatement : Prop :=
  UnramifiedUpstairsRadicalRootGenerationStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G) (x : C.Apartment)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Q : SpecialFibreQuotientData D),
    D.neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}) →
    IsUnipotentRadical Q.radicalInclusion →
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range Q.radicalInclusion) Q.projection →
    ∀ (M : Type u) [Group M] (q : D.neutral.integralPoints →* M),
      (∀ g, q g = 1 → Q.parahoricReduction g = 1) →
      (∀ Y Y' : Set C.ReducedBuilding,
        C.HasChamberClosurePresentation Y (C.apartmentMap x) →
        C.HasChamberClosurePresentation Y' (C.apartmentMap x) →
          ∃ h ∈ E.zeroPoints ⊓ C.fixer (C.apartmentMap x), (h • ·) '' Y = Y') →
      ∀ Y : Set C.ReducedBuilding, C.HasChamberClosurePresentation Y (C.apartmentMap x) →
        ∀ g : D.neutral.integralPoints, q g = 1 →
          ((g : rationalPoints G) • ·) '' Y = Y

/-- The conditional chamber fixation statement holds. -/
theorem unramifiedRadicalChamberFixation : UnramifiedRadicalChamberFixationStatement.{u} := by
  intro hRad F _ _ _ _ G _ C E x D Q hD hrad hQ M _ q hq htrans Y hY g hg
  exact parahoricReduction_ker_stabilizes_presented C E Q hRad x hD hrad hQ q hq htrans Y hY g hg

end Langlands.BruhatTits.IntegralModels
