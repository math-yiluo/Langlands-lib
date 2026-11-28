import Langlands.Global.AdelicNestedRadicalLattices
import Langlands.Global.LeftCosetSemidirectNormalizedIntegral

/-! # Compatible normalized Haar for nested unipotent radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped CategoryTheory.MonObj ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

namespace AdelicSubgroupPoints

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (U : SubgroupFunctor G) [hU : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]

local notation "Γ" => rationalSubgroup F G U
local notation "H" => adelicPoints F G U
local notation "dΓ" => isDiscrete_rationalSubgroup F G U
local instance : LocallyCompactSpace H := hU.locallyCompactSpace
local instance : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology
  (adelicPoints F G U : Set (AdelicGroupPoints F G)))

/-- The ambient normalization by quotient mass is the lattice normalization of Haar. -/
theorem normalizedHaarMeasure_eq_latticeNormalizedHaar :
    normalizedHaarMeasure F G U = LeftCosetSpace.Semidirect.latticeNormalizedHaar Γ dΓ := by
  unfold normalizedHaarMeasure quotientMassNormalizer rationalQuotientHaarMeasure
  rw [LeftCosetSpace.haarQuotientMeasure, LeftCosetSpace.discreteQuotientMeasure,
    LeftCosetSpace.quotientMeasure_univ]
  rfl

variable [CompactSpace (RationalQuotient F G U)]

/-- The ambient measure normalized by a compact quotient is Haar. -/
theorem isHaarMeasure_normalizedHaarMeasure : (normalizedHaarMeasure F G U).IsHaarMeasure := by
  exact Measure.IsHaarMeasure.smul _ (quotientMassNormalizer_ne_zero F G U)
    (quotientMassNormalizer_ne_top F G U)

/-- The radical representative domain has mass one with this Haar normalization. -/
theorem normalizedHaarMeasure_fundamentalDomain :
    normalizedHaarMeasure F G U (LeftCosetSpace.fundamentalDomain Γ dΓ) = 1 := by
  let : IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure Γ dΓ) :=
    rationalQuotientHaarMeasure_isFiniteMeasure F G U
  have htop : (Measure.haar : Measure H) (LeftCosetSpace.fundamentalDomain Γ dΓ) ≠ ⊤ :=
    LeftCosetSpace.haar_fundamentalDomain_ne_top Γ dΓ
  rw [normalizedHaarMeasure_eq_latticeNormalizedHaar U,
    LeftCosetSpace.Semidirect.latticeNormalizedHaar, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (LeftCosetSpace.haar_fundamentalDomain_ne_zero Γ dΓ) htop

end AdelicSubgroupPoints

namespace StandardParabolicFamily

open AdelicSubgroupPoints
open LeftCosetSpace.Semidirect (latticeNormalizedHaar prodHomeomorph semidirectNormalizedHaar)

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) {I Q : StandardIndex F G fam.i fam.ν}
  (d : NestedRadicalSplit fam I Q)

local notation "rad(" J ")" => SubgroupFunctor.range (fam.iU J ≫ fam.p J)
local notation "mid" => SubgroupFunctor.range (d.complementHom fam)
local notation "pt(" U ")" => adelicPoints F G U
local notation "pr(" U ")" => AdelicSubgroupPoints.rationalSubgroup F G U
local notation "dn(" U ")" => normalizedHaarMeasure F G U

local instance radical_closed (J : StandardIndex F G fam.i fam.ν) :
    IsClosed (pt(rad(J)) : Set (AdelicGroupPoints F G)) :=
  isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)

local instance middle_radical_closed : IsClosed (pt(mid) : Set (AdelicGroupPoints F G)) := by
  let h := d.complement_closed fam
  let : IsAffine d.W.X.left := isAffine_left_of_isClosedSubgroup F (d.complementHom fam) h
  let : IsClosedImmersion (d.complementHom fam).hom.hom.left := h
  exact isClosed_adelicPoints_range F G (d.complementHom fam)

local instance radical_locallyCompact (J : StandardIndex F G fam.i fam.ν) : LocallyCompactSpace pt(rad(J)) :=
  (radical_closed fam J).locallyCompactSpace

local instance middle_radical_locallyCompact : LocallyCompactSpace pt(mid) :=
  (middle_radical_closed fam d).locallyCompactSpace

/-- The normalized Haar of the smaller parabolic's radical is exactly the product of the
normalized outer and complementary radical factors under the actual multiplication map. -/
def NestedRadicalHaarStatement (c : NestedRadicalCoordinates fam d) : Prop :=
  MeasurePreserving (fun z : pt(rad(Q)) × pt(mid) => c.normal z.1 * c.sectionHom z.2)
    (dn(rad(Q)).prod dn(mid)) dn(rad(I))

set_option maxHeartbeats 2700000 in
/-- Use the split principal lattice and compactness of the two component quotients to
normalize the exact semidirect Haar product. -/
theorem nestedRadicalHaar (c : NestedRadicalCoordinates fam d) : fam.NestedRadicalHaarStatement d c := by
  let i := c.normal
  let j := c.sectionHom
  let p := c.projection
  let Γ := pr(rad(I))
  let Λ := pr(mid)
  let ΛN := pr(rad(Q))
  let hΓ := isDiscrete_rationalSubgroup F G rad(I)
  let hΛ := isDiscrete_rationalSubgroup F G mid
  let hΛN := isDiscrete_rationalSubgroup F G rad(Q)
  have hc : Γ.comap i = ΛN := c.normal_principal
  let hcN : IsDiscrete ((Γ.comap i : Subgroup pt(rad(Q))) : Set pt(rad(Q))) := by
    rw [hc]
    exact hΛN
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G rad(Q)) :=
    fam.compactSpace_radicalRationalQuotient Q
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G mid) :=
    d.compactSpace_complementQuotient fam
  have hfin (δ : Subgroup pt(rad(Q))) (hδ : IsDiscrete (δ : Set pt(rad(Q)))) (he : δ = ΛN) :
      IsFiniteMeasure (LeftCosetSpace.haarQuotientMeasure δ hδ) := by
    subst δ
    exact rationalQuotientHaarMeasure_isFiniteMeasure F G rad(Q)
  have hN : latticeNormalizedHaar (Γ.comap i) hcN = dn(rad(Q)) := by
    rw [normalizedHaarMeasure_eq_latticeNormalizedHaar]
    have he (δ : Subgroup pt(rad(Q))) (hδ : IsDiscrete (δ : Set pt(rad(Q))))
        (h : δ = ΛN) : latticeNormalizedHaar δ hδ = latticeNormalizedHaar ΛN hΛN := by
      subst δ
      rfl
    exact he _ _ hc
  let Φ := prodHomeomorph i j p c.section_projection c.kernel c.projection_normal
    c.normal_embedding c.section_continuous c.projection_continuous
  have hmap := semidirectNormalizedHaar i j p c.section_projection c.kernel c.projection_normal
    c.normal_embedding c.section_continuous c.projection_continuous Γ hΓ Λ hΛ hcN
    c.section_principal c.projection_principal (hfin _ _ hc)
    (rationalQuotientHaarMeasure_isFiniteMeasure F G mid)
  have hμ : dn(rad(I)) = (dn(rad(Q)).prod dn(mid)).map Φ := by
    rw [normalizedHaarMeasure_eq_latticeNormalizedHaar rad(I),
      normalizedHaarMeasure_eq_latticeNormalizedHaar mid]
    rw [← hN]
    exact hmap
  change MeasurePreserving Φ (dn(rad(Q)).prod dn(mid)) dn(rad(I))
  exact ⟨Φ.continuous.measurable, hμ.symm⟩

end StandardParabolicFamily
end Langlands.Global
