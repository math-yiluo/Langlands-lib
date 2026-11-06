import Langlands.Representation.Plancherel.RationalSourceGammaConjugation

/-! # Conjugation of the actual compact-normalized subgroup Haar measures -/

noncomputable section

open MeasureTheory Topology

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz QuotientIntegration
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance haarConjugationPointTopology : TopologicalSpace (RationalPoint F G.X) :=
  rationalPointTopology F G.X
local instance haarConjugationPointMeasurable : MeasurableSpace (RationalPoint F G.X) :=
  borel (RationalPoint F G.X)
local instance haarConjugationPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance haarConjugationFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance haarConjugationPointTopologicalGroup :
    IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance haarConjugationPointT2 : T2Space (RationalPoint F G.X) :=
  rationalPoint_t2Space F G
local instance haarConjugationPointLocallyCompact :
    LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance haarConjugationPointNonarchimedean :
    NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (g : RationalPoint F G.X)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀

/-- The actual parabolic membership comparison has the same forward
conjugation convention as the topological group isomorphism. -/
theorem parabolic_conjugation_mem_iff (x : RationalPoint F G.X) :
    rationalPointsConjHomeomorph G g x ∈
      SubgroupFunctor.carrier (Dynamic.parabolic (χ ≫ (G.innerIso g).hom)) X₀ ↔
      x ∈ P := by
  simpa only [rationalPointsConjHomeomorph_apply, GroupScheme.constantPoint_self] using
    (Dynamic.mem_parabolic_conj χ g (x := x)).symm

/-- Forward conjugation preserves actual radical membership. -/
theorem radical_conjugation_mem_iff (x : RationalPoint F G.X) :
    rationalPointsConjHomeomorph G g x ∈ unipotentPoints (χ ≫ (G.innerIso g).hom) ↔
      x ∈ unipotentPoints χ := by
  simpa only [rationalPointsConjHomeomorph_apply, GroupScheme.constantPoint_self] using
    (Dynamic.mem_unipotent_conj χ g (x := x)).symm

/-- The restricted continuous group isomorphism on the literal parabolics. -/
def parabolicSourceConjugation :
    P ≃ₜ* SubgroupFunctor.carrier (Dynamic.parabolic (χ ≫ (G.innerIso g).hom)) X₀ :=
  subgroupContinuousMulEquiv (rationalPointsConjHomeomorph G g) P
    (SubgroupFunctor.carrier (Dynamic.parabolic (χ ≫ (G.innerIso g).hom)) X₀)
    (parabolic_conjugation_mem_iff χ g)

/-- The restricted continuous group isomorphism on the literal radicals. -/
def radicalSourceConjugation :
    unipotentPoints χ ≃ₜ* unipotentPoints (χ ≫ (G.innerIso g).hom) :=
  subgroupContinuousMulEquiv (rationalPointsConjHomeomorph G g) _ _
    (radical_conjugation_mem_iff χ g)

variable (K K' : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (hK' : IsCompact (K' : Set (RationalPoint F G.X)))

/-- Conjugation carries the original normalized parabolic Haar exactly
to the original normalization at the corresponding compact. -/
theorem measurePreserving_parabolicSourceConjugation
    (hcompact : ∀ x, rationalPointsConjHomeomorph G g x ∈ K' ↔ x ∈ K) :
    MeasurePreserving (parabolicSourceConjugation χ g)
      (parabolicHaar χ K hK)
      (parabolicHaar (χ ≫ (G.innerIso g).hom) K' hK') :=
  measurePreserving_sourceSubgroupHaar (rationalPointsConjHomeomorph G g) K K' hK hK' P
    (SubgroupFunctor.carrier (Dynamic.parabolic (χ ≫ (G.innerIso g).hom)) X₀)
    (isClosed_dynamic_parabolic F G χ)
    (isClosed_dynamic_parabolic F G (χ ≫ (G.innerIso g).hom))
    (parabolic_conjugation_mem_iff χ g) hcompact

/-- Conjugation carries the original normalized radical Haar exactly
to the original normalization at the corresponding compact. -/
theorem measurePreserving_radicalSourceConjugation
    (hcompact : ∀ x, rationalPointsConjHomeomorph G g x ∈ K' ↔ x ∈ K) :
    MeasurePreserving (radicalSourceConjugation χ g)
      (radicalHaar χ K hK)
      (radicalHaar (χ ≫ (G.innerIso g).hom) K' hK') :=
  measurePreserving_sourceSubgroupHaar (rationalPointsConjHomeomorph G g) K K' hK hK' _ _
    (isClosed_unipotentPoints χ)
    (isClosed_unipotentPoints (χ ≫ (G.innerIso g).hom))
    (radical_conjugation_mem_iff χ g) hcompact

end Langlands.Plancherel.RationalDynamicSource
