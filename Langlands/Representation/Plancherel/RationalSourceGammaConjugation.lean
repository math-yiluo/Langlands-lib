import Langlands.Representation.Plancherel.RationalDynamicSourceHaar
import Langlands.Representation.Plancherel.SourceGammaTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation

/-! # Conjugation of the actual rational source gamma -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz QuotientIntegration
open BruhatTits.DynamicUnipotentContainment

section Algebraic

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (g : rationalPoints G)

/-- Opposite cocharacters commute with the actual scheme inner automorphism. -/
theorem oppositeCocharacter_conjugate :
    oppositeCocharacter (χ ≫ (G.innerIso g).hom) =
      oppositeCocharacter χ ≫ (G.innerIso g).hom := by
  exact (Category.assoc _ _ _).symm

end Algebraic

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance sourceGammaConjugationPointTopology : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance sourceGammaConjugationPointMeasurable : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
local instance sourceGammaConjugationPointBorel : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance sourceGammaConjugationFieldT2 : T2Space F := BruhatTits.localField_t2Space F
local instance sourceGammaConjugationPointTopologicalGroup : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance sourceGammaConjugationPointLocallyCompact : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "A" => RationalPoint F G.X
local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "V" => unipotentPoints (oppositeCocharacter χ)

/-- The existing compact-image construction for actual rational conjugation. -/
abbrev conjugateCompact (g : A) (K : OpenSubgroup A) : OpenSubgroup A :=
  sourceCompactImage (rationalPointsConjHomeomorph G g) K

@[simp] theorem mem_conjugateCompact (g x : A) (K : OpenSubgroup A) :
    g * x * g⁻¹ ∈ conjugateCompact g K ↔ x ∈ K :=
  mem_sourceCompactImage (rationalPointsConjHomeomorph G g) K x

theorem conjugateCompact_isCompact (g : A) (K : OpenSubgroup A)
    (hK : IsCompact (K : Set A)) : IsCompact (conjugateCompact g K : Set A) :=
  sourceCompactImage_isCompact (rationalPointsConjHomeomorph G g) K hK

theorem conjugateCompact_eq_self (g : A) (K : OpenSubgroup A) (hg : g ∈ K) :
    conjugateCompact g K = K := by
  ext x
  change g⁻¹ * x * g ∈ K ↔ x ∈ K
  constructor
  · intro hx
    simpa [mul_assoc] using K.mul_mem (K.mul_mem hg hx) (K.inv_mem hg)
  · intro hx
    exact K.mul_mem (K.mul_mem (K.inv_mem hg) hx) hg

/-- Conjugation preserving the chosen compact preserves the actual rational
source gamma, with the same intrinsic subgroup Haar normalization. -/
theorem gamma_eq_of_compactPreserving_conjugation
    (g : A) (K K' : OpenSubgroup A)
    (hK : IsCompact (K : Set A)) (hK' : IsCompact (K' : Set A))
    (hcompact : ∀ x : A, g * x * g⁻¹ ∈ K' ↔ x ∈ K) :
    gamma (χ ≫ (G.innerIso g).hom) K' hK' = gamma χ K hK := by
  let e := rationalPointsConjHomeomorph G g
  have hpar : ∀ x : A,
      e x ∈ (Dynamic.parabolic (χ ≫ (G.innerIso g).hom)).carrier X₀ ↔ x ∈ P := by
    intro x
    simpa only [e, rationalPointsConjHomeomorph_apply, constantPoint_rationalPoint] using
      (Dynamic.mem_parabolic_conj χ g (x := x)).symm
  have hopp : ∀ x : A,
      e x ∈ unipotentPoints (oppositeCocharacter (χ ≫ (G.innerIso g).hom)) ↔ x ∈ V := by
    intro x
    rw [oppositeCocharacter_conjugate]
    simpa only [e, rationalPointsConjHomeomorph_apply, constantPoint_rationalPoint] using
      (Dynamic.mem_unipotent_conj (oppositeCocharacter χ) g (x := x)).symm
  exact compactNormalizedSourceGamma_eq_of_transport e K K' hK hK'
    (isClosed_dynamic_parabolic F G χ) (isClosed_unipotentPoints (oppositeCocharacter χ))
    (isClosed_dynamic_parabolic F G (χ ≫ (G.innerIso g).hom))
    (isClosed_unipotentPoints (oppositeCocharacter (χ ≫ (G.innerIso g).hom)))
    hpar hopp hcompact

/-- Moving the chosen compact along with the cocharacter gives exact covariance
for every rational conjugating point. -/
theorem gamma_conjugateCompact (g : A) (K : OpenSubgroup A)
    (hK : IsCompact (K : Set A)) :
    gamma (χ ≫ (G.innerIso g).hom) (conjugateCompact g K)
      (conjugateCompact_isCompact g K hK) = gamma χ K hK :=
  gamma_eq_of_compactPreserving_conjugation χ g K (conjugateCompact g K) hK
    (conjugateCompact_isCompact g K hK) (fun x => mem_conjugateCompact g x K)

/-- In particular, conjugating by an element of the chosen compact leaves
the fixed-compact rational source gamma unchanged. -/
theorem gamma_conjugate_of_mem_compact (g : A) (K : OpenSubgroup A)
    (hK : IsCompact (K : Set A)) (hg : g ∈ K) :
    gamma (χ ≫ (G.innerIso g).hom) K hK = gamma χ K hK := by
  apply gamma_eq_of_compactPreserving_conjugation χ g K K hK hK
  intro x
  simpa only [conjugateCompact_eq_self g K hg] using mem_conjugateCompact g x K

end Langlands.Plancherel.RationalDynamicSource
