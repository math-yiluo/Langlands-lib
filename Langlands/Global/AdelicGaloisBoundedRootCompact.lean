import Langlands.Global.AdelicBoundedRootProduct
import Langlands.Global.AdelicGaloisUnitQuotient
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximalModel
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Compactness from bounded-root coverage after Galois scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise NNReal

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints AdelicSiegelFactors

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The actual scalar-extension map restricted to the original norm-one groups. -/
def scalarExtensionNormOneMap : normOneSubgroup F G →ₜ*
    normOneSubgroup L (AffineWeil.unitBaseChange F L G) :=
  (AdelicWeilRestriction.normOneMap F L (AffineWeil.unitBaseChange F L G)).comp
    (mapNormOne F G (W F L G) (AffineWeil.unit F L G))

variable [IsGalois F L]

/-- The point map induces precisely the published scalar-extension quotient map. -/
theorem scalarExtensionQuotientMap_mk_normOne (g : normOneSubgroup F G) :
    scalarExtensionQuotientMap F L G
        (LeftCosetSpace.mk (rationalNormOneSubgroup F G) g) =
      LeftCosetSpace.mk (rationalNormOneSubgroup L (AffineWeil.unitBaseChange F L G))
        (scalarExtensionNormOneMap F L G g) := rfl

/-- A single compact set of upper-field principal representatives for the scalar-extension
image gives compact principal representatives over the original field. -/
theorem hasCompactNormOneRationalCover_of_scalarExtension_representatives
    (K : Set (normOneSubgroup L (AffineWeil.unitBaseChange F L G))) (hK : IsCompact K)
    (hcover : ∀ g : normOneSubgroup F G,
      ∃ q : RationalGroupPoints L (AffineWeil.unitBaseChange F L G),
        rationalNormOne L _ q * scalarExtensionNormOneMap F L G g ∈ K) :
    HasCompactNormOneRationalCover G := by
  let π := LeftCosetSpace.mk
    (rationalNormOneSubgroup L (AffineWeil.unitBaseChange F L G))
  have hπK : IsCompact (π '' K) :=
    hK.image (LeftCosetSpace.continuous_mk _)
  apply hasCompactNormOneRationalCover_of_isClosedEmbedding
    (scalarExtensionQuotientMap F L G)
    (isClosedEmbedding_scalarExtensionQuotientMap F L G)
  apply hπK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hπK.isClosed
  rintro _ ⟨x, rfl⟩
  induction x using Quotient.inductionOn with
  | _ g =>
      obtain ⟨q, hq⟩ := hcover g
      refine ⟨rationalNormOne L _ q * scalarExtensionNormOneMap F L G g, hq, ?_⟩
      exact LeftCosetSpace.mk_subgroup_mul
        (rationalNormOneSubgroup L (AffineWeil.unitBaseChange F L G))
        ⟨rationalNormOne L _ q, ⟨q, rfl⟩⟩ _

section BoundedRoots

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

variable (T : CommGroupScheme (Spec (CommRingCat.of L)))
  (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G) (ν : cocharacterLattice T)

/-- Uniform bounded-root coverage of the scalar-extension image, allowing genuine
upper-field principal rational translates. The parabolic factor has its own full
norm-one condition, and the compact factor lies in the actual ambient adelic group. -/
def HasBoundedRootScalarExtensionCover : Prop :=
  ∃ (b : ℝ≥0), 1 ≤ b ∧
    ∃ C : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)), IsCompact C ∧
      ∀ g : normOneSubgroup F G,
        ∃ q : RationalGroupPoints L (AffineWeil.unitBaseChange F L G),
          (rationalNormOne L _ q * scalarExtensionNormOneMap F L G g :
            normOneSubgroup L (AffineWeil.unitBaseChange F L G)).val ∈
              boundedRootParabolicProduct L (AffineWeil.unitBaseChange F L G)
                T i ν b C

/-- Bounded-root coverage after a finite Galois extension constructs a compact
principal cover of the source without requiring compactness of the whole upper quotient. -/
theorem hasCompactNormOneRationalCover_of_boundedRootScalarExtensionCover
    (hG : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hmax : IsMaximalTorus i)
    (hcover : HasBoundedRootScalarExtensionCover F L G T i ν) :
    HasCompactNormOneRationalCover G := by
  obtain ⟨b, hb, C, hC, hcover⟩ := hcover
  obtain ⟨K, hK, hrep⟩ :=
    exists_isCompact_normOne_rational_mul_mem_emptyParabolic_rootBox_mul_compact
      L (AffineWeil.unitBaseChange F L G) T i ν hG hi hν hmax b hb C hC
  apply hasCompactNormOneRationalCover_of_scalarExtension_representatives F L G K hK
  intro g
  obtain ⟨q, hq⟩ := hcover g
  obtain ⟨r, hr⟩ := hrep
    (rationalNormOne L _ q * scalarExtensionNormOneMap F L G g) hq
  refine ⟨r * q, ?_⟩
  simpa only [map_mul, mul_assoc] using hr

end BoundedRoots

end Langlands.Global.AdelicGaloisUnit

namespace Langlands.GroupScheme.FiniteGaloisSplitMaximalModel

open Langlands.Global Langlands.Global.AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (D : FiniteGaloisSplitMaximalModel G)

local instance : NumberField D.carrier := NumberField.of_module_finite F D.carrier

/-- The actual finite Galois split-maximal-torus bundle supplies all the structural
inputs to the bounded-root compactness pullback. -/
theorem hasCompactNormOneRationalCover_of_boundedRootCover
    (hG : IsConnectedReductive G) (ν : cocharacterLattice D.torus)
    (hν : IsGenericCocharacter D.inclusion ν)
    (hcover : AdelicGaloisUnit.HasBoundedRootScalarExtensionCover
      F D.carrier G D.torus D.inclusion ν) :
    HasCompactNormOneRationalCover G :=
  AdelicGaloisUnit.hasCompactNormOneRationalCover_of_boundedRootScalarExtensionCover
    F D.carrier G D.torus D.inclusion ν
    (D.isConnectedReductive hG) (D.isMaximalTorus.isMaximalSplitTorus D.isSplitTorus)
    hν D.isMaximalTorus hcover

end Langlands.GroupScheme.FiniteGaloisSplitMaximalModel
