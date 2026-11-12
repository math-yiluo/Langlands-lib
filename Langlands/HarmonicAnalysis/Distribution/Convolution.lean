import Langlands.HarmonicAnalysis.Distribution.CompactSupportPairing
import Langlands.HarmonicAnalysis.Distribution.TensorProduct
import Langlands.HarmonicAnalysis.GroupAction

/-! # Renard II.3.10: convolution of compactly supported distributions -/

noncomputable section

open scoped Pointwise

namespace Langlands.HarmonicAnalysis.Distribution

universe uG uX

variable {X : Type uX} [TopologicalSpace X]

/-- The actual point-evaluation distribution. -/
def dirac (x : X) : Distribution X where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem dirac_apply (x : X) (f : SchwartzBruhat X) : dirac x f = f x := rfl

section CompactDirac

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

/-- Evaluation is supported on its point, hence has compact support. -/
def compactDirac (x : X) : compactlySupported (X := X) :=
  ⟨dirac x, isCompact_singleton.of_isClosed_subset (isClosed_support _) <|
    support_subset_of_mem_supportedOn isClosed_singleton (by
      intro f hf
      exact hf x (Set.mem_singleton x))⟩

@[simp]
theorem coe_compactDirac (x : X) :
    (compactDirac x : Distribution X) = dirac x := rfl

end CompactDirac

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The original distribution descended to its own closed topological support,
using the published closed-pushforward equivalence. -/
def onSupport (T : compactlySupported (X := G)) :
    Distribution (support (T : Distribution G)) :=
  (closedPushforwardSupportedEquiv (isClosed_support (T : Distribution G))).symm
    ⟨(T : Distribution G), mem_supportedOn_support _⟩

/-- Pullback of a test by multiplication on the product of the two actual
compact supports. Compactness makes this a genuine test there. -/
def multiplicationPullback (T S : compactlySupported (X := G)) :
    SchwartzBruhat G →ₗ[ℂ]
      SchwartzBruhat (support (T : Distribution G) × support (S : Distribution G)) where
  toFun f := by
    letI : CompactSpace (support (T : Distribution G)) :=
      isCompact_iff_compactSpace.mp T.property
    letI : CompactSpace (support (S : Distribution G)) :=
      isCompact_iff_compactSpace.mp S.property
    exact ⟨fun p => f (p.1.val * p.2.val),
      f.locallyConstant.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_subtype_val.comp continuous_snd)),
      HasCompactSupport.of_compactSpace _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem multiplicationPullback_apply (T S : compactlySupported (X := G))
    (f : SchwartzBruhat G)
    (x : support (T : Distribution G)) (y : support (S : Distribution G)) :
    multiplicationPullback T S f (x, y) = f (x.val * y.val) := rfl

/-- The convolution formula as an actual full distribution, evaluated on the
tensor product of the distributions descended to their compact supports. -/
def convolutionDistribution (T S : compactlySupported (X := G)) : Distribution G :=
  (tensor (onSupport T) (onSupport S)).comp (multiplicationPullback T S)

/-- The support bound also supplies the compactness needed to construct the
operation on E′ itself. -/
theorem support_convolutionDistribution_subset (T S : compactlySupported (X := G)) :
    support (convolutionDistribution T S) ⊆
      support (T : Distribution G) * support (S : Distribution G) := by
  apply support_subset_of_mem_supportedOn (T.property.mul S.property).isClosed
  intro f hf
  change tensor (onSupport T) (onSupport S) (multiplicationPullback T S f) = 0
  have hz : multiplicationPullback T S f = 0 := by
    ext p
    exact hf _ ⟨p.1.val, p.1.property, p.2.val, p.2.property, rfl⟩
  rw [hz, map_zero]

/-- Convolution on the existing compactly supported distribution carrier. -/
def convolution (T S : compactlySupported (X := G)) : compactlySupported (X := G) :=
  ⟨convolutionDistribution T S,
    (T.property.mul S.property).of_isClosed_subset (isClosed_support _)
      (support_convolutionDistribution_subset T S)⟩

@[simp]
theorem convolution_apply (T S : compactlySupported (X := G))
    (f : SchwartzBruhat G) :
    (convolution T S : Distribution G) f =
      tensor (onSupport T) (onSupport S) (multiplicationPullback T S f) := rfl

/-- Convolution of an arbitrary distribution with a scalar test, as a scalar
function; its local constancy is a separate statement obligation. -/
def leftConvolveTest (T : Distribution G) (f : SchwartzBruhat G) (x : G) : ℂ :=
  T (Hecke.TestFunction.leftTranslate x (Hecke.TestFunction.inversion f))

/-- Right convolution has the source's inverse parameter in the right translate. -/
def rightConvolveTest (f : SchwartzBruhat G) (T : Distribution G) (x : G) : ℂ :=
  T (Hecke.TestFunction.rightTranslate x⁻¹ (Hecke.TestFunction.inversion f))

/-- Compact distributions can also be paired with all locally constant
functions, using the existing compact-support pairing. -/
def leftConvolveSmooth (T : compactlySupported (X := G))
    (f : LocallyConstant G ℂ) (x : G) : ℂ :=
  compactSupportPairing T
    ⟨fun g => f (g⁻¹ * x),
      f.isLocallyConstant.comp_continuous (continuous_inv.mul continuous_const)⟩

def rightConvolveSmooth (f : LocallyConstant G ℂ)
    (T : compactlySupported (X := G)) (x : G) : ℂ :=
  compactSupportPairing T
    ⟨fun g => f (x * g⁻¹),
      f.isLocallyConstant.comp_continuous (continuous_const.mul continuous_inv)⟩

end Langlands.HarmonicAnalysis.Distribution
