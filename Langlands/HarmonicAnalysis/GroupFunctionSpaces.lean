import Langlands.HarmonicAnalysis.GroupAction
import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Renard II.3.5: fixed and uniformly invariant function spaces -/

noncomputable section

namespace Langlands.HarmonicAnalysis.GroupFunctionSpaces

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Fixed vectors use Mathlib's invariants of the restricted representation. -/
abbrev fixed {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) : Submodule ℂ V :=
  Representation.invariants (ρ.comp K.subtype)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem mem_fixed_iff {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ k : K, ρ k v = v := Iff.rfl

/-- Union of the levels over compact open subgroups, as in the source.
No span or completion is inserted in this union. -/
def uniform {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (levels : Subgroup G → Submodule ℂ V) : Set V :=
  {v | ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ v ∈ levels K.toSubgroup}

/-- `C∞(G,K,l)` on the existing locally constant carrier. -/
def functionsLeft (K : Subgroup G) : Submodule ℂ (LocallyConstant G ℂ) :=
  (fixed GroupAction.leftFunctions K).comap (LocallyConstant.coeFnₗ ℂ)

/-- `C∞(G,K,r)` on the existing locally constant carrier. -/
def functionsRight (K : Subgroup G) : Submodule ℂ (LocallyConstant G ℂ) :=
  (fixed GroupAction.rightFunctions K).comap (LocallyConstant.coeFnₗ ℂ)

def functionsBoth (K : Subgroup G) : Submodule ℂ (LocallyConstant G ℂ) :=
  functionsLeft K ⊓ functionsRight K

abbrev testsLeft (K : Subgroup G) : Submodule ℂ (SchwartzBruhat G) :=
  fixed GroupAction.leftTests K

abbrev testsRight (K : Subgroup G) : Submodule ℂ (SchwartzBruhat G) :=
  fixed GroupAction.rightTests K

/-- The two-sided test space is the already published actual bi-invariant space. -/
abbrev testsBoth (K : Subgroup G) : Submodule ℂ (SchwartzBruhat G) :=
  Hecke.TestFunction.biInvariant K K

theorem testsBoth_eq_inf (K : Subgroup G) :
    testsBoth K = testsLeft K ⊓ testsRight K := by
  ext f
  rw [Hecke.TestFunction.mem_biInvariant_iff]
  simp only [Submodule.mem_inf, testsLeft, testsRight, mem_fixed_iff,
    GroupAction.leftTests_eq_leftTranslate, GroupAction.rightTests_eq_rightTranslate,
    LinearEquiv.coe_toLinearMap]

abbrev distributionsLeft (K : Subgroup G) : Submodule ℂ (Distribution G) :=
  fixed GroupAction.leftDistributions K

abbrev distributionsRight (K : Subgroup G) : Submodule ℂ (Distribution G) :=
  fixed GroupAction.rightDistributions K

def distributionsBoth (K : Subgroup G) : Submodule ℂ (Distribution G) :=
  distributionsLeft K ⊓ distributionsRight K

abbrev uniformFunctionsLeft : Set (LocallyConstant G ℂ) := uniform functionsLeft
abbrev uniformFunctionsRight : Set (LocallyConstant G ℂ) := uniform functionsRight
abbrev uniformFunctionsBoth : Set (LocallyConstant G ℂ) := uniform functionsBoth

abbrev uniformTestsLeft : Set (SchwartzBruhat G) := uniform testsLeft
abbrev uniformTestsRight : Set (SchwartzBruhat G) := uniform testsRight
abbrev uniformTestsBoth : Set (SchwartzBruhat G) := uniform testsBoth

abbrev uniformDistributionsLeft : Set (Distribution G) := uniform distributionsLeft
abbrev uniformDistributionsRight : Set (Distribution G) := uniform distributionsRight
abbrev uniformDistributionsBoth : Set (Distribution G) := uniform distributionsBoth

section CompactSupport

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- The E′ levels are actual intersections inside the published full distribution space. -/
def compactDistributionsLeft (K : Subgroup G) : Submodule ℂ (Distribution G) :=
  Distribution.compactlySupported ⊓ distributionsLeft K

def compactDistributionsRight (K : Subgroup G) : Submodule ℂ (Distribution G) :=
  Distribution.compactlySupported ⊓ distributionsRight K

def compactDistributionsBoth (K : Subgroup G) : Submodule ℂ (Distribution G) :=
  Distribution.compactlySupported ⊓ distributionsBoth K

abbrev uniformCompactDistributionsLeft : Set (Distribution G) :=
  uniform compactDistributionsLeft

abbrev uniformCompactDistributionsRight : Set (Distribution G) :=
  uniform compactDistributionsRight

abbrev uniformCompactDistributionsBoth : Set (Distribution G) :=
  uniform compactDistributionsBoth

end CompactSupport

end Langlands.HarmonicAnalysis.GroupFunctionSpaces
