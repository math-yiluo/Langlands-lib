import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport
import Langlands.HarmonicAnalysis.Distribution.SupportedRestriction
import Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Compactly supported distributions paired with locally constant functions

Renard, 9 July 2026, II.1.2, printed p.31 / PDF p.37.
The distribution is descended to its actual compact topological support.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Restriction of a locally constant scalar function to a compact subset,
regarded as an actual scalar test function on the induced subspace. -/
def restrictLocallyConstantCompact {K : Set X} (hK : IsCompact K) :
    LocallyConstant X ℂ →ₗ[ℂ] SchwartzBruhat K where
  toFun f := by
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact ⟨fun x => f x.val,
      f.isLocallyConstant.comp_continuous continuous_subtype_val,
      HasCompactSupport.of_compactSpace _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrictLocallyConstantCompact_apply {K : Set X} (hK : IsCompact K)
    (f : LocallyConstant X ℂ) (x : K) :
    restrictLocallyConstantCompact hK f x = f x.val := rfl

variable [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

/-- Every locally constant function has an ambient scalar test representative
on each compact subset. This reuses published closed-restriction surjectivity. -/
theorem exists_testFunction_agrees_on_compact {K : Set X} (hK : IsCompact K)
    (f : LocallyConstant X ℂ) :
    ∃ g : SchwartzBruhat X, ∀ x ∈ K, g x = f x := by
  obtain ⟨g, hg⟩ := SchwartzBruhat.closedRestrictionSurjective X K hK.isClosed
    (restrictLocallyConstantCompact hK f)
  refine ⟨g, fun x hx => ?_⟩
  exact congrArg (fun q : SchwartzBruhat K => q ⟨x, hx⟩) hg

/-- For a fixed compactly supported distribution, evaluation after descent to
its own support is complex-linear in the locally constant function. -/
def compactSupportFunctional (T : compactlySupported (X := X)) :
    LocallyConstant X ℂ →ₗ[ℂ] ℂ :=
  ((closedPushforwardSupportedEquiv (isClosed_support (T : Distribution X))).symm
    ⟨(T : Distribution X), mem_supportedOn_support _⟩).comp
      (restrictLocallyConstantCompact T.property)

/-- The source's evaluation formula on the actual compact support. -/
theorem compactSupportFunctional_apply (T : compactlySupported (X := X))
    (f : LocallyConstant X ℂ) :
    compactSupportFunctional T f =
      (closedPushforwardSupportedEquiv (isClosed_support (T : Distribution X))).symm
        ⟨(T : Distribution X), mem_supportedOn_support _⟩
        (restrictLocallyConstantCompact T.property f) := rfl

/-- Any ambient scalar test agreeing on the actual support computes the same
value. No choice of an ambient extension enters the definition. -/
theorem compactSupportFunctional_eq_of_agrees
    (T : compactlySupported (X := X)) (f : LocallyConstant X ℂ)
    (g : SchwartzBruhat X)
    (h : ∀ x ∈ support (T : Distribution X), g x = f x) :
    compactSupportFunctional T f = (T : Distribution X) g := by
  have hr : restrictLocallyConstantCompact T.property f =
      SchwartzBruhat.restrictClosed (isClosed_support (T : Distribution X)) g := by
    ext x
    exact (h x.val x.property).symm
  rw [compactSupportFunctional_apply, hr,
    closedPushforwardSupportedEquiv_symm_apply_restrictClosed]

/-- The bilinear source pairing E′(X) × C∞(X) → ℂ, using actual compact
topological support and the published closed descent. -/
def compactSupportPairing :
    compactlySupported (X := X) →ₗ[ℂ] LocallyConstant X ℂ →ₗ[ℂ] ℂ where
  toFun := compactSupportFunctional
  map_add' T S := by
    ext f
    obtain ⟨g, hg⟩ := exists_testFunction_agrees_on_compact
      (T.property.union S.property) f
    have hT := compactSupportFunctional_eq_of_agrees T f g
      (fun x hx => hg x (Or.inl hx))
    have hS := compactSupportFunctional_eq_of_agrees S f g
      (fun x hx => hg x (Or.inr hx))
    have hTS := compactSupportFunctional_eq_of_agrees (T + S) f g
      (fun x hx => hg x (support_add_subset _ _ hx))
    exact hTS.trans (congrArg₂ (· + ·) hT hS).symm
  map_smul' c T := by
    ext f
    obtain ⟨g, hg⟩ := exists_testFunction_agrees_on_compact T.property f
    have hT := compactSupportFunctional_eq_of_agrees T f g hg
    have hcT := compactSupportFunctional_eq_of_agrees (c • T) f g
      (fun x hx => hg x (support_smul_subset c _ hx))
    exact hcT.trans (congrArg (c • ·) hT).symm

/-- The pairing is literally evaluation of the unique descended distribution
on the restriction to the distribution's own compact support. -/
theorem compactSupportPairing_apply (T : compactlySupported (X := X))
    (f : LocallyConstant X ℂ) :
    compactSupportPairing T f =
      (closedPushforwardSupportedEquiv (isClosed_support (T : Distribution X))).symm
        ⟨(T : Distribution X), mem_supportedOn_support _⟩
        (restrictLocallyConstantCompact T.property f) := rfl

theorem compactSupportPairing_eq_of_agrees
    (T : compactlySupported (X := X)) (f : LocallyConstant X ℂ)
    (g : SchwartzBruhat X)
    (h : ∀ x ∈ support (T : Distribution X), g x = f x) :
    compactSupportPairing T f = (T : Distribution X) g :=
  compactSupportFunctional_eq_of_agrees T f g h

/-- Compatibility with the original full algebraic dual's evaluation. -/
@[simp]
theorem compactSupportPairing_testFunction (T : compactlySupported (X := X))
    (g : SchwartzBruhat X) :
    compactSupportPairing T ⟨(g : X → ℂ), g.locallyConstant⟩ =
      (T : Distribution X) g :=
  compactSupportPairing_eq_of_agrees T _ g (fun _ _ => rfl)

theorem compactSupportPairing_add_left (T S : compactlySupported (X := X))
    (f : LocallyConstant X ℂ) :
    compactSupportPairing (T + S) f =
      compactSupportPairing T f + compactSupportPairing S f :=
  LinearMap.congr_fun (map_add compactSupportPairing T S) f

theorem compactSupportPairing_smul_left (c : ℂ) (T : compactlySupported (X := X))
    (f : LocallyConstant X ℂ) :
    compactSupportPairing (c • T) f = c • compactSupportPairing T f :=
  LinearMap.congr_fun (map_smul compactSupportPairing c T) f

theorem compactSupportPairing_add_right (T : compactlySupported (X := X))
    (f g : LocallyConstant X ℂ) :
    compactSupportPairing T (f + g) =
      compactSupportPairing T f + compactSupportPairing T g :=
  map_add (compactSupportPairing T) f g

theorem compactSupportPairing_smul_right (T : compactlySupported (X := X))
    (c : ℂ) (f : LocallyConstant X ℂ) :
    compactSupportPairing T (c • f) = c • compactSupportPairing T f :=
  map_smul (compactSupportPairing T) c f

end Langlands.HarmonicAnalysis.Distribution
