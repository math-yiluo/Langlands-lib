import Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement
import Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof

/-!
# Scalar covariance of supported descent through an open subspace

Extension by zero and closed restriction commute with compatible
homeomorphisms. Surjectivity of closed restriction then reduces covariance of
the chosen descent `descendInOpen` to the ambient covariance.
-/

noncomputable section

namespace Langlands.HarmonicAnalysis

open Hecke.TestFunction

universe u

namespace SchwartzBruhat

/-- Extension by zero commutes with compatible ambient and open-subspace maps. -/
theorem extendZero_pullback {X : Type u} [TopologicalSpace X] [T2Space X] {U : Set X}
    (hU : IsOpen U) (e : X ≃ₜ X) (eU : U ≃ₜ U)
    (he : ∀ x : U, (eU x).val = e x.val) (f : SchwartzBruhat U) :
    extendZero hU (pullback eU f) = pullback e (extendZero hU f) := by
  ext x
  by_cases hx : x ∈ U
  · change extendZero hU _ (⟨x, hx⟩ : U).val = extendZero hU f (e x)
    rw [extendZero_apply_subtype, ← he ⟨x, hx⟩, extendZero_apply_subtype]
    rfl
  · have hex : e x ∉ U := by
      intro hex
      let y : U := ⟨e x, hex⟩
      have hy : (eU.symm y).val = x := by
        exact e.injective ((he (eU.symm y)).symm.trans
          (congrArg Subtype.val (eU.apply_symm_apply y)))
      exact hx (hy ▸ (eU.symm y).property)
    simp only [extendZero_apply_of_not_mem hU _ hx, pullback_apply,
      extendZero_apply_of_not_mem hU _ hex]

/-- Closed restriction commutes with compatible maps of the two spaces. -/
theorem restrictClosed_pullback {Y : Type u} [TopologicalSpace Y] {Z : Set Y}
    (hZ : IsClosed Z) (e : Y ≃ₜ Y) (eZ : Z ≃ₜ Z)
    (he : ∀ z : Z, (eZ z).val = e z.val) (f : SchwartzBruhat Y) :
    restrictClosed hZ (pullback e f) = pullback eZ (restrictClosed hZ f) := by
  ext z
  change f (e z.val) = f (eZ z).val
  rw [he]

end SchwartzBruhat

namespace Distribution

/-- Scalar covariance of the actual chosen supported descent through an open
subspace. -/
theorem supportedDescentCovariance : SupportedDescentCovarianceStatement.{u} := by
  intro X _ _ _ _ U Z hU hZU D e eU eZ c he heZ hD
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  ext φ
  obtain ⟨f, rfl⟩ :=
    SchwartzBruhat.closedRestrictionSurjective U ((Subtype.val : U → X) ⁻¹' Z) hZU φ
  change descendInOpen hU hZU D
      (pullback eZ (SchwartzBruhat.restrictClosed hZU f)) =
    c • descendInOpen hU hZU D (SchwartzBruhat.restrictClosed hZU f)
  rw [← SchwartzBruhat.restrictClosed_pullback hZU eU eZ heZ,
    descendInOpen_apply_restrictClosed, descendInOpen_apply_restrictClosed,
    SchwartzBruhat.extendZero_pullback hU e eU he]
  exact congrArg (fun T : Distribution X =>
    T (SchwartzBruhat.extendZero hU f)) hD

end Distribution

end Langlands.HarmonicAnalysis
