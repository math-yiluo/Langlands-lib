import Langlands.AlgebraicGeometry.ClosedFibreOpenIntegrality
import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality
import Langlands.AlgebraicGeometry.SmoothReducedBase
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime

/-! # Normal stalks over an integrally closed domain -/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

namespace Langlands.AlgebraicGeometry

/-- A scheme smooth over the spectrum of an integrally closed domain has normal stalks. -/
def SmoothNormalDomainStalksStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R] {X : Scheme.{u}}
    (p : X ⟶ Spec R), Smooth p → HasNormalStalks X

/-- The actual stalks of a smooth scheme over an integrally closed domain
are integrally closed domains. -/
theorem smoothNormalDomainStalks : SmoothNormalDomainStalksStatement.{u} := by
  intro R _ _ X p hp x
  let := hp
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let q := X.affineCover.f i ≫ p
  have : Smooth q := inferInstance
  let g : R ⟶ Γ(U, ⊤) := (Scheme.ΓSpecIso R).inv ≫ q.appTop
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appTop @Smooth q inferInstance)
  algebraize [g.hom]
  have : Algebra.Smooth R Γ(U, ⊤) := RingHom.smooth_algebraMap.mp hg
  let z : (⊤ : U.Opens) := ⟨y, trivial⟩
  let P := ((isAffineOpen_top U).primeIdealOf z).asIdeal
  let := TopCat.Presheaf.algebra_section_stalk U.presheaf z
  have := (isAffineOpen_top U).isLocalization_stalk z
  let h :=
    P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.solution
      R Γ(U, ⊤) P (U.presheaf.stalk y)
  let e := (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv.symm
  let := h.1
  exact ⟨Function.Injective.isDomain e.symm e.symm.injective, h.2.of_equiv e⟩

/-- A smooth morphism with geometrically connected fibres over an integral base
has integral source. -/
theorem isIntegral_of_smooth_geometricallyConnected {X S : Scheme.{u}} [IsIntegral S]
    (p : X ⟶ S) [Smooth p] [GeometricallyConnected p] : IsIntegral X := by
  let := geometricallyIntegral_of_smooth_geometricallyConnected p
  have : IrreducibleSpace X := GeometricallyIrreducible.irreducibleSpace p p.isOpenMap
  have : IsReduced X := SmoothReducedBase.isReduced_of_smooth_of_isReduced p
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end Langlands.AlgebraicGeometry
