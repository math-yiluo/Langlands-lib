import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Actual stalk quotients of closed immersions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.ClosedImmersion

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]

/-- The kernel on actual stalks is the localization of the affine-section kernel. -/
lemma ker_stalkMap_eq_map (x : X) (U : Y.Opens) (hU : IsAffineOpen U)
    (hx : i x ∈ U) :
    RingHom.ker (i.stalkMap x).hom =
      (RingHom.ker (i.app U).hom).map (Y.presheaf.germ U (i x) hx).hom := by
  let V := i ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage i
  let := Y.presheaf.algebra_section_stalk (⟨i x, hx⟩ : U)
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  have := hU.isLocalization_stalk ⟨i x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  let p := (hU.primeIdealOf ⟨i x, hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have hcomap : q.comap (i.app U).hom = p := by
    simpa [Scheme.Hom.appLE, V, p, q] using
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hx)
  have hT : p.primeCompl.map (i.app U).hom = q.primeCompl := by
    simpa only [hcomap] using
      Ideal.map_primeCompl_comap_of_surjective _ (i.app_surjective U hU) q
  have hmap :
      IsLocalization.map (X.presheaf.stalk x) (i.app U).hom
        (hT.symm ▸ p.primeCompl.le_comap_map) = (i.stalkMap x).hom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    simp only [RingHom.comp_apply, IsLocalization.map_eq]
    exact (i.germ_stalkMap_apply U x hx a).symm
  rw [← hmap]
  exact IsLocalization.ker_map (X.presheaf.stalk x) (i.app U).hom hT

/-- The actual target stalk is the quotient of the source stalk by the extended
affine-section kernel, as an algebra over that source stalk. -/
def quotientStalkAlgEquiv (x : X) (U : Y.Opens) (hU : IsAffineOpen U)
    (hx : i x ∈ U) :
    letI := (i.stalkMap x).hom.toAlgebra
    ((Y.presheaf.stalk (i x)) ⧸
      (RingHom.ker (i.app U).hom).map (Y.presheaf.germ U (i x) hx).hom) ≃ₐ[
        Y.presheaf.stalk (i x)] X.presheaf.stalk x := by
  letI := (i.stalkMap x).hom.toAlgebra
  exact (Ideal.quotientEquivAlgOfEq (Y.presheaf.stalk (i x))
    (ker_stalkMap_eq_map i x U hU hx).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective
        (f := Algebra.ofId (Y.presheaf.stalk (i x)) (X.presheaf.stalk x))
        (i.stalkMap_surjective x))

end Langlands.AlgebraicGeometry.Modules.ClosedImmersion
