import Langlands.AlgebraicGeometry.SmoothDomainStalksStatement
import Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizationsProof

/-! # Domain stalks of smooth schemes over arbitrary fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

private theorem smoothDomainStalks_of_domainLocalizations
    (hRing : Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizations.{u, u}) :
    SmoothDomainStalks.{u} := by
  intro K _ X p hp x
  let := hp
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  let U := X.affineCover.X i
  let q := X.affineCover.f i ≫ p
  have : Smooth q := inferInstance
  let g : CommRingCat.of K ⟶ Γ(U, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ q.appTop
  have hg : g.hom.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
    (HasRingHomProperty.appTop @Smooth q inferInstance)
  algebraize [g.hom]
  have : Algebra.Smooth K Γ(U, ⊤) := RingHom.smooth_algebraMap.mp hg
  let P := ((isAffineOpen_top U).primeIdealOf ⟨y, trivial⟩).asIdeal
  have : IsDomain (Localization.AtPrime P) := hRing K _ inferInstance P
  let := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨y, trivial⟩ : (⊤ : U.Opens))
  have := (isAffineOpen_top U).isLocalization_stalk ⟨y, trivial⟩
  have : IsDomain (U.presheaf.stalk y) :=
    (IsLocalization.algEquiv P.primeCompl
      (U.presheaf.stalk y) (Localization.AtPrime P)).toRingEquiv.toMulEquiv.isDomain _
  exact
    (asIso ((X.affineCover.f i).stalkMap y)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

/-- Every stalk of a scheme smooth over any field is a domain. -/
theorem smoothDomainStalks : SmoothDomainStalks.{u} :=
  smoothDomainStalks_of_domainLocalizations
    Langlands.CommutativeAlgebra.smoothAlgebraDomainLocalizations.{u, u}

end Langlands.AlgebraicGeometry
