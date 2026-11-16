import Langlands.AlgebraicGeometry.Picard.RosatiRationalInverseStatement
import Langlands.AbelianScheme.IsogenyInverse
import Langlands.AbelianScheme.IsogenyInverseSpecialization
import Langlands.GroupScheme.CentralIsogeny.KernelTorsion

/-! # Rational invertibility of actual geometric polarizations -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Rosati

/-- Every actual geometric polarization is invertible in the existing rational
Hom category, with all construction prerequisites retained. -/
theorem rationalInverse : RationalInverseStatement.{u} := by
  intro P k _ _ _ A W lam hlam
  have hf : IsIsogeny lam := hlam.1
  apply isogenyInverseStatement_of_commGroupScheme
    Langlands.CommGroupScheme.isogenyInverse _ A (W.dual P) lam hf
  let K := Langlands.GroupScheme.kernel (groupHom lam)
  have : IsFinite K.X.hom :=
    MorphismProperty.of_isPullback
      (Langlands.GroupScheme.kernel_isPullback_scheme (groupHom lam)) hf.1
  obtain ⟨n, hn, hpow⟩ := Langlands.GroupScheme.exists_pow_eq_one_of_isFinite K
  refine ⟨(n : ℤ), by exact_mod_cast hn.ne', ?_⟩
  apply Grp.hom_ext
  simpa only [Langlands.GroupScheme.multiplication_hom, Grp.Hom.hom_one,
    Mon.Hom.hom_one, zpow_natCast]
    using hpow K.X (𝟙 K.X)

end Langlands.AbelianScheme.Rosati
