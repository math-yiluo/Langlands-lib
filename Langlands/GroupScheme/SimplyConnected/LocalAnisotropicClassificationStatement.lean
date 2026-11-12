import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.CentralSimpleNormOne
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Anisotropic simply connected absolutely almost-simple groups over local fields

This module states the specialization of Bruhat–Tits (1967), Proposition 6, to
nonarchimedean local fields, using the actual reduced-norm-one group scheme of a
finite-dimensional central division algebra. It supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every affine, anisotropic, simply connected, absolutely almost-simple group over a
nonarchimedean local field is the reduced-norm-one group of a finite-dimensional central
division algebra. No characteristic restriction is imposed. -/
def LocalAnisotropicSimplyConnectedClassificationStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom],
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → IsAnisotropic G →
      ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D) (_ : FiniteDimensional K D)
        (_ : Algebra.IsCentral K D),
        Nonempty (G ≅ CentralSimpleUnits.normOne K D)

end Langlands.GroupScheme
