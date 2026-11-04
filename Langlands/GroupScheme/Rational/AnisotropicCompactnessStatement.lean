import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.PointTopology
import Mathlib.NumberTheory.LocalField.Basic

/-! # Compact rational points and anisotropy over a nonarchimedean local field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The locally compact consequence of KP Theorem 2.2.9, in the canonical
rational-point topology and with split-rank-zero anisotropy. -/
def AnisotropicCompactness
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) : Prop :=
  letI : IsAffineHom G.X.hom := hG.isAffineHom
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  IsCompact (Set.univ : Set (rationalPoints G)) ↔ IsAnisotropic G

/-- For every actual connected reductive group over every nonarchimedean local
field, its full rational-point set is compact exactly when its split rank is zero.
This is a statement target, with no compactness or boundedness premise. -/
def AnisotropicCompactnessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    AnisotropicCompactness G hG

end Langlands.GroupScheme
