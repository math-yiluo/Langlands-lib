import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.CentralSimpleBinaryRoots
import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.GroupScheme.Examples.HermitianRootReflectionAction
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Absolutely almost-simple simply connected groups of split rank one over local fields

This module states the classification, due to Kneser in characteristic zero and
to Bruhat–Tits in general, of absolutely almost-simple simply connected groups
of split rank one over a nonarchimedean local field, in the form used by
Prasad–Raghunathan (1985), §2. It supplies no proof.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over a nonarchimedean local field `K`, every affine, simply connected, absolutely
almost-simple group scheme `G` of split rank one is (i) `SL₂(D)` for a finite-dimensional
central division algebra `D`; or (ii) the special unitary group of a Witt-index-one
hermitian form in 3 or 4 variables relative to a separable quadratic extension of `K`; or
(iii), for a quaternion central division algebra `D` with an involution `σ` of the first kind
such that `dim_K D^σ = 3`, the symplectic group of a nondegenerate `σ`-antihermitian form of
rank 2 or 3 and Witt index one, or a spin group of a nondegenerate `σ`-quadratic form of
rank 4 or 5 and Witt index one. (Prasad–Raghunathan 1985, §2.) -/
def LocalRankOneClassificationStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom],
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → splitRank G = 1 →
      -- (i) `SL₂(D)` for a finite-dimensional central division algebra `D`
      (∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D) (_ : FiniteDimensional K D)
          (_ : Algebra.IsCentral K D),
          Nonempty (G ≅ CentralSimpleUnits.BinaryRoot.groupScheme K D)) ∨
      -- (ii) `SU` of a Witt-index-one Hermitian form in 3 or 4 variables
      (∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
          (_ : Algebra.IsQuadraticExtension K L) (_ : Algebra.IsSeparable K L) (m : ℕ),
          (m = 1 ∨ m = 2) ∧
          ∃ (H : HermitianRoot.DiagonalForm (SU3Root.fieldInvolution K L) (Fin m))
            (w : Fin m → Lˣ) (hw : ∀ i, (w i : L) = H.weight i),
            H.IsAnisotropic ∧
              Nonempty (G ≅ HermitianRoot.SchemeModel.groupScheme K L H w hw)) ∨
      -- (iii) quaternionic symplectic groups in 2 or 3 variables and spin groups in
      -- 4 or 5 variables, of Witt index one
      (∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D) (_ : Algebra.IsCentral K D)
          (_ : FiniteDimensional K D),
          Module.finrank K D = 4 ∧
          ∃ σ : Quaternionic.FirstKindInvolution K D,
            Module.finrank K σ.symmetricSubspace = 3 ∧
            ((∃ (m : ℕ) (_ : NeZero m), (m = 2 ∨ m = 3) ∧
                ∃ H : Matrix (Fin m) (Fin m) D,
                  σ.IsAntihermitian H ∧ IsUnit H ∧ σ.wittIndex H = 1 ∧
                    Nonempty (G ≅ σ.symplecticGroup H)) ∨
              (∃ m : ℕ, (m = 4 ∨ m = 5) ∧
                ∃ q : σ.QuadraticForms (Fin m),
                  σ.IsNondegenerateQuadratic q ∧ σ.quadraticWittIndex q = 1 ∧
                    ∃ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π)))

end Langlands.GroupScheme
