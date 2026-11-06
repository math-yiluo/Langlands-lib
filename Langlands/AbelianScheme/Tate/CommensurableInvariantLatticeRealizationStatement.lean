import Langlands.AbelianScheme.Tate.RationalMonodromy
import Langlands.Global.IntegralFiniteAdeles
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Realizing commensurable monodromy-invariant full Tate lattices -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

open Langlands.AlgebraicGeometry.FiniteEtale

/-- Over a connected locally noetherian base on which every positive integer is
invertible, let `A` be an actual abelian scheme satisfying the explicit
finite-set fibre-affineness criterion. Every integral finite-adele submodule `L`
of the full rational Tate module of `A` at one geometric point that is stable
under the actual rational monodromy, and that is commensurable with the image of
the full integral Tate group by one positive integer bound, is the image of the
full integral Tate group of an actual abelian scheme `B` over the same base
under an actual rational isomorphism from `B` to `A`. The finite-etale torsion
target and the rational profinite-integer comparison are explicit inputs. This
is a statement target, not a proof. -/
def CommensurableInvariantLatticeRealizationStatement : Prop :=
  ∀ (htor : TorsionFiniteEtaleStatement.{u})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (S : Scheme.{u}) [IsLocallyNoetherian S] [ConnectedSpace S]
    (hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (A : AbelianScheme S),
    (∀ (F : Finset A.X.left) (t : S), (∀ x ∈ F, A.X.hom x = t) →
      ∃ W : A.X.left.Opens, IsAffineOpen W ∧ ∀ x ∈ F, x ∈ W) →
    letI : Module (Global.FiniteAdeles ℚ) (Rational A (Over.mk s) (fun _ => True)) :=
      finiteAdeleModule A (Over.mk s) (fun _ => True) h
    letI : Module (Global.integralFiniteAdeles ℚ)
        (Rational A (Over.mk s) (fun _ => True)) :=
      Module.compHom _ (Global.integralFiniteAdeles ℚ).subtype
    ∀ L : Submodule (Global.integralFiniteAdeles ℚ) (Rational A (Over.mk s) (fun _ => True)),
      (∀ (gamma : FundamentalGroup s hs) (w : Rational A (Over.mk s) (fun _ => True)),
        rationalMonodromy s hs htor A (fun _ => True) hu gamma w ∈ L ↔ w ∈ L) →
      (∃ n : ℕ, 0 < n ∧
        (∀ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
          n • GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x ∈ L) ∧
        (∀ w : Rational A (Over.mk s) (fun _ => True), w ∈ L →
          ∃ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
            GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x = n • w)) →
      ∃ (B : AbelianScheme S) (e : Rationalization.of B ≅ Rationalization.of A),
        ∀ w : Rational A (Over.mk s) (fun _ => True),
          w ∈ L ↔ ∃ x : GroupScheme.Tate.Full B.toGrp (Over.mk s),
            rationalHomMap (A := B) (B := A) (Over.mk s) (fun _ => True) e.hom
                (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x) = w

end Langlands.AbelianScheme.Tate
