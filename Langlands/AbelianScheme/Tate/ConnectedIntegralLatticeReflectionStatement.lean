import Langlands.AbelianScheme.Tate.Rational
import Langlands.AbelianScheme.TorsionFiniteEtaleStatement
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Integral Tate images reflecting rational isomorphisms over connected bases -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

/-- Over a connected locally noetherian base on which every positive integer is
invertible, a rational isomorphism of actual abelian schemes whose two arrows
carry the images of the full integral Tate groups at one geometric point into
each other is the rationalization of an actual isomorphism. The finite-etale
torsion target is an explicit hypothesis. This is a statement target, not a
proof. -/
def ConnectedIntegralLatticeReflectionStatement : Prop :=
  TorsionFiniteEtaleStatement.{u} →
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] [ConnectedSpace S],
    (∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤))) →
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ S) (A B : AbelianScheme S)
      (e : Rationalization.of A ≅ Rationalization.of B),
      (∀ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
        ∃ y : GroupScheme.Tate.Full B.toGrp (Over.mk s),
          rationalHomMap (A := A) (B := B) (Over.mk s) (fun _ => True) e.hom
              (GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x) =
            GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) y) →
      (∀ y : GroupScheme.Tate.Full B.toGrp (Over.mk s),
        ∃ x : GroupScheme.Tate.Full A.toGrp (Over.mk s),
          rationalHomMap (A := B) (B := A) (Over.mk s) (fun _ => True) e.inv
              (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) y) =
            GroupScheme.Tate.toRational A.toGrp (Over.mk s) (fun _ => True) x) →
      ∃ g : A ≅ B,
        Rationalization.ofHom g.hom = e.hom ∧ Rationalization.ofHom g.inv = e.inv

end Langlands.AbelianScheme.Tate
