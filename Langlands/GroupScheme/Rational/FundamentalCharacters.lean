import Langlands.GroupScheme.Rational.FundamentalRepresentations
import Langlands.GroupScheme.Rational.TraceClassFunctions
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Actual fundamental trace characters and their invariant-generation statement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

namespace FundamentalRepresentation

variable {a : p.base.support} (F : p.FundamentalRepresentation a)

/-- The fundamental character is the trace of the supplied actual representation,
as an element of the scheme-theoretic invariant coordinate algebra. -/
def character : ClassFunctions.algebra G :=
  MatrixRepresentation.traceClassFunction F.representation

/-- Fundamental characters evaluate to actual representation traces over every
commutative coefficient algebra, including nonreduced algebras. -/
theorem character_evaluate {A : Type u} [CommRing A] [Algebra k A]
    (g : Lie.AffinePoints G A) :
    Lie.pointCoordinates G g (F.character).val =
      Matrix.trace (F.representation.affineMatrix
        (CommAlgCat.of (CommRingCat.of k) A) g : Matrix (Fin F.dimension) (Fin F.dimension) A) :=
  MatrixRepresentation.traceClassFunction_evaluate F.representation g

end FundamentalRepresentation

variable (p) {r : ℕ}

/-- The polynomial map into the actual invariant algebra given by fundamental
trace characters in the supplied simple-root ordering. -/
def fundamentalCharacterMap (e : Fin r ≃ p.base.support)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a) :
    MvPolynomial (Fin r) k →ₐ[k] ClassFunctions.algebra G :=
  MvPolynomial.aeval fun j => (F (e j)).character

@[simp] theorem fundamentalCharacterMap_X (e : Fin r ≃ p.base.support)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a) (j : Fin r) :
    p.fundamentalCharacterMap e F (MvPolynomial.X j) = (F (e j)).character :=
  MvPolynomial.aeval_X _ _

/-- The polynomial algebra equivalence obtained if the fundamental characters
freely generate the actual invariant algebra. -/
def fundamentalCharacterEquiv (e : Fin r ≃ p.base.support)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)
    (h : Function.Bijective (p.fundamentalCharacterMap e F)) :
    MvPolynomial (Fin r) k ≃ₐ[k] ClassFunctions.algebra G :=
  AlgEquiv.ofBijective (p.fundamentalCharacterMap e F) h

@[simp] theorem fundamentalCharacterEquiv_apply (e : Fin r ≃ p.base.support)
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)
    (h : Function.Bijective (p.fundamentalCharacterMap e F))
    (q : MvPolynomial (Fin r) k) :
    p.fundamentalCharacterEquiv e F h q = p.fundamentalCharacterMap e F q := rfl

end SplitPinning

/-- Over an algebraically closed field, the actual fundamental trace characters
freely generate the canonical invariant algebra of a simply connected split group. -/
def SplitFundamentalCharacterGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ (r : ℕ) (e : Fin r ≃ p.base.support)
      (F : ∀ a : p.base.support, p.FundamentalRepresentation a),
      Function.Bijective (p.fundamentalCharacterMap e F)

end Langlands.GroupScheme
