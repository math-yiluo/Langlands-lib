import Langlands.GroupScheme.Rational.FundamentalCharacters
import Langlands.GroupScheme.Rational.SteinbergRestriction
import Langlands.CommutativeAlgebra.TriangularPolynomial

/-! # Actual triangular character restriction and the canonical quotient assembly -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.CommutativeAlgebra

namespace Langlands.GroupScheme
namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

/-- Actual fundamental characters restrict to a polynomial substitution with
unit diagonal and well-founded lower-variable remainders. -/
def HasTriangularFundamentalRestriction
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a) : Prop :=
  ∃ rel : Fin r → Fin r → Prop, WellFounded rel ∧
    ∃ (c : Fin r → kˣ) (f : Fin r → MvPolynomial (Fin r) k),
      TriangularPolynomial.HasLowerRemainders rel f ∧
      ∀ j : Fin r,
        steinbergRestriction e x n ((F (e j)).character) =
          MvPolynomial.C (c j : k) * MvPolynomial.X j + f j

/-- Free invariant generation and the actual triangular character formula imply
the exact canonical quotient isomorphism on the supplied product. -/
theorem steinbergProduct_rho_isIso_of_fundamental_triangular
    (F : ∀ a : p.base.support, p.FundamentalRepresentation a)
    (hgen : Function.Bijective (p.fundamentalCharacterMap e F))
    (htri : HasTriangularFundamentalRestriction e x n F) :
    IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) := by
  obtain ⟨rel, wf, c, f, hf, hχ⟩ := htri
  have hmap :
      (steinbergRestriction e x n).comp (p.fundamentalCharacterMap e F) =
        TriangularPolynomial.substitution c f := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa only [AlgHom.comp_apply, fundamentalCharacterMap_X,
      TriangularPolynomial.substitution, MvPolynomial.aeval_X] using hχ j
  apply steinbergProduct_rho_isIso_of_polynomial_generators e x n
    (fun j => (F (e j)).character) hgen
  change Function.Bijective
    ((steinbergRestriction e x n).comp (p.fundamentalCharacterMap e F))
  rw [hmap]
  exact TriangularPolynomial.substitution_bijective wf c f hf

end SplitPinning

/-- Over an algebraically closed field, actual fundamental trace characters have
a triangular restriction on every supplied simply connected Steinberg product. -/
def SplitSteinbergCharacterTriangularStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ (r : ℕ) (e : Fin r ≃ p.base.support)
      (F : ∀ a : p.base.support, p.FundamentalRepresentation a)
      (x : p.NormalizedSimpleRootParametrizations)
      (n : p.SimpleReflectionRepresentatives),
      SplitPinning.HasTriangularFundamentalRestriction e x n F

/-- Conditional assembly over algebraically closed fields. The three structural
propositions are explicit inputs, each of which still needs its own proof. -/
theorem splitSteinbergQuotient_algClosed_of_character_inputs
    (hExists : SplitFundamentalRepresentationsExistStatement.{u})
    (hGen : SplitFundamentalCharacterGenerationStatement.{u})
    (hTri : SplitSteinbergCharacterTriangularStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G) (hsc : IsSimplyConnected G)
    (r : ℕ) (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives) :
    IsIso (SplitPinning.steinbergProduct e x n ≫ ClassFunctions.rho G) := by
  classical
  let F : ∀ a : p.base.support, p.FundamentalRepresentation a :=
    fun a => Classical.choice (hExists k G p hsc a)
  exact SplitPinning.steinbergProduct_rho_isIso_of_fundamental_triangular e x n F
    (hGen k G p hsc r e F) (hTri k G p hsc r e F x n)

end Langlands.GroupScheme
