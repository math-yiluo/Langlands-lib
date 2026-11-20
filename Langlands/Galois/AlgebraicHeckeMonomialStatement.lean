import Langlands.Galois.HeckeCharacterRealization
import Langlands.Galois.WeakAssociation
import Langlands.Global.Arithmetic.HarrisSetup
import Langlands.Global.CompletionPadic
import Langlands.Global.HeckeNormPower
import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
import Langlands.LocalFactor.RankOne
import Langlands.Automorphic.Unramified.WeakInduction
import Langlands.Weil.Representation.Induction

/-! # Algebraic Hecke characters and their monomial families -/

noncomputable section

universe uV

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.Automorphic.Unramified.WeakInduction
open Langlands.LocalClassField Langlands.LocalFactor.RankOne
open NumberField (IsCMField IsTotallyComplex)

variable {K L : Type} [Field K] [Field L] [NumberField K] [NumberField L]

/-- At a place away from the coefficient residue characteristic, the avatar's
restriction to the actual Weil group reads the finite Hecke component through
geometric reciprocity and the common coefficient field. -/
def IsLocalLambdaAdicRealization (ι : L →+* ℂ) (lam : FinitePlace L)
    (χ : HeckeCharacter K) (ψ : LambdaAdicCharacter K L lam) (v : FinitePlace K) : Prop :=
  let F := CompletionPadic.padicField v
  ∀ e : ReciprocityCandidate F,
    GeometricWeilReciprocityRelation F F.canonicalTopologicalData e →
      ∀ w : Weil.Local.localWeilGroup F, ∃ a : L,
        (χ.finiteComponent v (reciprocityUnits F e w) : ℂ) = ι a ∧
        (ψ.atFinitePlace v (Weil.Local.localProjection F w) : FiniteCompletion L lam) =
          NumberField.FinitePlace.embedding lam a

/-- The algebraic Hecke characters in a finite family have avatars at all
coefficient places for one number field and one complex embedding. The local
clause uses only places away from the coefficient residue characteristic. -/
def AlgebraicHeckeAvatarExistenceStatement : Prop :=
  ∀ (I : Type) [Fintype I] (K : I → Type)
    [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsTotallyComplex (K i)]
    (χ : ∀ i, HeckeCharacter (K i)),
    (∀ i, Harris.IsAlgebraic (χ i)) →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →+* ℂ)
      (ψ : ∀ i (lam : FinitePlace L), LambdaAdicCharacter (K i) L lam),
      (∀ i lam, IsLambdaAdicRealization ι lam (χ i) (ψ i lam)) ∧
      (∀ i lam (v : FinitePlace (K i)),
        residueCharacteristic v ≠ residueCharacteristic lam →
        IsLocalLambdaAdicRealization ι lam (χ i) (ψ i lam) v)

/-- An actual scalar line induced from the image of the absolute Galois group
under the specified field embedding. The character on the image is obtained
using the inverse of the injective absolute-Galois map. -/
def IsInducedFromLambdaAdicCharacter {E : Type} [Field E]
    (f : E →+* K) (lam : FinitePlace L) (ψ : LambdaAdicCharacter K L lam)
    (A : LambdaAdic.{0, 0, uV} E L lam) : Prop :=
  let g := (Field.absoluteGaloisGroup.map f).toMonoidHom
  ∃ (hi : Function.Injective g) (hf : g.range.FiniteIndex),
    letI := hf
    let χ := ψ.toMonoidHom.comp (MonoidHom.ofInjective hi).symm.toMonoidHom
    let line : FiniteRepresentation.{0, 0, uV} (FiniteCompletion L lam) g.range :=
      FiniteRepresentation.of (Langlands.twist χ
        (Representation.trivial (FiniteCompletion L lam) g.range (ULift.{uV} (FiniteCompletion L lam))))
    Nonempty (FiniteRepresentation.Equiv (FiniteRepresentation.induce g.range line) A.val)

/-- The integral infinity-type normalization used to construct the adic
family. The unitary character remains the input of the Euler comparison. -/
def algebraicNormTwist (b : ℕ) (χ : HeckeCharacter K) : HeckeCharacter K :=
  χ * HeckeCharacter.normPower K ((b : ℂ) / 2)

/-- Inducing the avatars of the algebraic normalization gives a pure
collection. After unitarization its Euler polynomials are precisely the
induction polynomials of the original unitary character. -/
def HeckeMonomialCollectionStatement : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [IsCMField K] [Algebra E K] (χ : HeckeCharacter K) (b : ℕ),
    χ.IsUnitary → Harris.IsAlgebraicAfterTwist b χ →
    ∀ (L : Type) [Field L] [NumberField L] (ι : L →+* ℂ)
      (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam),
      (∀ lam, IsLambdaAdicRealization ι lam (algebraicNormTwist b χ) (ψ lam)) →
      (∀ lam (w : FinitePlace K), residueCharacteristic w ≠ residueCharacteristic lam →
        IsLocalLambdaAdicRealization ι lam (algebraicNormTwist b χ) (ψ lam) w) →
      ∃ (R : Collection.{0, 0, uV} E L ∅) (S : Finset (FinitePlace E))
        (P : FinitePlace E → Polynomial L),
        (∀ lam, IsInducedFromLambdaAdicCharacter (algebraMap E K) lam.val
          (ψ lam.val) (R lam)) ∧ HasRank ∅ R (Module.finrank E K) ∧
        MatchesOutside ∅ R S P ∧
        ∀ v, v ∉ S →
          Cohomology.Weights.IsPurePolynomial (residueCardinality v) (-(b : ℤ)) (P v).reverse ∧
          IsUnramifiedAbove χ v ∧
          ∀ ϖ, IsUniformizerFamily v ϖ →
            unitaryEulerPolynomial ((P v).map ι) = inducedEulerPolynomial χ v ϖ

end Langlands.GaloisRepresentation
