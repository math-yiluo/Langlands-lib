import Langlands.Automorphic.AssociatedFactorStatement
import Langlands.Global.Factors.CuspidalPairSchemeSeries
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Sections of a cuspidal pair are square integrable up to an imaginary twist

For actual cuspidal realizations `T`, `T'` with unitary central characters, every section `φ` of
the cuspidal pair, transported to the points of the group scheme `GL_N`, `N = r + t + 2`, is
`ψ m_P^{iy}` for a real parameter `y` of the block parabolic `P` and a function `ψ` in Lapid's
space `A^2_P` (`IsSquareIntegrableInducedForm`). Multiplication by `m_P^{-iy}` cancels the unitary
exponents of the central characters on the split component `A_M`. This file states the
proposition and does not prove it. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.Global.CuspidalPairEisenstein

open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicBlockEisensteinGeometry AdelicGroupPoints GeneralLinearGroupPoints
open Langlands.Automorphic.GroupSchemeFunctions PrimitiveAdelicHeight
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

local instance squareTwistGLAffine {F : Type} [Field F] (n : ℕ) :
    IsAffine (groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance squareTwistGLAffineHom {F : Type} [Field F] (n : ℕ) :
    IsAffineHom (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  isAffineHom_groupScheme (n := Fin n) (R := CommRingCat.of F)

local instance squareTwistGLFiniteType {F : Type} [Field F] [NumberField F] (n : ℕ) :
    LocallyOfFiniteType (groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  have := (isConnectedReductive_generalLinear F (Fin n)).smooth
  inferInstance

local instance squareTwistParabolicAffine {F : Type} [Field F] {r t : ℕ} :
    IsAffine (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  blockParabolic_isAffine F (blockShape r t)

local instance squareTwistParabolicFiniteType {F : Type} [Field F] [NumberField F] {r t : ℕ} :
    LocallyOfFiniteType (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.hom :=
  IsClosedSubgroup.locallyOfFiniteType
    (isClosedSubgroup_blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t)))

local instance squareTwistLeviAffine {F : Type} [Field F] {r t : ℕ} :
    IsAffine (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.left :=
  have : IsAffineHom (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.hom :=
    (isClosedSubgroup_blockLeviHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).isAffineHom
  isAffine_of_isAffineHom (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
    (blockShapeWeight (blockShape r t))).X.hom

local instance squareTwistLeviFiniteType {F : Type} [Field F] [NumberField F] {r t : ℕ} :
    LocallyOfFiniteType (blockLeviScheme (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t))).X.hom :=
  IsClosedSubgroup.locallyOfFiniteType
    (isClosedSubgroup_blockLeviHom (Fin (r + t + 2)) (CommRingCat.of F)
      (blockShapeWeight (blockShape r t)))

/-- **Square-integrable imaginary twist of a cuspidal-pair section.** Let `F : Type` be a number
field with compact adele quotient, `T : CuspidalOperatorRealization F r` and
`T' : CuspidalOperatorRealization F t` actual cuspidal realizations with unitary central
characters, and `φ` a section of the cuspidal pair (`IsSection T T' φ`). Let `P` be the scheme
block parabolic of type `(r + 1, t + 1)` in `GL_N`, `N = r + t + 2`, with its block-unipotent
radical and block-diagonal Levi `M`, `K` the standard maximal compact subgroup, and `m_P^λ` the
height power of the Iwasawa height of `K`. Then there are a real parameter `y ∈ X^*(P) ⊗ ℝ` and a
function `ψ` on the adelic points of `GL_N` such that

* `φ (adelicHomeomorph x) = ψ x · m_P(x)^{iy}` for every adelic point `x`, and
* for all smooth-structure data `hsmooth`, `hcalc` of `GL_N`, `ψ` lies in Lapid's space `A^2_P`
  (`IsSquareIntegrableInducedForm`) for `K`, the standard matrix embedding and the block
  parabolic, radical and Levi. -/
def CuspidalPairSquareIntegrableTwistStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r t : ℕ)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
    ∀ φ : AdelicGL F (r + t + 2) → ℂ, IsSection T T' φ →
      ∃ (y : RealCharacterParameter F (blockParabolicScheme (Fin (r + t + 2)) (CommRingCat.of F)
          (blockShapeWeight (blockShape r t))))
        (ψ : AdelicGroupPoints F (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) → ℂ),
        (∀ x, φ (adelicHomeomorph F (r + t + 2) x) =
          ψ x * (isIwasawaCompact_blockParabolic F (blockShape r t)).heightPower
            (imaginaryParameter F _ y) x) ∧
        ∀ {d : ℕ} (hsmooth : SmoothOfRelativeDimension d
            (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)).X.hom)
          (hcalc : AdelicDifferentialCommutator F
            (groupScheme (Fin (r + t + 2)) (CommRingCat.of F)) hsmooth),
          IsSquareIntegrableInducedForm (standardCompactPoints F (r + t + 2))
            (isIwasawaCompact_blockParabolic F (blockShape r t)).isCompact
            (MatrixRepresentation.standard (Fin (r + t + 2)) (CommRingCat.of F)) hsmooth hcalc
            (blockParabolicHom (Fin (r + t + 2)) (CommRingCat.of F)
              (blockShapeWeight (blockShape r t)))
            (blockUnipotentInclusion F (blockShape r t)) (blockLeviInclusion F (blockShape r t)) ψ

end Langlands.Global.CuspidalPairEisenstein
