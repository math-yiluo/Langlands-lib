import Langlands.Galois.HeckeAvatarFinitePart
import Langlands.Galois.CompatibleFamily
import Langlands.Global.AdelicFunctoriality.Extension

/-! # The idele correction at a coefficient place -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global IsDedekindDomain
open scoped NumberField

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]

/-- The place of `K` below the coefficient place for the specified embedding. -/
def avatarPlaceBelow (e : K →+* L) (lam : FinitePlace L) : FinitePlace K :=
  letI : Algebra K L := e.toAlgebra
  lam.under (𝓞 K)

/-- The actual continuous completion embedding for one term of the correction. -/
def avatarCompletionMap (e : K →+* L) (lam : FinitePlace L) :
    FiniteCompletion K (avatarPlaceBelow e lam) →+* FiniteCompletion L lam := by
  letI : Algebra K L := e.toAlgebra
  letI : lam.asIdeal.LiesOver (avatarPlaceBelow e lam).asIdeal :=
    Ideal.over_under lam.asIdeal
  exact AdelicFunctoriality.FiniteExtension.completionMap (avatarPlaceBelow e lam) lam

/-- The finite factor of the idele supported at one finite place. -/
def singleFiniteIdele (v : FinitePlace K) (a : (FiniteCompletion K v)ˣ) : FiniteIdeles K :=
  (ideleProductEquiv K (finiteIdeleInclusion K v a)).2

/-- The actual inclusion from the units of the completed integer ring into the
units of its fraction field, continuous for the units topologies. -/
def completionIntegerUnitsInclusion (lam : FinitePlace L) :
    (lam.adicCompletionIntegers L)ˣ →ₜ* (FiniteCompletion L lam)ˣ where
  toMonoidHom := Units.map (lam.adicCompletionIntegers L).subtype.toMonoidHom
  continuous_toFun := continuous_subtype_val.units_map _

/-- The finite part times the infinity-type monomial evaluated on the
coordinates over the coefficient prime. The exponents have the sign of the
complex infinity type because the finite part is its inverse on principals. -/
def correctedIdeleValue (t : InfinityType K) (emb : (K →+* ℂ) → (K →+* L))
    (φ : FiniteIdeles K →* Lˣ) (lam : FinitePlace L) (x : Ideles K) :
    (FiniteCompletion L lam)ˣ :=
  Units.map (NumberField.FinitePlace.embedding lam).toMonoidHom
      (φ (ideleProductEquiv K x).2) *
    ∏ σ : K →+* ℂ,
      (Units.map (avatarCompletionMap (emb σ) lam).toMonoidHom
        (finiteIdeleProjection K (avatarPlaceBelow (emb σ) lam) x)) ^ t σ

/-- The corrected value descends continuously to actual idele classes, lands in
integral units, and agrees away from the coefficient prime with the embedded
finite part on every one-place idele. -/
def HeckeAvatarIdeleCorrectionStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (L : Type uL) [Field L] [NumberField L]
    (χ : HeckeCharacter K) (t : InfinityType K) (ι : L →+* ℂ)
    (emb : (K →+* ℂ) → (K →+* L)) (φ : FiniteIdeles K →* Lˣ),
    χ.HasPrescribedInfinityComponent (InfinityType.toCharacter t) →
    (∀ σ, ι.comp (emb σ) = σ) → IsHeckeFinitePart χ ι φ →
    ∀ lam : FinitePlace L,
      ∃ η : IdeleClasses K →ₜ* (lam.adicCompletionIntegers L)ˣ,
        (∀ x : Ideles K, completionIntegerUnitsInclusion lam (η (ideleClassMap K x)) =
          correctedIdeleValue t emb φ lam x) ∧
        ∀ v : FinitePlace K, residueCharacteristic v ≠ residueCharacteristic lam →
          ∀ a : (FiniteCompletion K v)ˣ,
            completionIntegerUnitsInclusion lam (η (finiteClassInclusion K v a)) =
              Units.map (NumberField.FinitePlace.embedding lam).toMonoidHom
                (φ (singleFiniteIdele v a))

end Langlands.GaloisRepresentation
