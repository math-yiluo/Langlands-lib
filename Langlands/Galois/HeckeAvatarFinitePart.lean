import Langlands.Global.HeckeCharacter
import Langlands.Global.InfinityType

/-! # The common algebraic finite part of a Hecke character -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global NumberField

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L]

/-- A coefficient-field lift of the finite part. The open kernel expresses
continuity when the coefficient field is regarded as discrete. -/
def IsHeckeFinitePart (χ : HeckeCharacter K) (ι : L →+* ℂ)
    (φ : FiniteIdeles K →* Lˣ) : Prop :=
  IsOpen (φ.ker : Set (FiniteIdeles K)) ∧
  ∀ x : FiniteIdeles K, Units.map ι.toMonoidHom (φ x) = χ.atFinite x

/-- One number field contains the values on all finite ideles and the images of
all complex embeddings of the base field. The exceptional set is the set of
finite places where the complex Hecke character is ramified. -/
def AlgebraicHeckeFinitePartStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [IsTotallyComplex K]
    (χ : HeckeCharacter K) (t : InfinityType K),
    χ.HasPrescribedInfinityComponent (InfinityType.toCharacter t) →
    ∃ (L : Type uL) (hL : Field L),
      letI : Field L := hL
      ∃ (hnum : NumberField L),
        letI : NumberField L := hnum
        ∃ (ι : L →+* ℂ) (emb : (K →+* ℂ) → (K →+* L))
          (φ : FiniteIdeles K →* Lˣ) (S : Finset (Global.FinitePlace K)),
          (∀ σ, ι.comp (emb σ) = σ) ∧ IsHeckeFinitePart χ ι φ ∧
          ∀ v, v ∉ S ↔ χ.IsUnramifiedAt v

end Langlands.GaloisRepresentation
