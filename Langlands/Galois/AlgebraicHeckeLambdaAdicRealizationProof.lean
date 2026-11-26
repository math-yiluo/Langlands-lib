import Langlands.Galois.HeckeAvatarConstruction
import Langlands.Galois.HeckeAvatarFinitePartProof
import Langlands.Galois.HeckeAvatarCorrectionProof
import Langlands.Galois.HeckeAvatarInverseLimitProof
import Langlands.Galois.FiniteHeckeAvatarLiftProof
import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness

/-! # Compatible rank-one realizations of algebraic Hecke characters: proof -/

noncomputable section

universe uK uL

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global

/-- Every algebraic Hecke character of a totally complex number field has a
uniform family of adic avatars: one coefficient number field with a complex
embedding, its exact conductor support and common values in the coefficient
field at uniformizers. -/
theorem exists_isUniformHeckeAvatar (K : Type uK) [Field K] [NumberField K]
    [NumberField.IsTotallyComplex K] (χ : HeckeCharacter K) (hχ : Harris.IsAlgebraic χ) :
    ∃ (L : Type uL) (fieldL : Field L),
      letI : Field L := fieldL
      ∃ (numberFieldL : NumberField L),
        letI : NumberField L := numberFieldL
        ∃ (ι : L →+* ℂ) (S : Finset (FinitePlace K)) (a : FinitePlace K → Lˣ)
          (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam),
          IsUniformHeckeAvatar ι χ S a ψ := by
  obtain ⟨t, ht⟩ := hχ
  obtain ⟨L, fieldL, hdata⟩ := algebraicHeckeFinitePart.{uK, uL} K χ t ht
  let : Field L := fieldL
  obtain ⟨numberFieldL, ι, emb, φ, S, hemb, hφ, hS⟩ := hdata
  let : NumberField L := numberFieldL
  choose π hπ using fun v : FinitePlace K => ClassFieldTheory.Global.Artin.exists_uniformizer v
  obtain ⟨ψ, hψ⟩ := exists_isUniformHeckeAvatar_of_finitePart
    heckeAvatarIdeleCorrection.{uK, uL} finiteGeometricArtinLifting.{uK, uL}
    heckeAvatarInverseLimit.{uK, uL} ht hemb hφ hS π hπ
  exact ⟨L, fieldL, numberFieldL, ι, S, _, ψ, hψ⟩

/-- Compatible rank-one realizations of algebraic Hecke characters of totally
complex number fields, with one coefficient field and one exceptional set. -/
theorem algebraicHeckeLambdaAdicRealization :
    AlgebraicHeckeLambdaAdicRealizationStatement.{uK, uL} := by
  intro K _ _ _ χ hχ
  obtain ⟨L, fieldL, numberFieldL, ι, S, a, ψ, hψ⟩ :=
    exists_isUniformHeckeAvatar.{uK, uL} K χ hχ
  let : Field L := fieldL
  let : NumberField L := numberFieldL
  exact ⟨L, fieldL, numberFieldL, ι, ψ, hψ.isCompatibleLambdaAdicRealization⟩

end Langlands.GaloisRepresentation
