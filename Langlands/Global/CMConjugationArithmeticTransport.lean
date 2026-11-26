import Langlands.Global.AdelicGLTransport
import Langlands.Global.ArchimedeanCompactTransport
import Langlands.Global.ArchimedeanLieTransport

/-!
# Arithmetic transport commutes with the CM involutions

For CM fields `K`, `L` and a ring isomorphism `e : K ≃+* L`, the CM involutions satisfy
`e ∘ c_K = c_L ∘ e`: the CM involution of a CM field induces complex conjugation under
every complex embedding, and `ψ ∘ e` is a complex embedding of `K` for every complex
embedding `ψ` of `L`. Hence the arithmetic transports along `e` of the finite adelic
matrix group, of the standard compact subgroup at infinity, of the mixed archimedean
coordinates and of the real matrix Lie algebra commute with the entrywise CM
conjugations `finiteConj`, `compactConj`, `mixedConj` and `lieConj`.
-/

noncomputable section

universe uK uL uE

set_option autoImplicit false

namespace Langlands.Global.CMConjugation

open NumberField AdelicFunctoriality

section Single

variable (E : Type uE) [Field E] [NumberField E] [IsCMField E]

/-- Arithmetic transport of the mixed coordinates along the CM involution is entrywise
complex conjugation. -/
theorem mixedEquiv_fieldConj (x : mixedEmbedding.mixedSpace E) :
    ArchimedeanGLTransport.mixedEquiv (fieldConj E) x = mixedConj E x := by
  have h := mixedSpace_infiniteComplexConj E ((InfiniteAdeleRing.ringEquiv_mixedSpace E).symm x)
  rw [RingEquiv.apply_symm_apply] at h
  exact h

end Single

variable {K : Type uK} {L : Type uL} [Field K] [NumberField K] [IsCMField K]
  [Field L] [NumberField L] [IsCMField L]

/-- A ring isomorphism of CM fields commutes with their CM involutions. -/
theorem ringEquiv_complexConj (e : K ≃+* L) (x : K) :
    e (IsCMField.complexConj K x) = IsCMField.complexConj L (e x) := by
  obtain ⟨ψ⟩ : Nonempty (L →+* ℂ) := inferInstance
  apply ψ.injective
  have h := IsCMField.complexEmbedding_complexConj K (ψ.comp e.toRingHom) x
  rw [IsCMField.complexEmbedding_complexConj]
  exact h

/-- The ring-isomorphism form of `ringEquiv_complexConj`. -/
theorem fieldConj_trans (e : K ≃+* L) : (fieldConj K).trans e = e.trans (fieldConj L) := by
  apply RingEquiv.ext
  intro x
  exact ringEquiv_complexConj e x

variable (n : ℕ)

/-- Arithmetic transport of the finite adelic matrix group commutes with the CM
conjugations. -/
theorem finiteEquiv_finiteConj (e : K ≃+* L) (d : FiniteAdelicGL K n) :
    AdelicGLTransport.finiteEquiv n e (finiteConj K n d) =
      finiteConj L n (AdelicGLTransport.finiteEquiv n e d) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁ := RingEquiv.congr_fun (finiteAdeleEquiv_trans (fieldConj K) e) (d i j)
  have h₂ := RingEquiv.congr_fun (finiteAdeleEquiv_trans e (fieldConj L)) (d i j)
  rw [fieldConj_trans] at h₁
  exact h₁.symm.trans h₂

/-- Arithmetic transport of the infinite adelic matrix group commutes with the CM
conjugations. -/
theorem infiniteEquiv_infiniteConj (e : K ≃+* L) (g : InfiniteAdelicGL K n) :
    AdelicGLTransport.infiniteEquiv n e (infiniteConj K n g) =
      infiniteConj L n (AdelicGLTransport.infiniteEquiv n e g) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁ := RingEquiv.congr_fun (infiniteAdeleEquiv_trans (fieldConj K) e) (g i j)
  have h₂ := RingEquiv.congr_fun (infiniteAdeleEquiv_trans e (fieldConj L)) (g i j)
  rw [fieldConj_trans] at h₁
  exact h₁.symm.trans h₂

/-- Arithmetic transport of the standard compact subgroup at infinity commutes with the
CM conjugations. -/
theorem compactEquiv_compactConj (e : K ≃+* L) (k : standardInfiniteCompact K n) :
    ArchimedeanCompactTransport.compactEquiv n e (compactConj K n k) =
      compactConj L n (ArchimedeanCompactTransport.compactEquiv n e k) :=
  Subtype.ext (infiniteEquiv_infiniteConj n e k)

/-- Arithmetic transport of the mixed coordinates commutes with their entrywise complex
conjugations. -/
theorem mixedEquiv_mixedConj (e : K ≃+* L) (x : mixedEmbedding.mixedSpace K) :
    ArchimedeanGLTransport.mixedEquiv e (mixedConj K x) =
      mixedConj L (ArchimedeanGLTransport.mixedEquiv e x) := by
  rw [← mixedEquiv_fieldConj K, ← mixedEquiv_fieldConj L,
    ← ArchimedeanLieTransport.mixedEquiv_trans, ← ArchimedeanLieTransport.mixedEquiv_trans,
    fieldConj_trans]

/-- Arithmetic transport of the real matrix Lie algebra commutes with the CM
conjugations. -/
theorem realLieEquiv_lieConj (e : K ≃+* L) (X : ArchimedeanGL.RealLieAlgebra K n) :
    ArchimedeanLieTransport.realLieEquiv n e (lieConj K n X) =
      lieConj L n (ArchimedeanLieTransport.realLieEquiv n e X) := by
  apply (ArchimedeanGL.realLieAlgebraToMatrix L n).injective
  apply Matrix.ext
  intro i j
  rw [ArchimedeanLieTransport.realLieEquiv_entry, lieConj_apply, lieConj_apply,
    ArchimedeanLieTransport.realLieEquiv_entry]
  exact mixedEquiv_mixedConj e _

end Langlands.Global.CMConjugation
