import Langlands.Galois.FinitePlaceResidueCharacteristic
import Langlands.Galois.AlgebraicHeckeAvatarStatement
import Langlands.Galois.AlgebraicHeckeLambdaAdicRealizationStatement
import Langlands.Global.FiniteAdeleSplit

/-! # The conductor-level construction of adic avatars of algebraic Hecke characters

The finite part of an algebraic Hecke character of a totally complex field,
together with its conductor support, gives an actual continuous character of
the absolute Galois group at every finite place of the coefficient field.
The construction takes the idele correction, the finite geometrically
normalized lifts and their congruence limit as hypotheses, in the form of the
Library statements `HeckeAvatarIdeleCorrectionStatement`,
`FiniteGeometricArtinLifting` and `HeckeAvatarInverseLimitStatement`.
-/

noncomputable section

universe uK uL

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global
open scoped NumberField Valued

/-- The residue characteristic of a finite place is nonzero, since it is prime. -/
theorem residueCharacteristic_ne_zero {K : Type uK} [Field K] [NumberField K]
    (v : FinitePlace K) : residueCharacteristic v ≠ 0 :=
  (CharP.prime_ringChar (𝓞 K ⧸ v.asIdeal)).ne_zero

section Construction

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]

/-- The exceptional set at the coefficient place `λ`: the given finite set of
places of `K` together with the finitely many places of `K` whose residue
characteristic is that of `λ`. -/
def avatarExceptionalSet (S : Finset (FinitePlace K)) (lam : FinitePlace L) :
    Finset (FinitePlace K) :=
  letI := Classical.decEq (FinitePlace K)
  S ∪ (finite_setOf_residueCharacteristic_eq K
    (residueCharacteristic_ne_zero lam)).toFinset

theorem notMem_avatarExceptionalSet_iff {S : Finset (FinitePlace K)} {lam : FinitePlace L}
    {v : FinitePlace K} :
    v ∉ avatarExceptionalSet S lam ↔
      v ∉ S ∧ residueCharacteristic v ≠ residueCharacteristic lam := by
  classical
  simp [avatarExceptionalSet]

/-- The integral avatar at one coefficient place `λ`. The integral idele-class
character `η` is the corrected finite part; away from the residue
characteristic of `λ` it is the embedded finite part on one-place ideles. Each
of its congruence reductions has a unique geometrically normalized lift
outside the exceptional set `avatarExceptionalSet S λ`, the reduction of `ψ`
is that lift, and `ψ` itself matches `η` at every geometric Frobenius lift
outside that set. -/
def IsIntegralHeckeAvatarAt (t : InfinityType K) (emb : (K →+* ℂ) → (K →+* L))
    (φ : FiniteIdeles K →* Lˣ) (S : Finset (FinitePlace K)) (lam : FinitePlace L)
    (η : IdeleClasses K →ₜ* (lam.adicCompletionIntegers L)ˣ)
    (ψ : Field.absoluteGaloisGroup K →ₜ* (lam.adicCompletionIntegers L)ˣ) : Prop :=
  (∀ x : Ideles K, completionIntegerUnitsInclusion lam (η (ideleClassMap K x)) =
    correctedIdeleValue t emb φ lam x) ∧
  (∀ v : FinitePlace K, residueCharacteristic v ≠ residueCharacteristic lam →
    ∀ a : (FiniteCompletion K v)ˣ,
      completionIntegerUnitsInclusion lam (η (finiteClassInclusion K v a)) =
        Units.map (NumberField.FinitePlace.embedding lam).toMonoidHom
          (φ (singleFiniteIdele v a))) ∧
  (∀ n : ℕ, ∃! r : Field.absoluteGaloisGroup K →ₜ* CompletionUnitQuotient lam n,
    MatchesGeometricArtinOutside (avatarExceptionalSet S lam)
      ((completionUnitReduction lam n).comp η) r) ∧
  (∀ n : ℕ, MatchesGeometricArtinOutside (avatarExceptionalSet S lam)
    ((completionUnitReduction lam n).comp η) ((completionUnitReduction lam n).comp ψ)) ∧
  MatchesGeometricArtinOutside (avatarExceptionalSet S lam) η ψ

variable [NumberField.IsTotallyComplex K]

/-- The conductor-level construction at one coefficient place: the idele
correction of a finite part with conductor support `S`, its finite
geometric lifts outside `S` and the places over the residue characteristic
of `λ`, and their congruence limit. -/
theorem exists_isIntegralHeckeAvatarAt
    (correct : HeckeAvatarIdeleCorrectionStatement.{uK, uL})
    (finiteLift : FiniteGeometricArtinLifting.{uK, uL})
    (inverseLimit : HeckeAvatarInverseLimitStatement.{uK, uL})
    {χ : HeckeCharacter K} {t : InfinityType K} {ι : L →+* ℂ}
    {emb : (K →+* ℂ) → (K →+* L)} {φ : FiniteIdeles K →* Lˣ}
    {S : Finset (FinitePlace K)}
    (ht : χ.HasPrescribedInfinityComponent (InfinityType.toCharacter t))
    (hemb : ∀ σ, ι.comp (emb σ) = σ) (hφ : IsHeckeFinitePart χ ι φ)
    (hS : ∀ v, v ∉ S → χ.IsUnramifiedAt v) (lam : FinitePlace L) :
    ∃ (η : IdeleClasses K →ₜ* (lam.adicCompletionIntegers L)ˣ)
      (ψ : Field.absoluteGaloisGroup K →ₜ* (lam.adicCompletionIntegers L)ˣ),
      IsIntegralHeckeAvatarAt t emb φ S lam η ψ := by
  obtain ⟨η, hcorr, haway⟩ := correct K L χ t ι emb φ ht hemb hφ lam
  let T := avatarExceptionalSet S lam
  have hlocal (v : FinitePlace K) (hv : v ∉ T) : IsTrivialOnLocalUnits η v := by
    obtain ⟨hvS, hchar⟩ := notMem_avatarExceptionalSet_iff.mp hv
    intro u hu
    have hφu : φ (singleFiniteIdele v u) = 1 := by
      apply Units.map_injective (f := ι.toMonoidHom) ι.injective
      rw [hφ.2, map_one]
      exact hS v hvS u hu
    have hinclusion : Function.Injective (completionIntegerUnitsInclusion lam) :=
      Units.map_injective Subtype.val_injective
    apply hinclusion
    rw [haway v hchar u, hφu, map_one, map_one]
  have hlifts (n : ℕ) :
      ∃! r : Field.absoluteGaloisGroup K →ₜ* CompletionUnitQuotient lam n,
        MatchesGeometricArtinOutside T ((completionUnitReduction lam n).comp η) r := by
    refine finiteLift K (CompletionUnitQuotient lam n)
      ((completionUnitReduction lam n).comp η) T ?_
    intro v hv u hu
    change completionUnitReduction lam n (η (finiteClassInclusion K v u)) = 1
    rw [hlocal v hv u hu, map_one]
  obtain ⟨r, ψ, hr, -, hred, hψ⟩ := inverseLimit K L lam T η hlifts
  refine ⟨η, ψ, hcorr, haway, hlifts, fun n => ?_, hψ⟩
  rw [hred n]
  exact hr n

/-- The `λ`-adic character of the integral avatar: the integral character
followed by the inclusion of completed integer units into `L_λ^×`. -/
def integralAvatarCharacter (lam : FinitePlace L)
    (ψ : Field.absoluteGaloisGroup K →ₜ* (lam.adicCompletionIntegers L)ˣ) :
    LambdaAdicCharacter K L lam :=
  (completionIntegerUnitsInclusion lam).comp ψ

omit [NumberField.IsTotallyComplex K] in
/-- At a place outside the conductor support of residue characteristic
different from that of `λ`, the `λ`-adic character of an integral avatar is
unramified and sends every geometric Frobenius lift to the embedded finite
part at the uniformizer. -/
theorem IsIntegralHeckeAvatarAt.frobenius {t : InfinityType K}
    {emb : (K →+* ℂ) → (K →+* L)} {φ : FiniteIdeles K →* Lˣ}
    {S : Finset (FinitePlace K)} {lam : FinitePlace L}
    {η : IdeleClasses K →ₜ* (lam.adicCompletionIntegers L)ˣ}
    {ψ : Field.absoluteGaloisGroup K →ₜ* (lam.adicCompletionIntegers L)ˣ}
    (h : IsIntegralHeckeAvatarAt t emb φ S lam η ψ) {v : FinitePlace K} (hv : v ∉ S)
    (hchar : residueCharacteristic v ≠ residueCharacteristic lam) :
    (integralAvatarCharacter lam ψ).IsUnramifiedAt v ∧
      ∀ π : (FiniteCompletion K v)ˣ,
        Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) →
        ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
          ((integralAvatarCharacter lam ψ).atFinitePlace v g : FiniteCompletion L lam) =
            NumberField.FinitePlace.embedding lam (φ (singleFiniteIdele v π) : L) := by
  obtain ⟨-, haway, -, -, hψ⟩ := h
  obtain ⟨hinertia, hfrob⟩ := hψ v (notMem_avatarExceptionalSet_iff.mpr ⟨hv, hchar⟩)
  refine ⟨fun i => ?_, fun π hπ g hg => ?_⟩
  · change completionIntegerUnitsInclusion lam (ψ (localToGlobalGalois v i.val)) = 1
    rw [hinertia i, map_one]
  · change (completionIntegerUnitsInclusion lam (ψ (localToGlobalGalois v g)) :
      FiniteCompletion L lam) = NumberField.FinitePlace.embedding lam (φ (singleFiniteIdele v π) : L)
    rw [hfrob π hπ g hg, haway v hchar π]
    rfl

/-- The uniform family from a finite part with exact conductor support `S`
and a choice of uniformizers: one coefficient field, the conductor support
`S` for every coefficient place, and the values of the finite part at the
one-place ideles of the uniformizers. -/
theorem exists_isUniformHeckeAvatar_of_finitePart
    (correct : HeckeAvatarIdeleCorrectionStatement.{uK, uL})
    (finiteLift : FiniteGeometricArtinLifting.{uK, uL})
    (inverseLimit : HeckeAvatarInverseLimitStatement.{uK, uL})
    {χ : HeckeCharacter K} {t : InfinityType K} {ι : L →+* ℂ}
    {emb : (K →+* ℂ) → (K →+* L)} {φ : FiniteIdeles K →* Lˣ}
    {S : Finset (FinitePlace K)}
    (ht : χ.HasPrescribedInfinityComponent (InfinityType.toCharacter t))
    (hemb : ∀ σ, ι.comp (emb σ) = σ) (hφ : IsHeckeFinitePart χ ι φ)
    (hS : ∀ v, v ∉ S ↔ χ.IsUnramifiedAt v)
    (π : ∀ v : FinitePlace K, (FiniteCompletion K v)ˣ)
    (hπ : ∀ v, Valued.v (π v : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)) :
    ∃ ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam,
      IsUniformHeckeAvatar ι χ S (fun v => φ (singleFiniteIdele v (π v))) ψ := by
  have hint (lam : FinitePlace L) := exists_isIntegralHeckeAvatarAt correct finiteLift
    inverseLimit ht hemb hφ (fun v hv => (hS v).mp hv) lam
  choose η ψ hψ using hint
  refine ⟨fun lam => integralAvatarCharacter lam (ψ lam), hS, fun v hv => ⟨?_, ?_⟩⟩
  · refine ⟨π v, hπ v, ?_⟩
    have := congrArg Units.val (hφ.2 (singleFiniteIdele v (π v)))
    exact this.symm
  · intro lam hchar
    obtain ⟨hunr, hfrob⟩ := (hψ lam).frobenius hv hchar
    exact ⟨hunr, hfrob (π v) (hπ v)⟩

end Construction

variable {K : Type uK} [Field K] [NumberField K]
variable {L : Type uL} [Field L] [NumberField L]

/-- A uniform family is a compatible realization with the same exceptional set. -/
theorem IsUniformHeckeAvatar.isCompatibleLambdaAdicRealization {ι : L →+* ℂ}
    {χ : HeckeCharacter K} {S : Finset (FinitePlace K)} {a : FinitePlace K → Lˣ}
    {ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter K L lam}
    (h : IsUniformHeckeAvatar ι χ S a ψ) : IsCompatibleLambdaAdicRealization ι χ ψ :=
  ⟨S, fun v hv => ⟨(h.1 v).mp hv, a v, (h.2 v hv).1, (h.2 v hv).2⟩⟩

end Langlands.GaloisRepresentation
