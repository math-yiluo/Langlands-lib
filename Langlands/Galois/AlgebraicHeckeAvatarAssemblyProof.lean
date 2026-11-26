import Langlands.Galois.FinitePlaceResidueCharacteristic
import Langlands.Galois.AlgebraicHeckeAvatarStatement
import Langlands.ClassFieldTheory.Global.Artin.ArtinUniqueness
import Langlands.Global.FiniteAdeleSplit

/-! # Assembly of the uniform algebraic Hecke avatar -/

noncomputable section

universe uK uL

namespace Langlands.GaloisRepresentation

open Langlands.Global Langlands.ClassFieldTheory.Global.Artin
open scoped NumberField

/-- The common finite part, the local correction, the finite geometric lifts and
their congruence limit give the uniform adic avatar. -/
theorem algebraicHeckeAvatarAssembly : AlgebraicHeckeAvatarAssemblyStatement.{uK, uL} := by
  classical
  intro finitePart correct finiteLift inverseLimit K _ _ _ χ hχ
  obtain ⟨t, ht⟩ := hχ
  obtain ⟨L, hL, hdata⟩ := finitePart K χ t ht
  let : Field L := hL
  obtain ⟨hnum, ι, emb, φ, S, hemb, hφ, hS⟩ := hdata
  let : NumberField L := hnum
  choose π hπ using (fun v : FinitePlace K => exists_uniformizer v)
  let a (v : FinitePlace K) : Lˣ := φ (singleFiniteIdele v (π v))
  have finitePartAt (v : FinitePlace K) (u : (FiniteCompletion K v)ˣ) :
      Units.map ι.toMonoidHom (φ (singleFiniteIdele v u)) = χ.finiteComponent v u := by
    rw [hφ.2]
    rfl
  have localAvatar (lam : FinitePlace L) : ∃ ψ : LambdaAdicCharacter K L lam,
      ∀ v ∉ S, residueCharacteristic v ≠ residueCharacteristic lam →
        ψ.IsUnramifiedAt v ∧
          ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
            (ψ.atFinitePlace v g : FiniteCompletion L lam) =
              NumberField.FinitePlace.embedding lam (a v : L) := by
    obtain ⟨η, _, haway⟩ := correct K L χ t ι emb φ ht hemb hφ lam
    have hp : (residueCharacteristic lam).Prime := CharP.prime_ringChar (𝓞 L ⧸ lam.asIdeal)
    let T := S ∪ (finite_setOf_residueCharacteristic_eq K hp.ne_zero).toFinset
    have hgood (v : FinitePlace K) :
        v ∉ T ↔ v ∉ S ∧ residueCharacteristic v ≠ residueCharacteristic lam := by
      simp [T]
    have hlocal (v : FinitePlace K) (hv : v ∉ T) : IsTrivialOnLocalUnits η v := by
      obtain ⟨hvS, hchar⟩ := (hgood v).mp hv
      intro u hu
      have hφu : φ (singleFiniteIdele v u) = 1 := by
        apply Units.map_injective (f := ι.toMonoidHom) ι.injective
        rw [finitePartAt, map_one]
        exact (hS v).mp hvS u hu
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
    obtain ⟨_, ψ, _, _, _, hψ⟩ := inverseLimit K L lam T η hlifts
    refine ⟨(completionIntegerUnitsInclusion lam).comp ψ, ?_⟩
    intro v hv hchar
    obtain ⟨hinertia, hfrob⟩ := hψ v ((hgood v).mpr ⟨hv, hchar⟩)
    refine ⟨?_, ?_⟩
    · intro i
      change completionIntegerUnitsInclusion lam (ψ (localToGlobalGalois v i.val)) = 1
      rw [hinertia i, map_one]
    · intro g hg
      change (completionIntegerUnitsInclusion lam (ψ (localToGlobalGalois v g)) :
        FiniteCompletion L lam) = NumberField.FinitePlace.embedding lam (a v : L)
      rw [hfrob (π v) (hπ v) g hg, haway v hchar (π v)]
      rfl
  choose ψ hψ using localAvatar
  refine ⟨L, hL, hnum, ι, S, a, ψ, hS, fun v hv => ?_⟩
  exact ⟨⟨π v, hπ v, (congrArg Units.val (finitePartAt v (π v))).symm⟩,
    fun lam => hψ lam v hv⟩

end Langlands.GaloisRepresentation
