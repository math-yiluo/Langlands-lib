import Langlands.BaseChange.GlobalNormCharacterRestriction
import Langlands.ClassFieldTheory.Local.FiniteArtinTransport

/-! # Indexing norm characters at a unique completion -/

noncomputable section

set_option autoImplicit false

universe u v w

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality
open LocalClassField (normUnits)
open scoped FiniteExtension

/-- Transport of the norm-triviality predicate along compatible finite field equivalences. -/
theorem isNormTrivial_comp_unitsMapEquiv_iff
    {F : Type u} {E : Type v} {F' : Type w} {E' : Type*}
    [Field F] [Field E] [Field F'] [Field E']
    [Algebra F E] [Algebra F' E'] [FiniteDimensional F E] [FiniteDimensional F' E']
    (a : F ≃+* F') (b : E ≃+* E')
    (hab : (algebraMap F' E').comp a.toRingHom = b.toRingHom.comp (algebraMap F E))
    (κ : (F')ˣ →* ℂˣ) :
    IsNormTrivial E (κ.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom) ↔ IsNormTrivial E' κ := by
  change (∀ x : Eˣ, κ (Units.mapEquiv a.toMulEquiv (normUnits F E x)) = 1) ↔
    ∀ y : (E')ˣ, κ (normUnits F' E' y) = 1
  simp_rw [← LocalClassField.FiniteArtinTransport.normUnits_map a b hab]
  exact ((Units.mapEquiv b.toMulEquiv).surjective.forall
    (p := fun y => κ (normUnits F' E' y) = 1)).symm

/-- At a unique place above `p`, finite restriction, followed by transport to
the supplied local field, enumerates the actual norm characters exactly once. -/
def DistinguishedNormCharactersStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (p : FinitePlace K) (w₀ : FinitePlacesAbove L p), (∀ w, w = w₀) →
    ∀ (F : Type v) (E : Type w) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
      (a : F ≃+* p.adicCompletion K) (b : E ≃+* w₀.1.adicCompletion L),
    (algebraMap (p.adicCompletion K) (w₀.1.adicCompletion L)).comp a.toRingHom =
      b.toRingHom.comp (algebraMap F E) →
    ∀ (X : Finset (Fˣ →* ℂˣ)), (∀ κ, κ ∈ X ↔ IsNormTrivial E κ) →
    ∃ (χ : ((L ≃ₐ[K] L) →* ℂˣ) → HeckeCharacter K)
      (e : ((L ≃ₐ[K] L) →* ℂˣ) ≃ ↥X),
      Function.Injective χ ∧
      (∀ η : HeckeCharacter K, η.normComp (L := L) = 1 ↔ η ∈ Set.range χ) ∧
      Nat.card ((L ≃ₐ[K] L) →* ℂˣ) = Module.finrank K L ∧
      (∀ θ, (e θ : Fˣ →* ℂˣ) =
        ((χ θ).finiteComponent p).toMonoidHom.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom) ∧
      ∀ (v : FinitePlace K) (w : FinitePlacesAbove L v) (κ : (v.adicCompletion K)ˣ →* ℂˣ),
        (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ θ, ((χ θ).finiteComponent v).toMonoidHom = κ) ∧
        (IsNormTrivial (w.1.adicCompletion L) κ →
          Nat.card {θ // ((χ θ).finiteComponent v).toMonoidHom = κ} = Nat.card (FinitePlacesAbove L v))

set_option maxHeartbeats 700000 in
/-- Use the cardinality-one fibers of global restriction and the actual transported unit norms. -/
theorem distinguishedNormCharacters : DistinguishedNormCharactersStatement.{u, v, w} := by
  intro K L _ _ _ _ _ _ _ p w₀ hw F E _ _ _ _ a b hab X hX
  obtain ⟨χ, hχ, hnorm, hcard, hlocal⟩ := globalNormCharacterRestriction K L
  let R := fun θ => ((χ θ).finiteComponent p).toMonoidHom
  let A := Units.mapEquiv a.toMulEquiv
  let f (θ : (L ≃ₐ[K] L) →* ℂˣ) : ↥X :=
    ⟨(R θ).comp A.toMonoidHom,
      (hX _).2 ((isNormTrivial_comp_unitsMapEquiv_iff a b hab _).2
        ((hlocal p w₀ (R θ)).1.2 ⟨θ, rfl⟩))⟩
  have hwcard : Nat.card (FinitePlacesAbove L p) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun w w' => (hw w).trans (hw w').symm⟩, ⟨w₀⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro θ θ' h
      have hr : R θ = R θ' := by
        apply MonoidHom.ext
        intro y
        obtain ⟨x, rfl⟩ := A.surjective y
        exact DFunLike.congr_fun (congrArg Subtype.val h) x
      have hR := (hlocal p w₀ (R θ')).1.2 ⟨θ', rfl⟩
      let hsub : Subsingleton {i // R i = R θ'} :=
        (Nat.card_eq_one_iff_unique.mp (((hlocal p w₀ (R θ')).2 hR).trans hwcard)).1
      exact congrArg Subtype.val (hsub.elim ⟨θ, hr⟩ ⟨θ', rfl⟩)
    · intro κ
      let η := κ.1.comp A.symm.toMonoidHom
      have hη : η.comp A.toMonoidHom = κ.1 := by
        apply MonoidHom.ext
        intro x
        exact congrArg κ.1 (A.symm_apply_apply x)
      have hηnorm : IsNormTrivial (w₀.1.adicCompletion L) η :=
        (isNormTrivial_comp_unitsMapEquiv_iff a b hab _).1 (hη.symm ▸ (hX κ.1).1 κ.2)
      obtain ⟨θ, hθ⟩ := (hlocal p w₀ η).1.1 hηnorm
      exact ⟨θ, Subtype.ext ((congrArg (fun r => r.comp A.toMonoidHom) hθ).trans hη)⟩
  exact ⟨χ, Equiv.ofBijective f hbij, hχ, hnorm, hcard, (fun _ => rfl), hlocal⟩

end Langlands.BaseChange
