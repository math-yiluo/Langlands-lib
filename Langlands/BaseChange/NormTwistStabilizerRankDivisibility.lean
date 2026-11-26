import Langlands.BaseChange.NormTrivialCharacterGroup
import Langlands.Representation.Smooth.Schur.Proof

/-! # Rank divisibility of the norm-twist stabilizer -/

noncomputable section

namespace Langlands.BaseChange

open CharZeroLocalField GeneralLinear LocalClassField LocalClassField.UniverseZero

universe u v uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
  {E : Type v} [Field E] [Algebra F E]

private theorem isCyclic_normQuotient [FiniteDimensional F E]
    {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l) :
    IsCyclic (NormQuotient F E) := by
  let : IsGalois F E := hσ.isGalois
  let : IsAbelianGalois F E := hσ.isAbelianGalois
  let : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_orderOf_eq_card σ (by
    rw [IsGalois.card_aut_eq_finrank, hσ.2.1, hσ.2.2.2.1])
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let K := padicField F
  let L := PadicField.ofField (p := p) E
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : FiniteDimensional K.Carrier L.Carrier := (inferInstance : FiniteDimensional F E)
  let : IsAbelianGalois K.Carrier L.Carrier := (inferInstance : IsAbelianGalois F E)
  let K₀ := universeZeroModel K
  let L₀ := universeZeroModel L
  let := universeZeroAlgebra K L
  have := universeZeroAlgebra_finiteDimensional K L
  have := universeZeroAlgebra_isAbelianGalois K L
  let : IsCyclic Gal(L.Carrier/K.Carrier) := (inferInstance : IsCyclic (E ≃ₐ[F] E))
  let galoisEquiv := universeZeroGaloisEquiv K L
  let : IsCyclic Gal(L₀.Carrier/K₀.Carrier) :=
    isCyclic_of_injective galoisEquiv.toMonoidHom galoisEquiv.injective
  let ab := Abelianization.of (G := Gal(L₀.Carrier/K₀.Carrier))
  have hab : Function.Surjective ab := QuotientGroup.mk_surjective
  let normEquiv := ClassFieldTheory.Local.finiteNormAbelianizationEquiv K₀ L₀.Carrier
  let quotientEquiv : NormQuotient K₀.Carrier L₀.Carrier ≃* NormQuotient K.Carrier L.Carrier :=
    QuotientGroup.congr _ _ (Units.mapEquiv (universeZeroEquiv K).toRingEquiv.toMulEquiv)
      (universeZeroNormRange_map K L)
  exact isCyclic_of_surjective
    (quotientEquiv.toMonoidHom.comp (normEquiv.toMonoidHom.comp ab))
    (quotientEquiv.surjective.comp (normEquiv.surjective.comp hab))

omit [CharZero F] in
private theorem pow_eq_one_of_mem_stabilizer {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) (hπa : IsAdmissible π)
    (hπi : π.IsIrreducible) (κ : normTwistStabilizer E π) (a : Fˣ) :
    κ.1 a ^ n = 1 := by
  obtain ⟨χ, ⟨-, hχ⟩, -⟩ := admissibleSchur_centralCharacter π hπa hπi
  obtain ⟨-, ⟨e⟩⟩ := (mem_normTwistStabilizer E π κ.1).mp κ.2
  let : π.IsIrreducible := hπi
  let : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F)) π.asModule
  let z := scalarToCenter (n := n) a
  obtain ⟨w, hw⟩ := exists_ne (0 : V)
  have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans (map_zero e).symm))
  have he := LinearMap.congr_fun (e.isIntertwining' (z : GeneralLinear n F)) w
  change e (π (z : GeneralLinear n F) w) =
    (κ.1 (determinant (z : GeneralLinear n F)) : ℂ) • π (z : GeneralLinear n F) (e w) at he
  have hdet : determinant (z : GeneralLinear n F) = a ^ n := by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin n) a) = a ^ n
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  rw [hdet, map_pow, hχ, hχ, map_smul] at he
  have hχw : (χ z : ℂ) • e w ≠ 0 := smul_ne_zero (χ z).ne_zero hew
  exact Units.ext ((smul_left_injective ℂ hχw) (he.symm.trans (one_smul ℂ _).symm))

/-- The order of the norm-twist stabilizer of an irreducible admissible representation
of `GL_n(F)` divides both the cyclic extension degree and the matrix rank. -/
def NormTwistStabilizerRankDivisibilityStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [Algebra F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    IsCyclicAlgebra σ l →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V),
      IsAdmissible π → π.IsIrreducible → Nat.card (normTwistStabilizer E π) ∣ Nat.gcd l n

/-- Evaluation at a representative of a norm-quotient generator embeds the stabilizer
in the group of `n`-th roots of unity. -/
theorem normTwistStabilizer_card_dvd_gcd : NormTwistStabilizerRankDivisibilityStatement := by
  intro F _ _ _ _ _ E _ _ σ l n hσ V _ _ π hπa hπi
  refine Nat.dvd_gcd (normTwistStabilizer_card_dvd hσ π) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact dvd_zero _
  let : NeZero n := ⟨hn.ne'⟩
  let : FiniteDimensional F E := hσ.1
  let : IsCyclic (NormQuotient F E) := isCyclic_normQuotient hσ
  obtain ⟨q, hq⟩ := exists_zpow_surjective (NormQuotient F E)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (normSubgroup F E) q
  let H := normTwistStabilizer E π
  let ev := (MonoidHom.eval a).comp H.subtype
  let evRoots := ev.codRestrict (rootsOfUnity n ℂ)
    (fun κ => pow_eq_one_of_mem_stabilizer π hπa hπi κ a)
  have hinj : Function.Injective evRoots := by
    intro κ η h
    let χκ := normTrivialCharacterEquiv (F := F) (E := E) ⟨κ.1, κ.2.1⟩
    let χη := normTrivialCharacterEquiv (F := F) (E := E) ⟨η.1, η.2.1⟩
    have hgen : χκ (QuotientGroup.mk' (normSubgroup F E) a) =
        χη (QuotientGroup.mk' (normSubgroup F E) a) := congrArg Subtype.val h
    have hχ : χκ = χη := by
      apply MonoidHom.ext
      intro y
      obtain ⟨j, rfl⟩ := hq y
      rw [map_zpow, map_zpow, hgen]
    exact Subtype.ext (congrArg (fun χ : normTrivialCharacterGroup F E => χ.1)
      (normTrivialCharacterEquiv.injective hχ))
  simpa only [Complex.card_rootsOfUnity n] using Subgroup.card_dvd_of_injective evRoots hinj

end Langlands.BaseChange
