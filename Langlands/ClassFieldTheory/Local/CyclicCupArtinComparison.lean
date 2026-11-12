import Langlands.ClassFieldTheory.Local.CyclicCupEvaluation
import Langlands.ClassFieldTheory.Local.FiniteArtinSymbol

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

set_option backward.isDefEq.respectTransparency false

open CyclicClassAlgebra

section General

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] {n : ℕ} [NeZero n]

/-- A character evaluated after geometric inverse cup on the actual norm quotient. -/
def geometricCupCharacter (c : relativeCohomology K L 2)
    (h : Function.Bijective (relativeTateCup K L (-2) c))
    (ψ : Gal(L/K) →* Multiplicative (ZMod n)) :
    Langlands.LocalClassField.NormQuotient K L →* Multiplicative (ZMod n) :=
  (Abelianization.lift ψ).comp (geometricReciprocityOfCup K L c h).toMonoidHom

/-- The signed cup evaluation determines a carry class from its norm value. -/
theorem cyclicClass_eq_neg_nsmul_of_cup
    (χ : Gal(L/K) ≃* Multiplicative (ZMod n))
    (c : relativeCohomology K L 2) (a : Kˣ) (g : Gal(L/K))
    (hg : abelianizationCupToNormQuotient K L c
      (Additive.ofMul (Abelianization.of g)) =
        Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L a)) :
    cyclicClass K L χ.toMonoidHom a = -((χ g).toAdd.val • c) := by
  obtain ⟨b, hb⟩ := exists_cyclicClass_eq χ c
  let e := cyclicH2NormEquiv K L (cyclicCoordinateGenerator χ)
    (cyclicCoordinateGenerator_generates χ)
  have he (x : Kˣ) : e (cyclicClass K L χ.toMonoidHom x) =
      Additive.ofMul (Langlands.LocalClassField.normQuotientProjection K L x) :=
    cyclicClassNormNormalization K L n χ (cyclicCoordinateGenerator χ)
      (cyclicCoordinateGenerator_generates χ) (χ.apply_symm_apply _) x
  apply e.injective
  rw [map_neg, map_nsmul, ← hb, he, he]
  rw [← hb, abelianizationCupToNormQuotient_cyclicClass_signed] at hg
  exact hg.symm

end General

theorem denominatorEquiv_eq_val_nsmul {n : ℕ} [NeZero n] (z : ZMod n) :
    (denominatorEquiv n (NeZero.pos n) z : RationalModIntegers) =
      z.val • reciprocalClass n := by
  have hz : z = z.val • (1 : ZMod n) := by
    simp [nsmul_eq_mul]
  conv_lhs => rw [hz]
  rw [map_nsmul, AddSubgroup.coe_nsmul, denominatorEquiv_one]

theorem cyclicCoordinateGenerator_pow_val {G : Type*} [Group G]
    {n : ℕ} [NeZero n] (χ : G ≃* Multiplicative (ZMod n)) (g : G) :
    cyclicCoordinateGenerator χ ^ (χ g).toAdd.val = g := by
  apply χ.injective
  rw [map_pow]
  change χ (χ.symm (Multiplicative.ofAdd 1)) ^ _ = _
  rw [χ.apply_symm_apply, ← ofAdd_nsmul]
  apply Multiplicative.toAdd.injective
  simp [nsmul_eq_mul]

/-- Every character of a cyclic coordinate group is a power of that coordinate. -/
theorem character_eq_pow_cyclicCoordinate {G : Type*} [Group G]
    {n : ℕ} [NeZero n] (χ : G ≃* Multiplicative (ZMod n))
    (ψ : G →* Multiplicative (ZMod n)) :
    ψ = χ.toMonoidHom ^ (ψ (cyclicCoordinateGenerator χ)).toAdd.val := by
  ext g
  rw [MonoidHom.pow_apply]
  calc
    ψ g = ψ (cyclicCoordinateGenerator χ) ^ (χ g).toAdd.val := by
      rw [← map_pow, cyclicCoordinateGenerator_pow_val]
    _ = χ g ^ (ψ (cyclicCoordinateGenerator χ)).toAdd.val := by
      apply Multiplicative.toAdd.injective
      simp only [toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val]
      exact mul_comm _ _

section LocalField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (D : Type u) [Field D] [Algebra F.Carrier D]
  [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]

open scoped FiniteArtinSymbol

theorem symbolValue_cyclicCoordinate_of_cup
    (χ : Gal(D/F.Carrier) ≃* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (a : F.Carrierˣ) (g : Gal(D/F.Carrier))
    (hg : abelianizationCupToNormQuotient F.Carrier D c
      (Additive.ofMul (Abelianization.of g)) =
        Additive.ofMul (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)) :
    FiniteArtinSymbol.symbolValue χ.toMonoidHom a = -(χ g).toAdd := by
  rw [FiniteArtinSymbol.symbolValue_eq_iff, map_neg, AddSubgroup.coe_neg,
    denominatorEquiv_eq_val_nsmul,
    cyclicClass_eq_neg_nsmul_of_cup F.Carrier D χ c a g hg,
    map_neg, map_nsmul]
  rw [hc]

/-- Positive fundamental inverse cup has the negative cyclic symbol. -/
theorem arithmeticReciprocityOfCup_character_cyclicCoordinate
    (χ : Gal(D/F.Carrier) ≃* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (a : F.Carrierˣ) :
    Abelianization.lift χ.toMonoidHom
        (arithmeticReciprocityOfCup F.Carrier D c h
          (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)) =
      Multiplicative.ofAdd (-FiniteArtinSymbol.symbolValue χ.toMonoidHom a) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (commutator Gal(D/F.Carrier))
    (arithmeticReciprocityOfCup F.Carrier D c h
      (Langlands.LocalClassField.normQuotientProjection F.Carrier D a))
  change Abelianization.of g = _ at hg
  have hcup := cup_arithmeticReciprocityOfCup F.Carrier D c h
    (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)
  rw [← hg] at hcup
  rw [symbolValue_cyclicCoordinate_of_cup F D χ c hc a g hcup, neg_neg,
    ← hg, Abelianization.lift_apply_of]
  rfl

/-- Geometric inverse cup has the positive cyclic symbol. -/
theorem geometricReciprocityOfCup_character_cyclicCoordinate
    (χ : Gal(D/F.Carrier) ≃* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (a : F.Carrierˣ) :
    Abelianization.lift χ.toMonoidHom
        (geometricReciprocityOfCup F.Carrier D c h
          (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)) =
      Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue χ.toMonoidHom a) := by
  rw [geometricReciprocityOfCup_eq_inv, map_inv,
    arithmeticReciprocityOfCup_character_cyclicCoordinate F D χ c hc h a,
    ← ofAdd_neg, neg_neg]

theorem symbolValue_pow_character {n : ℕ} [NeZero n]
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod n)) (a : F.Carrierˣ) (k : ℕ) :
    FiniteArtinSymbol.symbolValue (ψ ^ k) a =
      k • FiniteArtinSymbol.symbolValue ψ a := by
  rw [FiniteArtinSymbol.symbolValue_eq_iff, map_nsmul, AddSubgroup.coe_nsmul,
    FiniteArtinSymbol.denominatorEquiv_symbolValue, cyclicClass_pow_character, map_nsmul]

/-- For any character of a cyclic Galois group, geometric inverse cup gives
the positive carry symbol. -/
theorem geometricReciprocityOfCup_character_of_cyclicCoordinate
    (χ : Gal(D/F.Carrier) ≃* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (a : F.Carrierˣ) :
    Abelianization.lift ψ
        (geometricReciprocityOfCup F.Carrier D c h
          (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)) =
      Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue ψ a) := by
  rw [character_eq_pow_cyclicCoordinate χ ψ, symbolValue_pow_character]
  have hlift (k : ℕ) : Abelianization.lift (χ.toMonoidHom ^ k) =
      (Abelianization.lift χ.toMonoidHom) ^ k := by
    apply Abelianization.hom_ext
    ext g
    simp
  rw [hlift, MonoidHom.pow_apply,
    geometricReciprocityOfCup_character_cyclicCoordinate F D χ c hc h a,
    ofAdd_nsmul]

/-- The geometric finite Artin character comparison holds for cyclic
finite Galois extensions, including degree one. -/
theorem geometricReciprocityOfCup_character_of_isCyclic [IsCyclic Gal(D/F.Carrier)]
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (a : F.Carrierˣ) :
    Abelianization.lift ψ
        (geometricReciprocityOfCup F.Carrier D c h
          (Langlands.LocalClassField.normQuotientProjection F.Carrier D a)) =
      Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue ψ a) := by
  let χ : Gal(D/F.Carrier) ≃* Multiplicative (ZMod (Module.finrank F.Carrier D)) := by
    rw [← IsGalois.card_aut_eq_finrank F.Carrier D]
    exact (zmodCyclicMulEquiv (inferInstance : IsCyclic Gal(D/F.Carrier))).symm
  exact geometricReciprocityOfCup_character_of_cyclicCoordinate F D χ c hc h ψ a

theorem geometricCupCharacter_projection_of_isCyclic [IsCyclic Gal(D/F.Carrier)]
    (c : relativeCohomology F.Carrier D 2)
    (hc : IsFundamentalClass F.Carrier D (FiniteArtinSymbol.relInv F D) c)
    (h : Function.Bijective (relativeTateCup F.Carrier D (-2) c))
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (a : F.Carrierˣ) :
    geometricCupCharacter F.Carrier D c h ψ
        (Langlands.LocalClassField.normQuotientProjection F.Carrier D a) =
      Multiplicative.ofAdd (FiniteArtinSymbol.symbolValue ψ a) :=
  geometricReciprocityOfCup_character_of_isCyclic F D c hc h ψ a

end LocalField

end Langlands.ClassFieldTheory.Local
