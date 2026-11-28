import Langlands.ClassFieldTheory.Local.KummerRadicalFields

/-!
# Kummer characters with values in the base field

For `β ^ n = b` with `b` a base-field unit, the Kummer character is given by
`σ β / β`. The existence of a primitive root of order `n` makes the quotient
an image of a unique root of unity in the base. This is the root action in
Milnor, *Introduction to Algebraic K-Theory* (1971), Remark 15.10, p. 152
(`milnor-1971-introduction-algebraic-k-theory`). It also applies to reducible
radical polynomials.
-/

noncomputable section

namespace Langlands.KTheory

open Polynomial Langlands.ClassFieldTheory.Local.KummerNorm

universe u v w

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
  {n : ℕ} [NeZero n] {b : Fˣ} {β γ : E}

private theorem root_ne_zero (hβ : β ^ n = algebraMap F E (b : F)) : β ≠ 0 := by
  intro h
  rw [h, zero_pow (NeZero.ne n)] at hβ
  exact ((_root_.map_ne_zero (algebraMap F E)).2 b.ne_zero) hβ.symm

omit [NeZero n] in
private theorem rootsOfUnity_algebraMap_injective :
    Function.Injective (fun ξ : rootsOfUnity n F => algebraMap F E (ξ : Fˣ)) :=
  fun _ _ h => Subtype.ext (Units.ext ((algebraMap F E).injective h))

private def rootRatio (hζ : (primitiveRoots n F).Nonempty)
    (hβ : β ^ n = algebraMap F E (b : F)) (hγ : γ ^ n = algebraMap F E (b : F)) :
    rootsOfUnity n F :=
  (rootsOfUnityEquivOfPrimitiveRoots (algebraMap F E).injective hζ).symm
    (rootsOfUnity.mkOfPowEq (γ / β) (by
      rw [div_pow, hγ, ← hβ, div_self (pow_ne_zero n (root_ne_zero hβ))]))

private theorem algebraMap_rootRatio (hζ : (primitiveRoots n F).Nonempty)
    (hβ : β ^ n = algebraMap F E (b : F)) (hγ : γ ^ n = algebraMap F E (b : F)) :
    algebraMap F E (rootRatio hζ hβ hγ : Fˣ) = γ / β := by
  rw [rootRatio, rootsOfUnityEquivOfPrimitiveRoots_symm_apply, rootsOfUnity.coe_mkOfPowEq]

private theorem algebraMap_rootRatio_mul (hζ : (primitiveRoots n F).Nonempty)
    (hβ : β ^ n = algebraMap F E (b : F)) (hγ : γ ^ n = algebraMap F E (b : F)) :
    algebraMap F E (rootRatio hζ hβ hγ : Fˣ) * β = γ := by
  rw [algebraMap_rootRatio, div_mul_cancel₀ _ (root_ne_zero hβ)]

omit [NeZero n] in
private theorem aut_pow_eq (hβ : β ^ n = algebraMap F E (b : F)) (σ : Gal(E/F)) :
    (σ β) ^ n = algebraMap F E (b : F) := by
  rw [← map_pow, hβ, AlgEquiv.commutes]

/-- The Kummer character of `b` on the automorphisms of an extension containing
an `n`-th root `β` of `b`. Its values lie in `rootsOfUnity n F`. -/
def kummerCharacter (hζ : (primitiveRoots n F).Nonempty)
    (hβ : β ^ n = algebraMap F E (b : F)) : Gal(E/F) →* rootsOfUnity n F := by
  let value (σ : Gal(E/F)) := rootRatio hζ hβ (aut_pow_eq hβ σ)
  have hvalue (σ : Gal(E/F)) : algebraMap F E (value σ : Fˣ) * β = σ β :=
    algebraMap_rootRatio_mul hζ hβ (aut_pow_eq hβ σ)
  refine { toFun := value, map_one' := ?_, map_mul' := ?_ }
  · apply rootsOfUnity_algebraMap_injective (E := E)
    apply mul_right_cancel₀ (root_ne_zero hβ)
    simpa only [Subgroup.coe_one, Units.val_one, map_one, one_mul, AlgEquiv.one_apply] using
      hvalue 1
  · intro σ τ
    apply rootsOfUnity_algebraMap_injective (E := E)
    apply mul_right_cancel₀ (root_ne_zero hβ)
    calc
      algebraMap F E (value (σ * τ) : Fˣ) * β = σ (τ β) := hvalue _
      _ = algebraMap F E (value τ : Fˣ) * σ β := by
        rw [← hvalue τ, map_mul, AlgEquiv.commutes]
      _ = algebraMap F E (↑(value σ * value τ) : Fˣ) * β := by
        rw [← hvalue σ, Subgroup.coe_mul, Units.val_mul, map_mul]
        ac_rfl

/-- The image of the Kummer character is the quotient of the conjugate root
by the root itself. -/
theorem algebraMap_kummerCharacter (hζ : (primitiveRoots n F).Nonempty)
    (hβ : β ^ n = algebraMap F E (b : F)) (σ : Gal(E/F)) :
    algebraMap F E (kummerCharacter hζ hβ σ : Fˣ) = σ β / β :=
  algebraMap_rootRatio hζ hβ (aut_pow_eq hβ σ)

/-- The Kummer character is independent of the chosen root of `b`. -/
theorem kummerCharacter_eq (hζ : (primitiveRoots n F).Nonempty)
    (hβ : β ^ n = algebraMap F E (b : F)) (hγ : γ ^ n = algebraMap F E (b : F)) :
    kummerCharacter hζ hβ = kummerCharacter hζ hγ := by
  apply MonoidHom.ext
  intro σ
  apply rootsOfUnity_algebraMap_injective (E := E)
  dsimp only
  rw [algebraMap_kummerCharacter, algebraMap_kummerCharacter,
    ← algebraMap_rootRatio_mul hζ hβ hγ, map_mul, AlgEquiv.commutes,
    mul_div_mul_left _ _ ((_root_.map_ne_zero (algebraMap F E)).2
      (Units.ne_zero (rootRatio hζ hβ hγ : Fˣ)))]

/-- Restricting an automorphism to a normal subfield and evaluating there
agrees with evaluating on the image of the root in the larger field. -/
theorem kummerCharacter_comp_restrictNormalHom {L : Type w} [Field L]
    [Algebra F L] [Algebra E L] [IsScalarTower F E L] [Normal F E]
    (hζ : (primitiveRoots n F).Nonempty) (hβ : β ^ n = algebraMap F E (b : F)) :
    (kummerCharacter hζ hβ).comp (AlgEquiv.restrictNormalHom E : Gal(L/F) →* Gal(E/F)) =
      kummerCharacter hζ (β := algebraMap E L β) (b := b) (by
        rw [← map_pow, hβ, ← IsScalarTower.algebraMap_apply]) := by
  apply MonoidHom.ext
  intro σ
  apply rootsOfUnity_algebraMap_injective (E := L)
  dsimp only [MonoidHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply F E L
      (↑(kummerCharacter hζ hβ (AlgEquiv.restrictNormalHom E σ) : Fˣ) : F),
    algebraMap_kummerCharacter, algebraMap_kummerCharacter, map_div₀]
  exact congrArg (fun x : L => x / algebraMap E L β) (σ.restrictNormal_commutes E β)

/-- The character of a radical splitting field is faithful, since it determines
the automorphism on every root of its defining polynomial. -/
theorem kummerCharacter_injective (hζ : (primitiveRoots n F).Nonempty)
    (hβ : β ^ n = algebraMap F E (b : F)) [IsSplittingField F E (X ^ n - C (b : F))] :
    Function.Injective (kummerCharacter hζ hβ) := by
  intro σ τ hστ
  have hequalizer : σ.toAlgHom.equalizer τ.toAlgHom = ⊤ := by
    rw [eq_top_iff, ← IsSplittingField.adjoin_rootSet E (X ^ n - C (b : F)),
      Algebra.adjoin_le_iff]
    intro x hx
    have hxpow : x ^ n = algebraMap F E (b : F) := by
      simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using
        (mem_rootSet_of_ne (X_pow_sub_C_ne_zero (NeZero.pos n) (b : F))).mp hx
    have hratio : σ x / x = τ x / x := by
      rw [← algebraMap_kummerCharacter hζ hxpow, ← algebraMap_kummerCharacter hζ hxpow,
        ← kummerCharacter_eq hζ hβ hxpow, hστ]
    exact (AlgHom.mem_equalizer _ _ _).mpr <| (div_left_inj' (root_ne_zero hxpow)).mp hratio
  exact AlgEquiv.ext fun x =>
    (AlgHom.mem_equalizer _ _ _).mp (hequalizer ▸ Algebra.mem_top (x := x))

/-- With the base roots of unity present, the actual radical splitting field
of a unit is a finite abelian extension even for a reducible binomial. -/
theorem isAbelianGalois_radicalField (hζ : (primitiveRoots n F).Nonempty) (b : Fˣ) :
    IsAbelianGalois F (radicalField F n (b : F)) := by
  let L := radicalField F n (b : F)
  have hβ := rootOfSplitsXPowSubC_pow (n := n) (b : F) L
  obtain ⟨ζ, hprim⟩ := hζ
  have hprimL := ((mem_primitiveRoots (NeZero.pos n)).mp hprim).map_of_injective
    (algebraMap F L).injective
  have hsep : (X ^ n - C (b : F)).Separable := by
    rw [← separable_map (algebraMap F L), Polynomial.map_sub, Polynomial.map_pow, map_X, map_C,
      X_pow_sub_C_eq_prod hprimL (NeZero.pos n) hβ, separable_prod_X_sub_C_iff']
    exact hprimL.injOn_pow_mul (root_ne_zero hβ)
  let : IsGalois F L := IsGalois.of_separable_splitting_field hsep
  refine { is_comm.comm := ?_ }
  intro σ τ
  apply kummerCharacter_injective ⟨ζ, hprim⟩ hβ
  rw [map_mul, map_mul, mul_comm]

end Langlands.KTheory
