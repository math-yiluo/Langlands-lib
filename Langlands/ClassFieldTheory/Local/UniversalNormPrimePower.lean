import Langlands.ClassFieldTheory.Local.KummerRadicalFields
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesProof
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof
import Langlands.ClassFieldTheory.Local.RelativeInvariantEquivalences

/-! # Prime-power divisibility of actual universal norms -/

noncomputable section

namespace Langlands.LocalClassField

universe u

/-- Units that are norms from every actual finite abelian intermediate extension. -/
def universalNormSubgroup (K : Type u) [Field K] : Subgroup Kˣ where
  carrier := {a | ∀ (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E], a ∈ normSubgroup K E}
  one_mem' := fun E _ _ => (normSubgroup K E).one_mem
  mul_mem' := fun ha hb E _ _ => (normSubgroup K E).mul_mem (ha E) (hb E)
  inv_mem' := fun ha E _ _ => (normSubgroup K E).inv_mem (ha E)

end Langlands.LocalClassField

namespace Langlands.ClassFieldTheory.Local.KummerNorm

universe u

open Polynomial Langlands.LocalClassField

/-- A local cyclic extension of degree greater than one has a nonnorm unit. -/
theorem exists_not_norm_of_cyclic_coordinate
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (L : Type u) [Field L] [Algebra F.Carrier L]
    [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L]
    {n : ℕ} [NeZero n] (χ : Gal(L/F.Carrier) ≃* Multiplicative (ZMod n))
    (hdegree : 1 < Module.finrank F.Carrier L) :
    ∃ b : F.Carrierˣ, b ∉ normSubgroup F.Carrier L := by
  let I := localInvariantFamily unramifiedH2Exhaustion p
  let e := I.relativeZModEquiv
    (localInvariantFamilyRelativeImages unramifiedH2Exhaustion p) F L
  have hone : (1 : ZMod (Module.finrank F.Carrier L)) ≠ 0 := by
    intro h
    have := ZMod.one_eq_zero_iff.mp h
    omega
  have hx : e.symm 1 ≠ 0 := by
    intro h
    apply hone
    calc
      (1 : ZMod (Module.finrank F.Carrier L)) = e (e.symm 1) :=
        (e.apply_symm_apply _).symm
      _ = 0 := by rw [h, map_zero]
  obtain ⟨b, hb⟩ := CyclicClassAlgebra.exists_cyclicClass_eq χ (e.symm 1)
  refine ⟨b, fun h => hx ?_⟩
  rw [← hb]
  exact (CyclicClassAlgebra.cyclicClass_eq_zero_iff χ b).mpr h

/-- If the base contains a primitive prime-order root, every universal norm is
that prime's power of a base unit. -/
theorem universalNorm_is_prime_power
    {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    {q : ℕ} (hq : q.Prime) (ζ : F.Carrierˣ)
    (hζ : IsPrimitiveRoot (ζ : F.Carrier) q) (a : F.Carrierˣ)
    (ha : ∀ (E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier))
      [FiniteDimensional F.Carrier E] [IsAbelianGalois F.Carrier E],
        a ∈ normSubgroup F.Carrier E) :
    ∃ c : F.Carrierˣ, c ^ q = a := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  by_contra hpower
  have Hanopower : ∀ c : F.Carrier, c ^ q ≠ (a : F.Carrier) := by
    intro c hc
    apply hpower
    have hc0 : c ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hq.ne_zero] at hc
      exact Units.ne_zero a hc.symm
    exact ⟨Units.mk0 c hc0, Units.ext hc⟩
  have Ha : Irreducible (X ^ q - C (a : F.Carrier)) :=
    X_pow_sub_C_irreducible_of_prime hq Hanopower
  let L := radicalField F.Carrier q (a : F.Carrier)
  let : IsAbelianGalois F.Carrier L := radicalField_isAbelianGalois Ha hζ
  have hdegree : Module.finrank F.Carrier L = q := radicalField_finrank Ha hζ
  obtain ⟨b, hb⟩ := exists_not_norm_of_cyclic_coordinate F L
    (autEquivZmod Ha L hζ) (by rw [hdegree]; exact hq.one_lt)
  have Hbnopower : ∀ c : F.Carrier, c ^ q ≠ (b : F.Carrier) := by
    intro c hc
    apply hb
    have hc0 : c ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hq.ne_zero] at hc
      exact Units.ne_zero b hc.symm
    refine ⟨Units.map (algebraMap F.Carrier L).toMonoidHom (Units.mk0 c hc0), ?_⟩
    apply Units.ext
    change Algebra.norm F.Carrier (algebraMap F.Carrier L c) = (b : F.Carrier)
    rw [Algebra.norm_algebraMap, hdegree]
    exact hc
  have Hb : Irreducible (X ^ q - C (b : F.Carrier)) :=
    X_pow_sub_C_irreducible_of_prime hq Hbnopower
  let R := radicalField F.Carrier q (b : F.Carrier)
  let : IsAbelianGalois F.Carrier R := radicalField_isAbelianGalois Hb hζ
  exact hb ((radicalField_norm_iff a b ζ Ha Hb hζ).mpr (ha R))

end Langlands.ClassFieldTheory.Local.KummerNorm
