import Langlands.ClassFieldTheory.Local.FiniteArtinSymbol

/-!
# Finite Artin character symbols on arbitrary Galois abelianizations
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local.FiniteArtinSymbol

universe u

open Langlands.LocalClassField CyclicClassAlgebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (D : Type u)
  [Field D] [Algebra F.Carrier D] [FiniteDimensional F.Carrier D]
  [IsGalois F.Carrier D]

local instance finiteAbelianizedArtinDegree_neZero :
    NeZero (Module.finrank F.Carrier D) := ⟨Module.finrank_pos.ne'⟩

/-- The order of the actual finite Galois abelianization divides the field degree. -/
lemma card_abelianized_galois_dvd :
    Nat.card (Abelianization Gal(D/F.Carrier)) ∣ Module.finrank F.Carrier D :=
  (Subgroup.card_quotient_dvd_card (commutator Gal(D/F.Carrier))).trans
    (card_galois_dvd F D)

/-- The carry symbol as a homomorphism on characters of the Galois abelianization.
Every such character is pulled back through the actual quotient projection. -/
def abelianizedSymbolHom (a : F.Carrierˣ) :
    (Abelianization Gal(D/F.Carrier) →*
      Multiplicative (ZMod (Module.finrank F.Carrier D))) →*
        Multiplicative (ZMod (Module.finrank F.Carrier D)) where
  toFun ψ := Multiplicative.ofAdd (symbolValue (ψ.comp Abelianization.of) a)
  map_one' := by
    change Multiplicative.ofAdd (symbolValue (1 : Gal(D/F.Carrier) →* _) a) = 1
    rw [symbolValue_one_character, ofAdd_zero]
  map_mul' ψ χ := by
    change Multiplicative.ofAdd
      (symbolValue (ψ.comp Abelianization.of * χ.comp Abelianization.of) a) = _
    rw [symbolValue_mul_character, ofAdd_add]

/-- Arithmetic carry-symbol reciprocity valued in the actual finite Galois
abelianization, including when the finite extension is not abelian. -/
def abelianizedArtinSymbol : F.Carrierˣ →* Abelianization Gal(D/F.Carrier) :=
  MonoidHom.mk'
    (fun a => dualEquiv (card_abelianized_galois_dvd F D) (abelianizedSymbolHom F D a))
    (fun a b => by
      apply eq_of_forall_character (card_abelianized_galois_dvd F D)
      intro ψ
      rw [apply_dualEquiv, map_mul, apply_dualEquiv, apply_dualEquiv]
      change Multiplicative.ofAdd (symbolValue (ψ.comp Abelianization.of) (a * b)) = _
      rw [symbolValue_mul, ofAdd_add]
      rfl)

/-- Every character of the original Galois group evaluates the constructed
abelianized symbol as its published carry-symbol value. -/
theorem character_abelianizedArtinSymbol
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (a : F.Carrierˣ) :
    Abelianization.lift ψ (abelianizedArtinSymbol F D a) =
      Multiplicative.ofAdd (symbolValue ψ a) := by
  have h := apply_dualEquiv (card_abelianized_galois_dvd F D)
    (abelianizedSymbolHom F D a) (Abelianization.lift ψ)
  have hp : (Abelianization.lift ψ).comp Abelianization.of = ψ := by
    ext g
    rfl
  change Abelianization.lift ψ (abelianizedArtinSymbol F D a) =
    Multiplicative.ofAdd (symbolValue ((Abelianization.lift ψ).comp Abelianization.of) a) at h
  rw [hp] at h
  exact h

/-- The evaluation formula holds for every character modulus dividing the field degree. -/
theorem character_abelianizedArtinSymbol_of_dvd {e : ℕ} [NeZero e]
    (he : e ∣ Module.finrank F.Carrier D)
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    Abelianization.lift ψ (abelianizedArtinSymbol F D a) =
      Multiplicative.ofAdd (symbolValue ψ a) := by
  obtain ⟨k, hn⟩ := he
  let ψ' : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)) :=
    (AddMonoidHom.toMultiplicative (scaleHom k hn)).comp ψ
  have hval : ∀ g, (ψ' g).toAdd.val = k * (ψ g).toAdd.val := fun g =>
    scaleHom_val k hn (ψ g).toAdd
  have hcl := cyclicClass_eq_of_val_eq hn ψ' ψ hval a
  have heval (x : Abelianization Gal(D/F.Carrier)) :
      (Abelianization.lift ψ' x).toAdd =
        scaleHom k hn (Abelianization.lift ψ x).toAdd := by
    refine QuotientGroup.induction_on x ?_
    intro g
    rfl
  have h1 : scaleHom k hn (Abelianization.lift ψ (abelianizedArtinSymbol F D a)).toAdd =
      symbolValue ψ' a := by
    rw [← heval]
    exact congrArg Multiplicative.toAdd (character_abelianizedArtinSymbol F D ψ' a)
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, eq_comm, symbolValue_eq_iff, ← denominatorEquiv_scaleHom k hn,
    h1, denominatorEquiv_symbolValue, hcl]

/-- The character values, read as fractions, are the actual relative carry-class invariants. -/
theorem denominatorEquiv_character_abelianizedArtinSymbol {e : ℕ} [NeZero e]
    (he : e ∣ Module.finrank F.Carrier D)
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    (denominatorEquiv e (NeZero.pos e)
      (Abelianization.lift ψ (abelianizedArtinSymbol F D a)).toAdd : RationalModIntegers) =
        relInv F D (cyclicClass F.Carrier D ψ a) := by
  rw [character_abelianizedArtinSymbol_of_dvd F D he, toAdd_ofAdd,
    denominatorEquiv_symbolValue]

/-- In the abelian case, this construction is the published Artin symbol
followed by its actual abelianization projection. -/
theorem abelianizedArtinSymbol_eq_of_comm
    [IsMulCommutative Gal(D/F.Carrier)] (a : F.Carrierˣ) :
    abelianizedArtinSymbol F D a = Abelianization.of (artinSymbol F D a) := by
  apply eq_of_forall_character (card_abelianized_galois_dvd F D)
  intro ψ
  have hp : Abelianization.lift (ψ.comp Abelianization.of) = ψ :=
    Abelianization.lift.apply_symm_apply ψ
  rw [← hp, character_abelianizedArtinSymbol, Abelianization.lift_apply_of]
  exact (character_artinSymbol F D (ψ.comp Abelianization.of) a).symm

section Tower

variable (E : Type u) [Field E] [Algebra F.Carrier E]
  [FiniteDimensional F.Carrier E] [IsGalois F.Carrier E]
  [Algebra E D] [IsScalarTower F.Carrier E D]

/-- Arithmetic carry symbols on all finite Galois abelianizations commute with
actual normal restriction, without requiring either Galois group to be abelian. -/
theorem restrictNormalHom_abelianizedArtinSymbol (a : F.Carrierˣ) :
    Abelianization.map (AlgEquiv.restrictNormalHom E)
        (abelianizedArtinSymbol F D a) =
      abelianizedArtinSymbol F E a := by
  let := FiniteDimensional.right F.Carrier E D
  have hdvd : Module.finrank F.Carrier E ∣ Module.finrank F.Carrier D :=
    Dvd.intro _ (Module.finrank_mul_finrank F.Carrier E D)
  apply eq_of_forall_character (card_abelianized_galois_dvd F E)
  intro χ
  let ψ := χ.comp (Abelianization.of : Gal(E/F.Carrier) →* _)
  have h := denominatorEquiv_character_abelianizedArtinSymbol F D hdvd
    (ψ.comp (AlgEquiv.restrictNormalHom E)) a
  rw [← relativeInflation_cyclicClass, relInv_relativeInflation,
    ← denominatorEquiv_character_abelianizedArtinSymbol F E dvd_rfl ψ a] at h
  have hv := Multiplicative.toAdd.injective
    ((denominatorEquiv _ (NeZero.pos _)).injective (Subtype.ext h))
  have hχ : χ.comp (Abelianization.map
      (AlgEquiv.restrictNormalHom E : Gal(D/F.Carrier) →* Gal(E/F.Carrier))) =
      Abelianization.lift (ψ.comp (AlgEquiv.restrictNormalHom E)) := by
    apply Abelianization.hom_ext
    ext σ
    rfl
  have hψ : Abelianization.lift ψ = χ :=
    Abelianization.lift.apply_symm_apply χ
  rw [← hχ, hψ] at hv
  exact hv

end Tower

end Langlands.ClassFieldTheory.Local.FiniteArtinSymbol
