import Langlands.ClassFieldTheory.Local.CyclicClassAlgebra
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyRelativeImagesProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyInflationProof
import Langlands.ClassFieldTheory.Local.LocalInvariantFamilyArithmeticProof
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof
import Langlands.ClassFieldTheory.Local.NormExistenceAbelianReduction
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-! # Finite Artin maps from cyclic symbols

For a finite abelian extension `D/K` of a p-adic field with `n = [D : K]`,
the relative invariant of the cyclic carry class `(χ, a)` lies in `(1/n)ℤ/ℤ`.
It is additive in the unit and in the character `χ : Gal(D/K) → ℤ/n`, so finite
abelian duality gives one Galois element `artinSymbol a` whose value under
every such character is that symbol.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

namespace FiniteArtinSymbol

universe u

open Langlands.LocalClassField CyclicClassAlgebra

section Duality

/-- `Multiplicative (ZMod n)` contains a primitive `n`-th root of unity and its
`n`-th roots of unity form a cyclic group. -/
theorem hasEnoughRootsOfUnity (n : ℕ) [NeZero n] :
    HasEnoughRootsOfUnity (Multiplicative (ZMod n)) n where
  prim := ⟨Multiplicative.ofAdd 1, by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]⟩
  cyc := by
    have : IsCyclic (Multiplicative (ZMod n))ˣ :=
      isCyclic_of_surjective (toUnits : Multiplicative (ZMod n) ≃* _).toMonoidHom
        toUnits.surjective
    infer_instance

variable {G : Type*} [CommGroup G] [Finite G] {n : ℕ} [NeZero n]

omit [Finite G] in
theorem hasEnoughRootsOfUnity_exponent (hG : Nat.card G ∣ n) :
    HasEnoughRootsOfUnity (Multiplicative (ZMod n)) (Monoid.exponent G) :=
  haveI := hasEnoughRootsOfUnity n
  HasEnoughRootsOfUnity.of_dvd _ (Group.exponent_dvd_nat_card.trans hG)

/-- Characters into `ℤ/n` separate the points of a finite abelian group whose
order divides `n`. -/
theorem eq_of_forall_character (hG : Nat.card G ∣ n) {g g' : G}
    (h : ∀ χ : G →* Multiplicative (ZMod n), χ g = χ g') : g = g' := by
  have := hasEnoughRootsOfUnity_exponent (G := G) hG
  refine (CommGroup.forall_apply_eq_apply_iff G (M := Multiplicative (ZMod n))).mp
    fun φ => ?_
  exact Units.ext (h ((Units.coeHom _).comp φ))

/-- Characters into `ℤ/n` detect membership in a subgroup of a finite abelian group whose
order divides `n`. -/
theorem mem_of_forall_character (hG : Nat.card G ∣ n) (H : Subgroup G) (x : G)
    (h : ∀ χ : G →* Multiplicative (ZMod n), (∀ y ∈ H, χ y = 1) → χ x = 1) : x ∈ H := by
  have := hasEnoughRootsOfUnity_exponent (G := G) hG
  refine (CommGroup.forall_monoidHom_apply_eq_one_iff (Multiplicative (ZMod n)) H x).1
    fun φ hφ => ?_
  exact Units.val_eq_one.1 (h ((Units.coeHom _).comp φ) fun y hy => by simp [hφ y hy])

/-- Finite abelian duality with values in `ℤ/n`: homomorphisms on the character
group are evaluations at unique group elements. -/
def dualEquiv (hG : Nat.card G ∣ n) :
    ((G →* Multiplicative (ZMod n)) →* Multiplicative (ZMod n)) ≃* G :=
  haveI := hasEnoughRootsOfUnity_exponent (G := G) hG
  let e : Multiplicative (ZMod n) ≃* (Multiplicative (ZMod n))ˣ := toUnits
  ((MulEquiv.monoidHomCongrLeft (MulEquiv.monoidHomCongrRight e)).trans
    (MulEquiv.monoidHomCongrRight e)).trans
    (CommGroup.monoidHomMonoidHomEquiv G (Multiplicative (ZMod n)))

theorem apply_dualEquiv (hG : Nat.card G ∣ n)
    (s : (G →* Multiplicative (ZMod n)) →* Multiplicative (ZMod n))
    (χ : G →* Multiplicative (ZMod n)) :
    χ (dualEquiv hG s) = s χ := by
  have := hasEnoughRootsOfUnity_exponent (G := G) hG
  let e : Multiplicative (ZMod n) ≃* (Multiplicative (ZMod n))ˣ := toUnits
  have h := CommGroup.apply_monoidHomMonoidHomEquiv (Multiplicative (ZMod n))
    (MulEquiv.monoidHomCongrRight e χ)
    ((MulEquiv.monoidHomCongrLeft (MulEquiv.monoidHomCongrRight e)).trans
      (MulEquiv.monoidHomCongrRight e) s)
  have h' : e (χ (dualEquiv hG s)) =
      e (s ((MulEquiv.monoidHomCongrRight e).symm (MulEquiv.monoidHomCongrRight e χ))) := h
  rw [MulEquiv.symm_apply_apply] at h'
  exact e.injective h'

/-- Multiplication by `k` from `ℤ/e` to `ℤ/n` when `n = e * k`. -/
def scaleHom {e n : ℕ} (k : ℕ) (hn : n = e * k) : ZMod e →+ ZMod n :=
  ZMod.lift e ⟨k • Int.castAddHom (ZMod n), by
    change k • ((e : ℤ) : ZMod n) = 0
    rw [Int.cast_natCast, nsmul_eq_mul, ← Nat.cast_mul, mul_comm, ← hn, ZMod.natCast_self]⟩

theorem scaleHom_val {e n : ℕ} [NeZero e] [NeZero n] (k : ℕ) (hn : n = e * k) (x : ZMod e) :
    (scaleHom k hn x).val = k * x.val := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => NeZero.ne n (by rw [hn, h, mul_zero])
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← Int.cast_natCast, scaleHom, ZMod.lift_coe]
  change (k • ((x.val : ℤ) : ZMod n)).val = _
  rw [Int.cast_natCast, nsmul_eq_mul, ← Nat.cast_mul, ZMod.val_natCast, Nat.mod_eq_of_lt]
  rw [hn, mul_comm e k]
  exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x) hk

theorem denominatorEquiv_scaleHom {e n : ℕ} [NeZero e] [NeZero n] (k : ℕ) (hn : n = e * k)
    (x : ZMod e) :
    (denominatorEquiv n (NeZero.pos n) (scaleHom k hn x) : RationalModIntegers) =
      denominatorEquiv e (NeZero.pos e) x := by
  have hk : (k : ℚ) ≠ 0 := by
    exact_mod_cast fun h : k = 0 => NeZero.ne n (by rw [hn, h, mul_zero])
  have he : (e : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne e
  rw [denominatorEquiv_apply, denominatorEquiv_apply, ZMod.cast_eq_val, ZMod.cast_eq_val,
    scaleHom_val, hn]
  congr 1
  push_cast
  field_simp

end Duality

section Symbol

open scoped IsMulCommutative

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (D : Type u) [Field D]
  [Algebra F.Carrier D] [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]

/-- The degree of a finite extension is nonzero. -/
scoped instance finrank_neZero : NeZero (Module.finrank F.Carrier D) :=
  ⟨Module.finrank_pos.ne'⟩

/-- The relative invariant of the published local invariant family. -/
abbrev relInv : relativeCohomology F.Carrier D 2 →+ RationalModIntegers :=
  (localInvariantFamily unramifiedH2Exhaustion.{u} p).relative F D

theorem relInv_injective : Function.Injective (relInv F D) :=
  (localInvariantFamilyRelativeImages.{u} unramifiedH2Exhaustion p F D).1

variable {F D}

omit [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D] in
theorem character_pow_eq_one {e : ℕ} (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) :
    ψ ^ e = 1 := by
  ext g
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem relInv_cyclicClass_mem {e : ℕ} [NeZero e]
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    relInv F D (cyclicClass F.Carrier D ψ a) ∈ denominatorSubgroup e := by
  change e • _ = 0
  rw [← map_nsmul, ← cyclicClass_pow_character, character_pow_eq_one,
    cyclicClass_one_character, map_zero]

/-- The symbol of a character `ψ` into `ℤ/e` and a unit `a`: the residue modulo `e`
whose fraction is the invariant of the carry class `(ψ, a)`. -/
def symbolValue {e : ℕ} [NeZero e] (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e))
    (a : F.Carrierˣ) : ZMod e :=
  (denominatorEquiv e (NeZero.pos e)).symm ⟨_, relInv_cyclicClass_mem ψ a⟩

theorem symbolValue_eq_iff {e : ℕ} [NeZero e]
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) (x : ZMod e) :
    symbolValue ψ a = x ↔
      (denominatorEquiv e (NeZero.pos e) x : RationalModIntegers) =
        relInv F D (cyclicClass F.Carrier D ψ a) := by
  rw [symbolValue, AddEquiv.symm_apply_eq, eq_comm, Subtype.ext_iff]

theorem denominatorEquiv_symbolValue {e : ℕ} [NeZero e]
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    (denominatorEquiv e (NeZero.pos e) (symbolValue ψ a) : RationalModIntegers) =
      relInv F D (cyclicClass F.Carrier D ψ a) :=
  (symbolValue_eq_iff ψ a _).1 rfl

theorem symbolValue_mul_character {e : ℕ} [NeZero e]
    (ψ₁ ψ₂ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    symbolValue (ψ₁ * ψ₂) a = symbolValue ψ₁ a + symbolValue ψ₂ a := by
  rw [symbolValue_eq_iff, map_add, AddSubgroup.coe_add, denominatorEquiv_symbolValue,
    denominatorEquiv_symbolValue, cyclicClass_mul_character, map_add]

theorem symbolValue_one_character {e : ℕ} [NeZero e] (a : F.Carrierˣ) :
    symbolValue (1 : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) a = 0 := by
  rw [symbolValue_eq_iff, map_zero, AddSubgroup.coe_zero, cyclicClass_one_character,
    map_zero]

theorem symbolValue_mul {e : ℕ} [NeZero e]
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a b : F.Carrierˣ) :
    symbolValue ψ (a * b) = symbolValue ψ a + symbolValue ψ b := by
  rw [symbolValue_eq_iff, map_add, AddSubgroup.coe_add, denominatorEquiv_symbolValue,
    denominatorEquiv_symbolValue, cyclicClass_mul, map_add]

variable (F D)

/-- The symbol of a unit, as a homomorphism on characters into `ℤ/[D : F]`. -/
def symbolHom (a : F.Carrierˣ) :
    (Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D))) →*
      Multiplicative (ZMod (Module.finrank F.Carrier D)) where
  toFun ψ := Multiplicative.ofAdd (symbolValue ψ a)
  map_one' := by rw [symbolValue_one_character, ofAdd_zero]
  map_mul' ψ₁ ψ₂ := by rw [symbolValue_mul_character, ofAdd_add]

theorem card_galois_dvd : Nat.card Gal(D/F.Carrier) ∣ Module.finrank F.Carrier D :=
  (IsGalois.card_aut_eq_finrank F.Carrier D).dvd

variable [IsMulCommutative Gal(D/F.Carrier)]

/-- The Galois element attached to a unit by duality: every character into
`ℤ/[D : F]` takes it to the symbol of the character and the unit. -/
def artinSymbolFun (a : F.Carrierˣ) : Gal(D/F.Carrier) :=
  dualEquiv (card_galois_dvd F D) (symbolHom F D a)

theorem character_artinSymbolFun
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (a : F.Carrierˣ) :
    ψ (artinSymbolFun F D a) = Multiplicative.ofAdd (symbolValue ψ a) :=
  apply_dualEquiv _ _ ψ

/-- The finite Artin symbol of `D/F` as a homomorphism. -/
def artinSymbol : F.Carrierˣ →* Gal(D/F.Carrier) :=
  MonoidHom.mk' (artinSymbolFun F D) fun a b => by
    refine eq_of_forall_character (card_galois_dvd F D) fun ψ => ?_
    rw [character_artinSymbolFun, map_mul, character_artinSymbolFun,
      character_artinSymbolFun, symbolValue_mul, ofAdd_add]

theorem character_artinSymbol
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (a : F.Carrierˣ) :
    ψ (artinSymbol F D a) = Multiplicative.ofAdd (symbolValue ψ a) :=
  character_artinSymbolFun F D ψ a

/-- On an extension with an arithmetic unramified coordinate, the Artin symbol of a
uniformizer is the arithmetic Frobenius generator of the coordinate. -/
theorem artinSymbol_eq_of_arithmeticCoordinate
    (χ : Gal(D/F.Carrier) ≃* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (hχ : IsArithmeticUnramifiedCoordinate F D χ) (a : F.Carrierˣ)
    (ha : F.canonicalTopologicalData.ord (a : F.Carrier) = 1) :
    artinSymbol F D a = χ.symm (Multiplicative.ofAdd 1) := by
  rw [MulEquiv.eq_symm_apply]
  have h := character_artinSymbol F D χ.toMonoidHom a
  rw [MulEquiv.coe_toMonoidHom] at h
  rw [h]
  congr 1
  rw [symbolValue_eq_iff, denominatorEquiv_one]
  exact (localInvariantFamilyArithmetic.{u} unramifiedH2Exhaustion p F D _ χ hχ a ha).symm

/-- The defining property of the Artin symbol holds for characters into `ℤ/e` for every
divisor `e` of the degree. -/
theorem character_artinSymbol_of_dvd {e : ℕ} [NeZero e]
    (he : e ∣ Module.finrank F.Carrier D)
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    ψ (artinSymbol F D a) = Multiplicative.ofAdd (symbolValue ψ a) := by
  obtain ⟨k, hn⟩ := he
  let ψ' : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)) :=
    (AddMonoidHom.toMultiplicative (scaleHom k hn)).comp ψ
  have hval : ∀ g, (ψ' g).toAdd.val = k * (ψ g).toAdd.val := fun g =>
    scaleHom_val k hn (ψ g).toAdd
  have hcl := cyclicClass_eq_of_val_eq hn ψ' ψ hval a
  have h1 : scaleHom k hn (ψ (artinSymbol F D a)).toAdd = symbolValue ψ' a :=
    congrArg Multiplicative.toAdd (character_artinSymbol F D ψ' a)
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, eq_comm, symbolValue_eq_iff, ← denominatorEquiv_scaleHom k hn, h1,
    denominatorEquiv_symbolValue, hcl]

/-- The character values of the Artin symbol, as invariants. -/
theorem denominatorEquiv_character_artinSymbol {e : ℕ} [NeZero e]
    (he : e ∣ Module.finrank F.Carrier D)
    (ψ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    (denominatorEquiv e (NeZero.pos e) (ψ (artinSymbol F D a)).toAdd : RationalModIntegers) =
      relInv F D (cyclicClass F.Carrier D ψ a) := by
  rw [character_artinSymbol_of_dvd F D he, toAdd_ofAdd, denominatorEquiv_symbolValue]

end Symbol

section Tower

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {D : Type u} [Field D]
  [Algebra F.Carrier D] [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]
  (E : Type u) [Field E] [Algebra F.Carrier E] [FiniteDimensional F.Carrier E]
  [IsGalois F.Carrier E] [Algebra E D] [IsScalarTower F.Carrier E D]

theorem relInv_relativeInflation (x : relativeCohomology F.Carrier E 2) :
    relInv F D (relativeInflation F.Carrier E D 2 x) = relInv F E x := by
  have : FiniteDimensional E D := FiniteDimensional.right F.Carrier E D
  exact localInvariantFamilyInflation.{u} unramifiedH2Exhaustion p F E D x

theorem relativeInflation_injective :
    Function.Injective (relativeInflation F.Carrier E D 2) := fun x y h =>
  relInv_injective F E <| by
    rw [← relInv_relativeInflation (D := D) E x, h, relInv_relativeInflation E y]

variable [IsMulCommutative Gal(D/F.Carrier)] [IsMulCommutative Gal(E/F.Carrier)]

open scoped IsMulCommutative in
/-- The Artin symbols of a tower are compatible with restriction. -/
theorem restrictNormalHom_artinSymbol (a : F.Carrierˣ) :
    AlgEquiv.restrictNormalHom E (artinSymbol F D a) = artinSymbol F E a := by
  have hdvd : Module.finrank F.Carrier E ∣ Module.finrank F.Carrier D :=
    Dvd.intro _ (Module.finrank_mul_finrank F.Carrier E D)
  refine eq_of_forall_character (card_galois_dvd F E) fun χ => ?_
  have h := denominatorEquiv_character_artinSymbol F D hdvd
    (χ.comp (AlgEquiv.restrictNormalHom E)) a
  rw [MonoidHom.comp_apply, ← relativeInflation_cyclicClass, relInv_relativeInflation,
    ← denominatorEquiv_character_artinSymbol F E dvd_rfl χ a] at h
  exact Multiplicative.toAdd.injective
    ((denominatorEquiv _ (NeZero.pos _)).injective (Subtype.ext h))

end Tower

section Kernel

open IntermediateField

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {D : Type u} [Field D]
  [Algebra F.Carrier D] [FiniteDimensional F.Carrier D] [IsGalois F.Carrier D]

/-- A character factored through the Galois group of the fixed field of its kernel. -/
def kernelFieldCharacter {e : ℕ} (χ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) :
    Gal(fixedField χ.ker/F.Carrier) →* Multiplicative (ZMod e) :=
  (QuotientGroup.kerLift χ).comp (IsGalois.normalAutEquivQuotient χ.ker).symm.toMonoidHom

theorem kernelFieldCharacter_comp {e : ℕ} (χ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) :
    (kernelFieldCharacter χ).comp (AlgEquiv.restrictNormalHom (fixedField χ.ker)) = χ := by
  ext σ
  change QuotientGroup.kerLift χ ((IsGalois.normalAutEquivQuotient χ.ker).symm
    (AlgEquiv.restrictNormalHom (fixedField χ.ker) σ)) = χ σ
  rw [← IsGalois.normalAutEquivQuotient_apply, MulEquiv.symm_apply_apply]
  rfl

theorem kernelFieldCharacter_injective {e : ℕ}
    (χ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) :
    Function.Injective (kernelFieldCharacter χ) :=
  (QuotientGroup.kerLift_injective χ).comp
    (IsGalois.normalAutEquivQuotient χ.ker).symm.injective

/-- The carry class of a character vanishes exactly on the norms from the fixed field of
its kernel. -/
theorem cyclicClass_eq_zero_iff_mem_normSubgroup {e : ℕ} [NeZero e]
    (χ : Gal(D/F.Carrier) →* Multiplicative (ZMod e)) (a : F.Carrierˣ) :
    cyclicClass F.Carrier D χ a = 0 ↔ a ∈ normSubgroup F.Carrier (fixedField χ.ker) := by
  have h := relativeInflation_cyclicClass F.Carrier (fixedField χ.ker) D
    (kernelFieldCharacter χ) a
  rw [kernelFieldCharacter_comp] at h
  rw [← h, (injective_iff_map_eq_zero' (CategoryTheory.ConcreteCategory.hom
    (relativeInflation F.Carrier (fixedField χ.ker) D 2))).1 (relativeInflation_injective _)]
  exact cyclicClass_eq_zero_iff_of_injective _ (kernelFieldCharacter_injective χ) a

variable [IsMulCommutative Gal(D/F.Carrier)]

open scoped IsMulCommutative in
theorem character_artinSymbol_eq_one_iff
    (χ : Gal(D/F.Carrier) →* Multiplicative (ZMod (Module.finrank F.Carrier D)))
    (a : F.Carrierˣ) :
    χ (artinSymbol F D a) = 1 ↔ cyclicClass F.Carrier D χ a = 0 := by
  rw [character_artinSymbol, ofAdd_eq_one, symbolValue_eq_iff, map_zero,
    ZeroMemClass.coe_zero, eq_comm, map_eq_zero_iff _ (relInv_injective F D)]

open scoped IsMulCommutative in
theorem normSubgroup_le_ker_artinSymbol :
    normSubgroup F.Carrier D ≤ (artinSymbol F D).ker := by
  intro a ha
  rw [MonoidHom.mem_ker]
  refine eq_of_forall_character (card_galois_dvd F D) fun χ => ?_
  rw [map_one, character_artinSymbol_eq_one_iff, cyclicClass_eq_zero_iff_mem_normSubgroup]
  exact normSubgroup_le_of_tower F.Carrier D (fixedField χ.ker) ha

end Kernel

section Surjective

open IntermediateField

open scoped IsMulCommutative

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {D : Type u} [Field D]
  [Algebra F.Carrier D] [FiniteDimensional F.Carrier D] [IsAbelianGalois F.Carrier D]

theorem artinSymbol_surjective : Function.Surjective (artinSymbol F D) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff]
  intro σ _
  refine mem_of_forall_character (card_galois_dvd F D) _ σ fun χ hχ => ?_
  suffices hker : χ.ker = ⊤ by
    have : σ ∈ χ.ker := by rw [hker]; exact Subgroup.mem_top σ
    exact this
  have htop : normSubgroup F.Carrier (fixedField χ.ker) = ⊤ :=
    eq_top_iff.2 fun a _ => (cyclicClass_eq_zero_iff_mem_normSubgroup χ a).1
      ((character_artinSymbol_eq_one_iff χ a).1 (hχ _ ⟨a, rfl⟩))
  have hrank : Module.finrank F.Carrier (fixedField χ.ker) = 1 := by
    rw [← normSubgroup_index_eq_finrank F, htop, Subgroup.index_top]
  rw [← fixingSubgroup_fixedField χ.ker, finrank_eq_one_iff.1 hrank,
    fixingSubgroup_bot]

/-- The kernel of the Artin symbol is exactly the norm subgroup. -/
theorem ker_artinSymbol : (artinSymbol F D).ker = normSubgroup F.Carrier D := by
  have hle := normSubgroup_le_ker_artinSymbol (F := F) (D := D)
  have h1 : (artinSymbol F D).ker.index = Module.finrank F.Carrier D := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 artinSymbol_surjective,
      Subgroup.card_top, IsGalois.card_aut_eq_finrank]
  have hrel := Subgroup.relIndex_mul_index hle
  rw [h1, normSubgroup_index_eq_finrank F D] at hrel
  have h2 : (normSubgroup F.Carrier D).relIndex (artinSymbol F D).ker = 1 :=
    Nat.eq_of_mul_eq_mul_right Module.finrank_pos (hrel.trans (one_mul _).symm)
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h2) hle

end Surjective

end FiniteArtinSymbol

end Langlands.ClassFieldTheory.Local
