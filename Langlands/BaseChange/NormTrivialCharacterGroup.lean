import Langlands.BaseChange.CuspidalSigmaLift
import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.ClassFieldTheory.Local.NormUnitImageIndexSupport
import Langlands.LocalField.CharZeroPadicRealization
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! # Characters of the norm quotient and stabilizer divisibility -/

noncomputable section

namespace Langlands.BaseChange

open CharZeroLocalField LocalClassField

universe u v uV

section NormCharacters

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]

/-- The subgroup of determinant characters trivial on the field norm. -/
def normTrivialCharacterGroup (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E] :
    Subgroup (Fˣ →* ℂˣ) where
  carrier := {κ | IsNormTrivial E κ}
  one_mem' := isNormTrivial_one E
  mul_mem' := IsNormTrivial.mul
  inv_mem' := IsNormTrivial.inv

/-- Norm-trivial characters identify with the complex characters of the actual norm quotient. -/
def normTrivialCharacterEquiv [FiniteDimensional F E] :
    normTrivialCharacterGroup F E ≃ (NormQuotient F E →* ℂˣ) where
  toFun κ := QuotientGroup.lift (normSubgroup F E) κ.1 (by
    rintro _ ⟨x, rfl⟩
    exact κ.2 x)
  invFun η := ⟨η.comp (QuotientGroup.mk' (normSubgroup F E)), fun x => by
    change η (QuotientGroup.mk (normUnits F E x)) = 1
    rw [(QuotientGroup.eq_one_iff _).mpr (show normUnits F E x ∈ normSubgroup F E from
      ⟨x, rfl⟩), map_one]⟩
  left_inv κ := Subtype.ext (MonoidHom.ext fun _ => rfl)
  right_inv η := MonoidHom.ext (fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rfl)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]

/-- A cyclic local extension of degree `l` has `l` norm-trivial complex characters. -/
theorem card_normTrivialCharacterGroup {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l) :
    Nat.card (normTrivialCharacterGroup F E) = l := by
  let : FiniteDimensional F E := hσ.1
  let : IsGalois F E := hσ.isGalois
  let : IsAbelianGalois F E := hσ.isAbelianGalois
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
  have hindex : (normSubgroup F E).index = l :=
    (NormUnitImage.normSubgroup_index_eq_finrank K L).trans hσ.2.1
  let : (normSubgroup F E).FiniteIndex := Subgroup.finiteIndex_iff.mpr (hindex.trans_ne hσ.pos.ne')
  let d := Monoid.exponent (NormQuotient F E)
  have hd : d ≠ 0 := Monoid.exponent_ne_zero_of_finite (G := NormQuotient F E)
  let : NeZero d := ⟨hd⟩
  let : HasEnoughRootsOfUnity ℂ d :=
    ⟨⟨_, Complex.isPrimitiveRoot_exp d hd⟩, rootsOfUnity.isCyclic ℂ d⟩
  rw [Nat.card_congr (normTrivialCharacterEquiv (F := F) (E := E)),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (NormQuotient F E) ℂ]
  exact hindex

/-- The order of the norm-twist stabilizer divides the extension degree. -/
theorem normTwistStabilizer_card_dvd {σ : E ≃ₐ[F] E} {l n : ℕ} (hσ : IsCyclicAlgebra σ l)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) : Nat.card (normTwistStabilizer E π) ∣ l := by
  rw [← card_normTrivialCharacterGroup hσ]
  exact Subgroup.card_dvd_of_le (fun _ h => h.1)

end NormCharacters

end Langlands.BaseChange
