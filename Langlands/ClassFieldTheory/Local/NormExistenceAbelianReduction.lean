import Langlands.ClassFieldTheory.Local.NormExistenceFiniteSupport

/-! # Reduction of finite Galois norms to the maximal abelian subextension -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The fixed field of the commutator subgroup of the actual finite Galois group. -/
def maximalAbelianNormSubfield (K M : Type u) [Field K] [Field M] [Algebra K M] :
    IntermediateField K M :=
  IntermediateField.fixedField (commutator Gal(M/K))

variable (K M : Type u) [Field K] [Field M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

instance maximalAbelianNormSubfield_isAbelianGalois :
    IsAbelianGalois K (maximalAbelianNormSubfield K M) := by
  let : IsGalois K (maximalAbelianNormSubfield K M) := by
    unfold maximalAbelianNormSubfield
    infer_instance
  let e : Abelianization Gal(M/K) ≃* Gal((maximalAbelianNormSubfield K M)/K) :=
    IsGalois.normalAutEquivQuotient (commutator Gal(M/K))
  refine { is_comm := ⟨fun x y => ?_⟩ }
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  exact (e.map_mul a b).symm.trans ((congrArg e (mul_comm a b)).trans (e.map_mul b a))

omit [IsGalois K M] in
/-- In a finite tower, every upper norm is a norm from the middle field. -/
theorem normSubgroup_le_of_tower (L : Type u) [Field L]
    [Algebra K L] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] :
    Langlands.LocalClassField.normSubgroup K M ≤
      Langlands.LocalClassField.normSubgroup K L := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Langlands.LocalClassField.normUnits L M x, ?_⟩
  apply Units.ext
  exact Algebra.norm_norm (R := K) (S := L) (a := (x : M))

variable {p : ℕ} [Fact p.Prime]

/-- Maximal abelian reduction preserves the actual determinant-norm subgroup. -/
theorem normSubgroup_maximalAbelianNormSubfield (F : PadicField.{u} p) (M : Type u)
    [Field M] [Algebra F.Carrier M] [FiniteDimensional F.Carrier M]
    [IsGalois F.Carrier M] :
    Langlands.LocalClassField.normSubgroup F.Carrier M =
      Langlands.LocalClassField.normSubgroup F.Carrier
        (maximalAbelianNormSubfield F.Carrier M) := by
  let A := maximalAbelianNormSubfield F.Carrier M
  have hle := normSubgroup_le_of_tower F.Carrier M A
  have hi : (Langlands.LocalClassField.normSubgroup F.Carrier M).index =
      (Langlands.LocalClassField.normSubgroup F.Carrier A).index := by
    calc
      (Langlands.LocalClassField.normSubgroup F.Carrier M).index =
          Nat.card (Abelianization Gal(M/F.Carrier)) :=
        Nat.card_congr (finiteNormAbelianizationEquiv F M).toEquiv.symm
      _ = Nat.card Gal(A/F.Carrier) := Nat.card_congr
        (IsGalois.normalAutEquivQuotient (commutator Gal(M/F.Carrier))).toEquiv
      _ = Module.finrank F.Carrier A := IsGalois.card_aut_eq_finrank _ _
      _ = (Langlands.LocalClassField.normSubgroup F.Carrier A).index :=
        (normSubgroup_index_eq_finrank F A).symm
  let := finiteIndex_normSubgroup F M
  apply le_antisymm hle
  by_contra h
  have hs := Subgroup.index_strictAnti (lt_of_le_of_ne hle (fun he => h he.ge))
  exact (ne_of_lt hs) hi.symm

end Langlands.ClassFieldTheory.Local
