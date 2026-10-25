import Langlands.Global.AdelicFunctoriality.IdeleClassCyclotomicSecondInequalityStatement
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! # The cyclotomic reduction of the prime-degree second inequality

For a Galois extension `L/K` of number fields of prime degree `p`, adjoin a primitive `p`-th
root of unity `ζ` to `L`. The field `K(ζ)` has degree `< p` over `K`, so it is linearly
disjoint from `L`, the extension `L(ζ)/K(ζ)` is Galois of degree `p`, and `K(ζ)` contains a
primitive `p`-th root of unity. The norm tower law and the finite degree-power bound then
reduce the second inequality for `L/K` to the Kummer case `L(ζ)/K(ζ)`
(Artin–Tate, Chapter VI §1, Reduction 2).
-/

noncomputable section

universe u v w

namespace Langlands.Global.AdelicFunctoriality

open NumberField Polynomial
open scoped NumberField

/-- The image index of a composite norm divides the product of the two image indices. -/
theorem ideleClassNorm_range_index_dvd_mul_of_tower
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M] [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    (htower : ∀ x : IdeleClassGroup (𝓞 M) M,
      ideleClassNorm (K := K) (L := M) x =
        ideleClassNorm (K := K) (L := L) (ideleClassNorm (K := L) (L := M) x)) :
    (ideleClassNorm (K := K) (L := M)).toMonoidHom.range.index ∣
      (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index *
        (ideleClassNorm (K := L) (L := M)).toMonoidHom.range.index := by
  have hcomp : (ideleClassNorm (K := K) (L := M)).toMonoidHom =
      (ideleClassNorm (K := K) (L := L)).toMonoidHom.comp
        (ideleClassNorm (K := L) (L := M)).toMonoidHom := MonoidHom.ext htower
  rw [hcomp, MonoidHom.range_comp, Subgroup.index_map,
    Nat.mul_comm (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index]
  exact mul_dvd_mul (Subgroup.index_dvd_of_le le_sup_left) (dvd_refl _)

/-- The norm image from the top of a tower lies in the norm image from the middle field. -/
theorem ideleClassNorm_range_index_dvd_of_tower
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M] [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    (htower : ∀ x : IdeleClassGroup (𝓞 M) M,
      ideleClassNorm (K := K) (L := M) x =
        ideleClassNorm (K := K) (L := L) (ideleClassNorm (K := L) (L := M) x)) :
    (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣
      (ideleClassNorm (K := K) (L := M)).toMonoidHom.range.index := by
  have hcomp : (ideleClassNorm (K := K) (L := M)).toMonoidHom =
      (ideleClassNorm (K := K) (L := L)).toMonoidHom.comp
        (ideleClassNorm (K := L) (L := M)).toMonoidHom := MonoidHom.ext htower
  rw [hcomp, MonoidHom.range_comp]
  exact Subgroup.index_dvd_of_le
    ((ideleClassNorm (K := L) (L := M)).toMonoidHom.range.map_le_range _)

section CyclotomicRootField

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L] [CharZero L]
  (p : ℕ) [NeZero p]

/-- The field `K(ζ)` generated over `K` by the chosen primitive `p`-th root of unity
`ζ = IsCyclotomicExtension.zeta p L (CyclotomicField p L)` inside `L(ζ) = CyclotomicField p L`.
-/
def cyclotomicRootField : IntermediateField K (CyclotomicField p L) :=
  IntermediateField.adjoin K {IsCyclotomicExtension.zeta p L (CyclotomicField p L)}

theorem zeta_mem_cyclotomicRootField :
    IsCyclotomicExtension.zeta p L (CyclotomicField p L) ∈ cyclotomicRootField K L p :=
  IntermediateField.mem_adjoin_simple_self K _

/-- The chosen root of unity is integral over `K`: it is a root of the monic polynomial
`Φ_p`. -/
theorem isIntegral_cyclotomicField_zeta :
    IsIntegral K (IsCyclotomicExtension.zeta p L (CyclotomicField p L)) := by
  refine ⟨cyclotomic p K, cyclotomic.monic p K, ?_⟩
  rw [← aeval_def, aeval_def, ← eval_map, map_cyclotomic]
  exact (IsCyclotomicExtension.zeta_spec p L (CyclotomicField p L)).isRoot_cyclotomic
    (NeZero.pos p)

instance finiteDimensional_cyclotomicRootField :
    FiniteDimensional K (cyclotomicRootField K L p) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_cyclotomicField_zeta K L p)

/-- `[K(ζ) : K] ≤ φ(p)`, since the minimal polynomial of `ζ` divides `Φ_p`. -/
theorem finrank_cyclotomicRootField_le_totient :
    Module.finrank K (cyclotomicRootField K L p) ≤ p.totient := by
  rw [cyclotomicRootField,
    IntermediateField.adjoin.finrank (isIntegral_cyclotomicField_zeta K L p),
    ← natDegree_cyclotomic p K]
  refine natDegree_le_of_dvd (minpoly.dvd K _ ?_) (cyclotomic_ne_zero p K)
  rw [aeval_def, ← eval_map, map_cyclotomic]
  exact (IsCyclotomicExtension.zeta_spec p L (CyclotomicField p L)).isRoot_cyclotomic
    (NeZero.pos p)

/-- `K(ζ)` contains a primitive `p`-th root of unity. -/
theorem exists_isPrimitiveRoot_cyclotomicRootField :
    ∃ ζ : cyclotomicRootField K L p, IsPrimitiveRoot ζ p :=
  ⟨⟨_, zeta_mem_cyclotomicRootField K L p⟩,
    IsPrimitiveRoot.coe_submonoidClass_iff.mp
      (IsCyclotomicExtension.zeta_spec p L (CyclotomicField p L))⟩

/-- `K(ζ)` and the image of `L` generate `L(ζ)`. -/
theorem cyclotomicRootField_sup_fieldRange_eq_top :
    cyclotomicRootField K L p ⊔ (IsScalarTower.toAlgHom K L (CyclotomicField p L)).fieldRange =
      ⊤ := by
  set F := cyclotomicRootField K L p ⊔
    (IsScalarTower.toAlgHom K L (CyclotomicField p L)).fieldRange with hF
  let S : Subalgebra L (CyclotomicField p L) :=
    { F.toSubalgebra with
      algebraMap_mem' := fun x => (le_sup_right : _ ≤ F) ⟨x, rfl⟩ }
  have hζ : IsCyclotomicExtension.zeta p L (CyclotomicField p L) ∈ S :=
    (le_sup_left : _ ≤ F) (zeta_mem_cyclotomicRootField K L p)
  have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := L)
    (IsCyclotomicExtension.zeta_spec p L (CyclotomicField p L))
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Algebra.adjoin L {IsCyclotomicExtension.zeta p L (CyclotomicField p L)} := by
    rw [htop]
    exact Algebra.mem_top
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hζ) hx

/-- If `[L : K]` is prime to `[K(ζ) : K]`, then `[L(ζ) : K(ζ)] = [L : K]`. -/
theorem finrank_cyclotomicField_cyclotomicRootField
    (hcop : (Module.finrank K (cyclotomicRootField K L p)).Coprime (Module.finrank K L)) :
    Module.finrank (cyclotomicRootField K L p) (CyclotomicField p L) = Module.finrank K L := by
  have hL : Module.finrank K L =
      Module.finrank K (IsScalarTower.toAlgHom K L (CyclotomicField p L)).fieldRange :=
    (AlgEquiv.ofInjectiveField
      (IsScalarTower.toAlgHom K L (CyclotomicField p L))).toLinearEquiv.finrank_eq
  rw [hL] at hcop ⊢
  exact (IntermediateField.LinearDisjoint.of_finrank_coprime hcop).finrank_left_eq_finrank
    (cyclotomicRootField_sup_fieldRange_eq_top K L p)

/-- If `L/K` is Galois, so is `L(ζ)/K(ζ)`. -/
theorem isGalois_cyclotomicField_cyclotomicRootField [FiniteDimensional K L] [IsGalois K L] :
    IsGalois (cyclotomicRootField K L p) (CyclotomicField p L) := by
  let e := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom K L (CyclotomicField p L))
  have : IsGalois K (IsScalarTower.toAlgHom K L (CyclotomicField p L)).fieldRange :=
    IsGalois.of_algEquiv e
  have : FiniteDimensional K (IsScalarTower.toAlgHom K L (CyclotomicField p L)).fieldRange :=
    Module.Finite.equiv e.toLinearEquiv
  exact IsGalois.sup_right _ _
    (by rw [sup_comm]; exact cyclotomicRootField_sup_fieldRange_eq_top K L p)

end CyclotomicRootField

/-- Artin–Tate VI §1, Reduction 2: the finite degree-power bound for norm indices and the norm
tower law reduce the prime-degree second inequality to the case where the base field contains
a primitive root of unity of that prime order. -/
theorem ideleClassCyclotomicSecondInequalityReduction_holds :
    IdeleClassCyclotomicSecondInequalityReduction.{u, v} := by
  intro hfin htower hkummer K _ _ L _ _ _ _ hp
  have : NeZero (Module.finrank K L) := ⟨hp.ne_zero⟩
  let M := CyclotomicField (Module.finrank K L) L
  let E := cyclotomicRootField K L (Module.finrank K L)
  have hEpos : Module.finrank K E ≠ 0 := Module.finrank_pos.ne'
  have hElt : Module.finrank K E < Module.finrank K L :=
    lt_of_le_of_lt (finrank_cyclotomicRootField_le_totient K L _)
      (Nat.totient_lt _ hp.one_lt)
  have hcop : (Module.finrank K L).Coprime (Module.finrank K E) :=
    Nat.coprime_of_lt_prime hEpos hElt hp
  have hEM : Module.finrank E M = Module.finrank K L :=
    finrank_cyclotomicField_cyclotomicRootField K L _ hcop.symm
  have : IsGalois E M := isGalois_cyclotomicField_cyclotomicRootField K L _
  have hkum := hkummer E M (by rw [hEM]; exact hp)
    (by rw [hEM]; exact exists_isPrimitiveRoot_cyclotomicRootField K L _)
  rw [hEM] at hkum
  obtain ⟨r, hr⟩ := (hfin K L).2
  obtain ⟨s, hs⟩ := (hfin K E).2
  have hdvd : (ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index ∣
      Module.finrank K E ^ s * Module.finrank K L :=
    dvd_trans (ideleClassNorm_range_index_dvd_of_tower K L M (htower K L M))
      (dvd_trans (ideleClassNorm_range_index_dvd_mul_of_tower K E M (htower K E M))
        (mul_dvd_mul hs hkum))
  have hcop' : ((ideleClassNorm (K := K) (L := L)).toMonoidHom.range.index).Coprime
      (Module.finrank K E ^ s) :=
    Nat.Coprime.coprime_dvd_left hr (hcop.pow r s)
  exact hcop'.dvd_of_dvd_mul_left hdvd

end Langlands.Global.AdelicFunctoriality
