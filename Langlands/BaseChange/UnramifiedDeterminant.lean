import Langlands.BaseChange.TwistedPaleyWiener
import Langlands.AllField.Representation.Parabolic.QuotientCompactProof
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlices
import Langlands.AllField.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof
import Langlands.Group.GL.CartanProof
import Langlands.Group.GL.UpperBruhatCells
import Langlands.Representation.RankinSelberg.RankOneMatrixIwasawa
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Finset.NoncommProd
import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Unramified characters of the actual general linear group -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear

universe v w

section Algebraic

variable {E : Type v} [Field E] {n : ℕ}

private theorem map_diagonal_mulSingle_eq {C : Type w} [CommGroup C]
    (ψ : GeneralLinear n E →* C) (i j : Fin n) (a : Eˣ) :
    ψ (Iwasawa.diagonalUnits (Pi.mulSingle i a)) =
      ψ (Iwasawa.diagonalUnits (Pi.mulSingle j a)) := by
  classical
  let p := Equiv.swap i j
  have hp : p i = j := Equiv.swap_apply_left _ _
  have hh : (fun k => Pi.mulSingle (M := fun _ => Eˣ) i a (p⁻¹ k)) = Pi.mulSingle j a := by
    funext k
    have he : p⁻¹ k = i ↔ k = j := by
      change p.symm k = i ↔ k = j
      rw [Equiv.symm_apply_eq, hp]
    by_cases hk : k = j
    · rw [he.mpr hk, hk, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (mt he.mp hk), Pi.mulSingle_eq_of_ne hk]
  have h := GeneralLinear.permutation_mul_diagonalUnits n p (Pi.mulSingle i a)
  rw [hh] at h
  have h' := congrArg ψ h
  simp only [map_mul] at h'
  rw [mul_comm (ψ (permutation n E p))] at h'
  exact mul_right_cancel h'

private theorem map_torus {C : Type w} [CommGroup C]
    (ψ : GeneralLinear n E →* C) (i : Fin n) (a : Eˣ) (lam : Fin n → ℤ) :
    ψ (Iwasawa.torus a lam) = ψ (Iwasawa.diagonalUnits (Pi.mulSingle i a)) ^ (∑ j, lam j) := by
  classical
  let d : Fin n → Eˣ := fun j => a ^ lam j
  let φ := ψ.comp Iwasawa.diagonalUnits
  have hsum (s : Finset (Fin n)) (z : C) : z ^ (∑ j ∈ s, lam j) = ∏ j ∈ s, z ^ lam j := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hjs ih => rw [Finset.sum_insert hjs, Finset.prod_insert hjs, zpow_add, ih]
  change φ d = _
  rw [← Finset.univ_prod_mulSingle d, map_prod, hsum]
  refine Finset.prod_congr rfl fun j _ => ?_
  change φ (Pi.mulSingle j (a ^ lam j)) = _
  rw [Pi.mulSingle_zpow, map_zpow]
  exact congrArg (fun x : C => x ^ lam j) (map_diagonal_mulSingle_eq ψ j i a)

end Algebraic

section Local

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/-- The normalized additive determinant order, in multiplicative notation. -/
def determinantOrderHom (n : ℕ) : GeneralLinear n E →* Multiplicative ℤ :=
  (LocalFieldData.ofInstances E).ordUnits.comp determinant

/-- Every compact subgroup consists of elements of determinant order zero. -/
theorem determinantOrderHom_eq_one_of_mem_compact (n : ℕ)
    (K : Subgroup (GeneralLinear n E)) (hK : IsCompact (K : Set (GeneralLinear n E)))
    {k : GeneralLinear n E} (hk : k ∈ K) : determinantOrderHom E n k = 1 := by
  let T := LocalFieldData.ofInstances E
  let f : GeneralLinear n E → ℤ := fun g => (determinantOrderHom E n g).toAdd
  have hcont : Continuous f :=
    (AllField.RankinSelberg.continuous_ord_units T).comp (T.generalLinearDeterminant n).continuous
  let : Finite ↥(f '' (K : Set (GeneralLinear n E))) := (hK.image hcont).finite_of_discrete
  let : Finite (K.map (determinantOrderHom E n)) :=
    Finite.of_injective
      (fun x => (⟨x.1.toAdd, by
        obtain ⟨y, hy, hyx⟩ := x.2
        exact ⟨y, hy, congrArg Multiplicative.toAdd hyx⟩⟩ : ↥(f '' (K : Set (GeneralLinear n E)))))
      (fun _ _ h => Subtype.ext (congrArg Multiplicative.ofAdd (congrArg Subtype.val h)))
  let x : K.map (determinantOrderHom E n) := ⟨_, ⟨k, hk, rfl⟩⟩
  exact ((K.map (determinantOrderHom E n)).subtype.isOfFinOrder (isOfFinOrder_of_finite x)).eq_one'

private theorem determinantOrderHom_diagonal_uniformizer {n : ℕ} (i : Fin n) :
    determinantOrderHom E n
      (Iwasawa.diagonalUnits (Pi.mulSingle i (LocalFieldData.ofInstances E).uniformizerUnit)) =
    Multiplicative.ofAdd 1 := by
  classical
  let T := LocalFieldData.ofInstances E
  change T.ordUnits (Matrix.GeneralLinearGroup.det (Iwasawa.diagonalUnits
    (Pi.mulSingle i T.uniformizerUnit))) = _
  rw [RankinSelberg.RankOneIwasawa.det_diagonalUnits]
  have hd : ∏ j, Pi.mulSingle (M := fun _ => Eˣ) i T.uniformizerUnit j = T.uniformizerUnit := by
    rw [Fintype.prod_eq_single i (fun j hj => Pi.mulSingle_eq_of_ne hj _), Pi.mulSingle_eq_same]
  rw [hd]
  change Multiplicative.ofAdd (T.ord (T.uniformizerUnit : E)) = _
  rw [T.uniformizerUnit_val, T.ord_uniformizer]

/-- In positive rank, a character trivial on every compact subgroup is the determinant-order
character with parameter its value on the diagonal matrix with a uniformizer in one slot. -/
theorem eq_detOrderCharacter_of_isUnramified {n : ℕ} (i : Fin n)
    (ψ : GeneralLinear n E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ) :
    ψ = (zpowersHom ℂˣ (ψ (Iwasawa.diagonalUnits
      (Pi.mulSingle i (LocalFieldData.ofInstances E).uniformizerUnit)))).comp
        (determinantOrderHom E n) := by
  classical
  let T := LocalFieldData.ofInstances E
  let v := ValuativeRel.valuation E
  have hπ : Iwasawa.IsUniformizingElement v T.uniformizerUnit :=
    AllField.Whittaker.SupercuspidalCoinvariantFinitenessProof.isUniformizingElement T
  apply MonoidHom.ext
  intro g
  obtain ⟨lam, _, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_cartan hπ n g
  have hK : IsCompact (Iwasawa.integralRange v n : Set (GeneralLinear n E)) :=
    AllField.Parabolic.isCompact_integralRange T n
  have h₁ := determinantOrderHom_eq_one_of_mem_compact E n (Iwasawa.integralRange v n) hK hk₁
  have h₂ := determinantOrderHom_eq_one_of_mem_compact E n (Iwasawa.integralRange v n) hK hk₂
  simp only [MonoidHom.comp_apply, map_mul, hψ _ hK _ hk₁, hψ _ hK _ hk₂,
    h₁, h₂, map_one, one_mul, mul_one, map_torus ψ i, map_torus (determinantOrderHom E n) i]
  rw [determinantOrderHom_diagonal_uniformizer E i, map_zpow, zpowersHom_apply]
  show _ = (_ ^ (1 : ℤ)) ^ _
  rw [zpow_one]

/-- On `GL_n` of positive rank, unramifiedness is the determinant-unit kernel condition. -/
theorem isUnramifiedCharacter_iff_detOrderKer_le {n : ℕ} (i : Fin n)
    (ψ : GeneralLinear n E →* ℂˣ) :
    IsUnramifiedCharacter ψ ↔ (determinantOrderHom E n).ker ≤ ψ.ker := by
  constructor
  · intro hψ g hg
    have hh := MonoidHom.mem_ker.mp hg
    exact MonoidHom.mem_ker.mpr (by rw [eq_detOrderCharacter_of_isUnramified E i ψ hψ,
      MonoidHom.comp_apply, hh, map_one])
  · intro h K hK k hk
    exact MonoidHom.mem_ker.mp (h (MonoidHom.mem_ker.mpr
      (determinantOrderHom_eq_one_of_mem_compact E n K hK hk)))

/-- There are finitely many unramified characters of positive-rank `GL_n` that are trivial
on the centre. Evaluation at a uniformizer in one diagonal slot embeds them into `μ_n`. -/
theorem finite_unramifiedCharacter_trivialCenter {n : ℕ} (i : Fin n) :
    Finite {ψ : GeneralLinear n E →* ℂˣ // IsUnramifiedCharacter ψ ∧
      Subgroup.center (GeneralLinear n E) ≤ ψ.ker} := by
  classical
  let : NeZero n := ⟨i.pos.ne'⟩
  let T := LocalFieldData.ofInstances E
  let d := Iwasawa.diagonalUnits (Pi.mulSingle i T.uniformizerUnit)
  have hroot (ψ : {ψ : GeneralLinear n E →* ℂˣ // IsUnramifiedCharacter ψ ∧
      Subgroup.center (GeneralLinear n E) ≤ ψ.ker}) : ψ.val d ^ n = 1 := by
    let z := scalar (n := n) T.uniformizerUnit
    have hz : z ∈ Subgroup.center (GeneralLinear n E) := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      exact (Matrix.GeneralLinearGroup.scalar_commute T.uniformizerUnit g).symm
    have h := MonoidHom.mem_ker.mp (ψ.property.2 hz)
    have hzdet : determinantOrderHom E n z = Multiplicative.ofAdd (n : ℤ) := by
      change T.ordUnits (Matrix.GeneralLinearGroup.det
        (Matrix.GeneralLinearGroup.scalar (Fin n) T.uniformizerUnit)) = _
      rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]
      change Multiplicative.ofAdd (T.ord (T.uniformizerUnit : E)) ^ n = _
      rw [T.uniformizerUnit_val, T.ord_uniformizer]
      apply Multiplicative.toAdd.injective
      simp
    rw [eq_detOrderCharacter_of_isUnramified E i ψ.val ψ.property.1,
      MonoidHom.comp_apply, hzdet] at h
    exact h
  refine Finite.of_injective (fun ψ => (⟨ψ.val d, (mem_rootsOfUnity _ _).mpr (hroot ψ)⟩ :
    rootsOfUnity n ℂ)) ?_
  intro ψ φ h
  have hh : ψ.val d = φ.val d := congrArg Subtype.val h
  apply Subtype.ext
  rw [eq_detOrderCharacter_of_isUnramified E i ψ.val ψ.property.1,
    eq_detOrderCharacter_of_isUnramified E i φ.val φ.property.1]
  exact congrArg (fun a : ℂˣ => (zpowersHom ℂˣ a).comp (determinantOrderHom E n)) hh

end Local

section Product

universe uI uM

variable {ι : Type uI} [Fintype ι] [DecidableEq ι] {G : ι → Type uM}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- A character of a finite product is unramified exactly when its restrictions to
all factors are unramified. This applies to the standard Levi products. -/
theorem isUnramifiedCharacter_pi_iff (ψ : (∀ i, G i) →* ℂˣ) :
    IsUnramifiedCharacter ψ ↔
      ∀ i, IsUnramifiedCharacter (ψ.comp (MonoidHom.mulSingle G i)) := by
  constructor
  · intro hψ i K hK k hk
    let f := MonoidHom.mulSingle G i
    have hf : Continuous f := continuous_mulSingle i
    change ψ (f k) = 1
    apply hψ (K.map f)
    · rw [Subgroup.coe_map]
      exact hK.image hf
    · exact ⟨k, hk, rfl⟩
  · intro h K hK k hk
    have h₁ (i : ι) : ψ (Pi.mulSingle i (k i)) = 1 := by
      let f := Pi.evalMonoidHom G i
      apply h i (K.map f)
      · rw [Subgroup.coe_map]
        exact hK.image (continuous_apply i)
      · exact ⟨k, hk, rfl⟩
    calc
      ψ k = ψ (Finset.univ.noncommProd (fun i => Pi.mulSingle i (k i))
          (fun i _ j _ _ => Pi.mulSingle_apply_commute k i j)) :=
        congrArg ψ (Finset.noncommProd_mulSingle k).symm
      _ = ∏ i, ψ (Pi.mulSingle i (k i)) :=
        (Finset.map_noncommProd _ _ _ ψ).trans (Finset.noncommProd_eq_prod _ _)
      _ = 1 := Finset.prod_eq_one (fun i _ => h₁ i)

end Product

end Langlands.BaseChange
