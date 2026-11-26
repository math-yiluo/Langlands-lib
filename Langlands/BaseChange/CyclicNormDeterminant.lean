import Langlands.BaseChange.Norm
import Langlands.ClassFieldTheory.Local.UnramifiedNormMembershipProof
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.FieldTheory.Galois.Basic

/-! # Determinants of cyclic matrix norms over fields -/

noncomputable section

namespace Langlands.BaseChange

universe u v

section Field

variable {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {l n : ℕ}

/-- A cyclic algebra which is a field is Galois over the base field. -/
theorem IsCyclicAlgebra.isGalois (h : IsCyclicAlgebra σ l) : IsGalois F E := by
  let : FiniteDimensional F E := h.1
  apply IsGalois.of_fixedField_eq_bot
  refine le_antisymm (fun x hx => ?_) bot_le
  exact IntermediateField.mem_bot.mpr (h.2.2.2.2 x
    ((IntermediateField.mem_fixedField_iff _ _).mp hx σ (Subgroup.mem_top σ)))

/-- A cyclic algebra of degree `l` that is a field is abelian Galois. -/
theorem IsCyclicAlgebra.isAbelianGalois {F : Type u} [Field F] {E : Type v} [Field E]
    [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) :
    IsAbelianGalois F E := by
  let : FiniteDimensional F E := h.1
  let : IsGalois F E := h.isGalois
  have hcard : orderOf σ = Nat.card (E ≃ₐ[F] E) := by
    rw [IsGalois.card_aut_eq_finrank, h.2.1, h.2.2.2.1]
  let : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_orderOf_eq_card σ hcard
  exact IsAbelianGalois.of_isCyclic F E

private theorem prod_pow_apply_eq_norm (h : IsCyclicAlgebra σ l) (x : E) :
    (∏ i : Fin l, (σ ^ (i : ℕ)) x) = algebraMap F E (Algebra.norm F x) := by
  classical
  let : FiniteDimensional F E := h.1
  let : IsGalois F E := h.isGalois
  let f : Fin l → E ≃ₐ[F] E := fun i => σ ^ (i : ℕ)
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (x := σ)
      (show (i : ℕ) < orderOf σ by rw [h.2.2.2.1]; exact i.isLt)
      (show (j : ℕ) < orderOf σ by rw [h.2.2.2.1]; exact j.isLt) hij
  have hcard : Fintype.card (Fin l) = Fintype.card (E ≃ₐ[F] E) := by
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, h.2.1]
  let e := Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩)
  rw [Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_equiv e _ (fun τ => τ x) (fun _ => rfl)

/-- The determinant of the ordered matrix norm is the scalar field norm after
embedding back into the extension. -/
theorem IsCyclicAlgebra.determinant_cyclicNorm (h : IsCyclicAlgebra σ l)
    (δ : GeneralLinear n E) :
    (GeneralLinear.determinant (cyclicNorm σ l δ) : E) =
      algebraMap F E (Algebra.norm F (GeneralLinear.determinant δ : E)) := by
  let det := (Units.coeHom E).comp (GeneralLinear.determinant (n := n))
  have hentry (i : ℕ) : det (entrywiseAut (σ ^ i) n δ) = (σ ^ i) (det δ) := by
    change (Matrix.map (δ : Matrix (Fin n) (Fin n) E)
      ((σ ^ i : E ≃ₐ[F] E) : E →+* E)).det = _
    exact ((σ ^ i : E ≃ₐ[F] E).map_det (δ : Matrix (Fin n) (Fin n) E)).symm
  change det (cyclicNorm σ l δ) = _
  rw [cyclicNorm, map_list_prod, List.map_map]
  change ((List.range l).map (fun i => det (entrywiseAut (σ ^ i) n δ))).prod = _
  simp_rw [hentry]
  have hrange : (List.finRange l).map (fun i : Fin l => (i : ℕ)) = List.range l := by
    simp
  rw [← hrange, List.map_map, ← Fin.prod_univ_def]
  exact prod_pow_apply_eq_norm h (det δ)

/-- Association of matrix elements implies equality of the scalar norm of the
twisted determinant and the base determinant. -/
theorem IsNormAssociated.norm_determinant_eq
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (hδγ : IsNormAssociated σ l δ γ)
    (h : IsCyclicAlgebra σ l) :
    Algebra.norm F (GeneralLinear.determinant δ : E) = (GeneralLinear.determinant γ : F) := by
  obtain ⟨x, hx⟩ := hδγ
  apply (algebraMap F E).injective
  rw [← h.determinant_cyclicNorm δ]
  have hdet := congrArg (fun g : GeneralLinear n E => GeneralLinear.determinant g) hx
  rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul] at hdet
  have he := congrArg (fun a : Eˣ => (a : E)) hdet
  change (GeneralLinear.determinant (cyclicNorm σ l δ) : E) =
    (Matrix.map (γ : Matrix (Fin n) (Fin n) F) (algebraMap F E)).det at he
  exact he.trans ((algebraMap F E).map_det (γ : Matrix (Fin n) (Fin n) F)).symm

end Field

section Unramified

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} {E : PadicField.{v} p}
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l n : ℕ}

/-- The determinant order at an associated base matrix equals the degree times
the determinant order at the twisted matrix. -/
theorem IsNormAssociated.ord_determinant_eq
    {δ : GeneralLinear n E.Carrier} {γ : GeneralLinear n F.Carrier}
    (hδγ : IsNormAssociated σ l δ γ) (h : IsCyclicAlgebra σ l)
    (he : E.canonicalTopologicalData.ramificationIndex =
      F.canonicalTopologicalData.ramificationIndex) :
    F.canonicalTopologicalData.ord (GeneralLinear.determinant γ : F.Carrier) =
      (l : ℤ) * E.canonicalTopologicalData.ord (GeneralLinear.determinant δ : E.Carrier) := by
  let : FiniteDimensional F.Carrier E.Carrier := h.1
  rw [← hδγ.norm_determinant_eq h,
    LocalClassField.ord_relative_norm_of_unramified F E _ _ he.symm, h.2.1]

end Unramified

end Langlands.BaseChange
