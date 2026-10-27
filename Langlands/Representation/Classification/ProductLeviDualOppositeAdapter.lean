import Langlands.Representation.Classification.MaximalConeAssembly
import Langlands.Representation.Exponents.DualEigenfunctionalExistence
import Langlands.Representation.Induction.OppositeProductReversalProof
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.Classification.ParabolicConeUniquenessProof

/-!
# The dual-opposite form of product-Levi tempered sufficiency

The upper generalized-exponent form of tempered sufficiency on a product Levi
implies its opposite dual-eigenfunctional form. Conjugation by the blockwise
reversal matrices identifies the upper Jacquet quotient of a refinement with
the opposite Jacquet quotient of the reversed refinement. A generalized
eigencharacter of the upper quotient is then the eigencharacter of a nonzero
dual eigenfunctional of the opposite quotient, whose nonpositive prefixes
bound the character on the monotone chamber by summation by parts.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators NNReal

universe u uF uV

namespace GeneralLinear

variable {R : Type u} [CommRing R]

/-- Relabelling coordinates fixes scalar matrices. -/
theorem reindex_scalar {m m' : ℕ} (e : Fin m ≃ Fin m') (a : Rˣ) :
    reindex (R := R) e (scalar a) = scalar a := by
  apply Units.ext
  ext x y
  simp [reindex, Matrix.scalar_apply, Matrix.diagonal_apply]

end GeneralLinear

namespace GeneralLinear.BlockShape

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

/-- The block reversal matrix conjugates block scalars of the reversed shape to
block scalars of the original shape with reversed labels. -/
theorem reverseMatrix_conj_blockScalar (b : Fin B.length → Rˣ) :
    MulAut.conj (B.reverseMatrix R) (B.reverse.blockScalar R b) =
      B.blockScalar R (fun k => b k.rev) := by
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, c⟩, rfl⟩ := B.indexEquiv.surjective y
  obtain ⟨i, rfl⟩ := Fin.rev_surjective i
  obtain ⟨j, rfl⟩ := Fin.rev_surjective j
  change MulAut.conj (B.reverseMatrix R) (B.reverse.blockScalar R b) (B.index i.rev a)
      (B.index j.rev c) = B.blockScalar R (fun k => b k.rev) (B.index i.rev a) (B.index j.rev c)
  rw [reverseMatrix_conjugate_entry]
  by_cases hij : i = j
  · subst hij
    refine (B.reverse.blockScalar_apply_same R b i a c).trans ?_
    rw [B.blockScalar_apply_same R _ i.rev a c]
    simp only [Fin.rev_rev]
    rfl
  · rw [B.reverse.blockScalar_apply_ne R b a c hij,
      B.blockScalar_apply_ne R _ a c (fun h => hij (Fin.rev_injective h))]

end GeneralLinear.BlockShape

namespace Geometric

variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Flattened block scalars have block scalar inner components. -/
theorem flattenedLeviProductEquiv_blockScalarLevi (c : Fin (B.flatten S).length → Rˣ)
    (i : Fin B.length) :
    flattenedLeviProductEquiv R B S ((B.flatten S).blockScalarLevi R c) i =
      (S i).blockScalarLevi R (fun j => c (B.flattenBlockEquiv S ⟨i, j⟩)) := by
  funext j
  rw [flattenedLeviProductEquiv_apply]
  exact GeneralLinear.reindex_scalar _ _

/-- The outer components of flattened block scalars are inner block scalars. -/
theorem flattenedLeviEquiv_blockScalarLevi_apply (c : Fin (B.flatten S).length → Rˣ)
    (i : Fin B.length) :
    (flattenedLeviEquiv R B S ((B.flatten S).blockScalarLevi R c)).val i =
      (S i).blockScalar R (fun j => c (B.flattenBlockEquiv S ⟨i, j⟩)) := by
  change (S i).leviEmbedding R (flattenedLeviProductEquiv R B S _ i) = _
  rw [flattenedLeviProductEquiv_blockScalarLevi]
  rfl

end Geometric

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)

/-- The inner blocks of a flattened element are its nested product coordinates. -/
theorem refinedLeviBlock_flattenedLeviEquiv (m : (B.flatten S).Levi F.Carrier)
    (i : Fin B.length) :
    refinedLeviBlock B S i (flattenedLeviEquiv F.Carrier B S m) =
      flattenedLeviProductEquiv F.Carrier B S m i := by
  change (refinedLeviEquiv F.Carrier B S).symm
    (refinedLeviEquiv F.Carrier B S (flattenedLeviProductEquiv F.Carrier B S m)) i = _
  rw [MulEquiv.symm_apply_apply]

end PadicField.TopologicalData

namespace Jacquet

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Translation by `g` between coinvariant quotients, when conjugation by `g`
carries the first subgroup into the second. -/
def conjTranslate (ρ : Representation ℂ G V) {N₁ N₂ : Subgroup G} (g : G)
    (h : ∀ u ∈ N₁, g * u * g⁻¹ ∈ N₂) : Coinvariants ρ N₁ →ₗ[ℂ] Coinvariants ρ N₂ :=
  lift ρ N₁ (mk ρ N₂ ∘ₗ ρ g) fun u => by
    refine LinearMap.ext fun v => ?_
    change mk ρ N₂ (ρ g (ρ u v)) = mk ρ N₂ (ρ g v)
    have hv : ρ g (ρ u v) = ρ (g * u * g⁻¹) (ρ g v) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel_right]
    rw [hv]
    exact mk_apply_subgroup ρ N₂ ⟨_, h u u.property⟩ (ρ g v)

@[simp] theorem conjTranslate_mk (ρ : Representation ℂ G V) {N₁ N₂ : Subgroup G} (g : G)
    (h : ∀ u ∈ N₁, g * u * g⁻¹ ∈ N₂) (v : V) :
    conjTranslate ρ g h (mk ρ N₁ v) = mk ρ N₂ (ρ g v) := rfl

/-- Translation by `g` undoes translation by `g⁻¹`. -/
theorem conjTranslate_conjTranslate_inv (ρ : Representation ℂ G V) {N₁ N₂ : Subgroup G}
    (g : G) (h₁ : ∀ u ∈ N₁, g * u * g⁻¹ ∈ N₂) (h₂ : ∀ u ∈ N₂, g⁻¹ * u * g⁻¹⁻¹ ∈ N₁)
    (x : Coinvariants ρ N₂) :
    conjTranslate ρ g h₁ (conjTranslate ρ g⁻¹ h₂ x) = x := by
  obtain ⟨v, rfl⟩ := mk_surjective ρ N₂ x
  change mk ρ N₂ (ρ g (ρ g⁻¹ v)) = mk ρ N₂ v
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end Jacquet

namespace ProductLeviDualOpposite

section Linear

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

/-- An intertwining linear map intertwines the powers of the defect operators. -/
theorem map_pow_sub_smul (L : M₁ →ₗ[ℂ] M₂) {A : Module.End ℂ M₁} {B : Module.End ℂ M₂}
    (h : ∀ x, L (A x) = B (L x)) (c : ℂ) (k : ℕ) (x : M₁) :
    L (((A - c • 1) ^ k) x) = ((B - c • 1) ^ k) (L x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    congr 1
    simp [h]

end Linear

section Abel

/-- Summation by parts for a nonnegative antitone vector. -/
theorem sum_mul_nonpos_of_antitone_of_nonneg : ∀ (m : ℕ) (t y : Fin m → ℝ), Antitone y →
    (∀ k, 0 ≤ y k) → (∀ i, ∑ k ∈ Finset.univ.filter (fun k => k ≤ i), t k ≤ 0) →
    ∑ k, t k * y k ≤ 0
  | 0, _, _, _, _, _ => by simp
  | m + 1, t, y, hy, hy0, ht => by
    have h1 : ∑ k, t k * y k =
        ∑ k, t k * (y k - y (Fin.last m)) + y (Fin.last m) * ∑ k, t k := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : ∑ k, t k * (y k - y (Fin.last m)) =
        ∑ k : Fin m, t k.castSucc * (y k.castSucc - y (Fin.last m)) := by
      rw [Fin.sum_univ_castSucc, sub_self, mul_zero, add_zero]
    have h3 : ∑ k, t k ≤ 0 := by
      have := ht (Fin.last m)
      rwa [Finset.filter_true_of_mem (fun k _ => Fin.le_last k)] at this
    have h4 : ∑ k : Fin m, t k.castSucc * (y k.castSucc - y (Fin.last m)) ≤ 0 := by
      refine sum_mul_nonpos_of_antitone_of_nonneg m _ _ ?_ ?_ ?_
      · intro a b hab
        exact sub_le_sub_right (hy (Fin.castSucc_le_castSucc_iff.mpr hab)) _
      · intro k
        exact sub_nonneg.mpr (hy (Fin.le_last _))
      · intro i
        have := ht i.castSucc
        have hl : ¬ Fin.last m ≤ i.castSucc := not_le.mpr (Fin.castSucc_lt_last i)
        rw [Finset.sum_filter, Fin.sum_univ_castSucc] at this
        rw [Finset.sum_filter]
        simpa [hl] using this
    rw [h1, h2]
    have h5 := mul_nonpos_of_nonneg_of_nonpos (hy0 (Fin.last m)) h3
    linarith

end Abel

section Reversal

variable {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)

/-- Reverse the order of the inner blocks in every outer block. -/
def reverseRefinement : BlockRefinement C := fun j => (D j).reverse

@[simp] theorem reverseRefinement_apply (j : Fin C.length) :
    reverseRefinement C D j = (D j).reverse := rfl

/-- The flattened labels of the reversed refinement, sent to the flattened
labels of `D` with reversed inner position. -/
def reverseLabel :
    Fin (C.flatten (reverseRefinement C D)).length ≃ Fin (C.flatten D).length :=
  (C.flattenBlockEquiv (reverseRefinement C D)).symm.trans
    ((Equiv.sigmaCongrRight fun j => (Fin.revPerm : Equiv.Perm (Fin (D j).length))).trans
      (C.flattenBlockEquiv D))

theorem reverseLabel_apply (j : Fin C.length) (i : Fin (reverseRefinement C D j).length) :
    reverseLabel C D (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, i⟩) =
      C.flattenBlockEquiv D ⟨j, Fin.rev (n := (D j).length) i⟩ :=
  congrArg (fun x : (k : Fin C.length) × Fin (D k).length =>
      C.flattenBlockEquiv D
        (Equiv.sigmaCongrRight (fun k => (Fin.revPerm : Equiv.Perm (Fin (D k).length))) x))
    ((C.flattenBlockEquiv (reverseRefinement C D)).symm_apply_apply ⟨j, i⟩)

theorem reverseLabel_symm_apply (j : Fin C.length) (i : Fin (D j).length) :
    (reverseLabel C D).symm (C.flattenBlockEquiv D ⟨j, i⟩) =
      C.flattenBlockEquiv (reverseRefinement C D)
        ⟨j, Fin.rev (n := (reverseRefinement C D j).length) i⟩ := by
  rw [Equiv.symm_apply_eq, reverseLabel_apply]
  exact congrArg (fun x => C.flattenBlockEquiv D ⟨j, x⟩) (Fin.rev_rev i).symm

variable (R : Type u) [CommRing R]

/-- The blockwise reversal matrices in the outer product Levi. -/
def reverseWeyl : C.Levi R := fun j => (D j).reverseMatrix R

/-- Conjugation by the blockwise reversal carries the opposite radical of the
reversed refinement onto the upper radical of `D`. -/
theorem conj_mem_refinedUnipotent_iff (g : C.Levi R) :
    reverseWeyl C D R * g * (reverseWeyl C D R)⁻¹ ∈ refinedUnipotent R C D ↔
      g ∈ refinedOppositeUnipotent R C (reverseRefinement C D) := by
  rw [mem_refinedUnipotent, mem_refinedOppositeUnipotent]
  refine forall_congr' fun j => ?_
  exact (D j).reverseMatrix_conj_mem_unipotentSubgroup_iff R (g j)

/-- Conjugating flattened block scalars of the reversed refinement by the
reversal gives flattened block scalars of `D` with relabelled entries. -/
theorem reverseWeyl_conj_blockScalar
    (c : Fin (C.flatten (reverseRefinement C D)).length → Rˣ) :
    reverseWeyl C D R * (flattenedLeviEquiv R C (reverseRefinement C D)
        ((C.flatten (reverseRefinement C D)).blockScalarLevi R c)).val *
        (reverseWeyl C D R)⁻¹ =
      (flattenedLeviEquiv R C D
        ((C.flatten D).blockScalarLevi R (c ∘ (reverseLabel C D).symm))).val := by
  funext j
  simp only [Pi.mul_apply, Pi.inv_apply, flattenedLeviEquiv_blockScalarLevi_apply]
  rw [← MulAut.conj_apply]
  refine ((D j).reverseMatrix_conj_blockScalar R _).trans ?_
  congr 1
  funext k
  simp only [Function.comp_apply, reverseLabel_symm_apply]
  rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (C.Levi R) V)

/-- Translation by the inverse reversal, from the upper quotient of `D` to the
opposite quotient of the reversed refinement. -/
def toOpposite :
    RefinedJacquetModule C D ρ →ₗ[ℂ] RefinedOppositeJacquetModule C (reverseRefinement C D) ρ :=
  Jacquet.conjTranslate ρ (reverseWeyl C D R)⁻¹ fun u hu => by
    rw [← conj_mem_refinedUnipotent_iff]
    have h : reverseWeyl C D R * ((reverseWeyl C D R)⁻¹ * u * (reverseWeyl C D R)⁻¹⁻¹) *
        (reverseWeyl C D R)⁻¹ = u := by group
    rw [h]
    exact hu

/-- Translation by the reversal, inverse to `toOpposite`. -/
def fromOpposite :
    RefinedOppositeJacquetModule C (reverseRefinement C D) ρ →ₗ[ℂ] RefinedJacquetModule C D ρ :=
  Jacquet.conjTranslate ρ (reverseWeyl C D R) fun u hu =>
    (conj_mem_refinedUnipotent_iff C D R u).mpr hu

theorem toOpposite_mk (v : V) :
    toOpposite C D R ρ (refinedJacquetMk C D ρ v) =
      refinedOppositeJacquetMk C (reverseRefinement C D) ρ (ρ (reverseWeyl C D R)⁻¹ v) := rfl

theorem fromOpposite_toOpposite (x : RefinedJacquetModule C D ρ) :
    fromOpposite C D R ρ (toOpposite C D R ρ x) = x :=
  Jacquet.conjTranslate_conjTranslate_inv ρ _ _ _ x

end Reversal

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)

/-- The refined modulus of the reversed refinement on its flattened block
scalars is the inverse refined modulus of `D` on the relabelled scalars. -/
theorem refinedLeviModulus_reverse
    (c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ) :
    T.refinedLeviModulus C (reverseRefinement C D)
        (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)
          ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier c)) =
      (T.refinedLeviModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (c ∘ (reverseLabel C D).symm))))⁻¹ := by
  rw [T.refinedLeviModulus_apply, T.refinedLeviModulus_apply, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [PadicField.TopologicalData.refinedLeviBlock_flattenedLeviEquiv,
    PadicField.TopologicalData.refinedLeviBlock_flattenedLeviEquiv,
    flattenedLeviProductEquiv_blockScalarLevi, flattenedLeviProductEquiv_blockScalarLevi,
    ← T.leviModulus_reverse (D j)]
  show T.leviModulus (D j).reverse _ = T.leviModulus (D j).reverse _
  congr 1
  funext i
  simp only [BlockShape.blockScalarLevi_apply, Function.comp_apply, reverseLabel_symm_apply]
  exact congrArg (fun x => GeneralLinear.scalar
    (c (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, x⟩))) (Fin.rev_rev i).symm

/-- The positive half modulus of the reversed refinement is the inverse half
modulus of `D` on the relabelled scalars. -/
theorem refinedLeviHalfModulus_reverse
    (c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ) :
    (T.refinedLeviHalfModulus C (reverseRefinement C D)
        (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)
          ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier c)) : ℂ) =
      (T.refinedLeviInverseHalfModulus C D (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (c ∘ (reverseLabel C D).symm))) : ℂ) := by
  rw [T.refinedLeviHalfModulus_apply, T.refinedLeviInverseHalfModulus_apply,
    refinedLeviModulus_reverse, Units.val_inv_eq_inv_val, NNReal.sqrt_inv, NNReal.coe_inv,
    Complex.ofReal_inv]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (C.Levi F.Carrier) V)

/-- The inverse reversal intertwines the upper action of relabelled block
scalars with the opposite action of the reversed refinement. -/
theorem toOpposite_normalizedRefinedJacquet
    (c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ)
    (x : RefinedJacquetModule C D ρ) :
    toOpposite C D F.Carrier ρ (T.normalizedRefinedJacquet C D ρ
        (flattenedLeviEquiv F.Carrier C D
          ((C.flatten D).blockScalarLevi F.Carrier (c ∘ (reverseLabel C D).symm))) x) =
      T.normalizedRefinedOppositeJacquet C (reverseRefinement C D) ρ
        (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)
          ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier c))
        (toOpposite C D F.Carrier ρ x) := by
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ (refinedUnipotent F.Carrier C D) x
  have hw : ∀ (g h : C.Levi F.Carrier) (u : V), ρ g (ρ h u) = ρ (g * h) u := fun g h u => by
    rw [map_mul, Module.End.mul_apply]
  rw [T.normalizedRefinedJacquet_mk, map_smul, toOpposite_mk, toOpposite_mk,
    T.normalizedRefinedOppositeJacquet_mk, refinedLeviHalfModulus_reverse,
    ← reverseWeyl_conj_blockScalar, hw, hw]
  congr 3
  group

/-- A generalized eigencharacter of the upper quotient of `D` on flattened
block scalars gives, after relabelling, a generalized eigencharacter of the
opposite quotient of the reversed refinement. -/
theorem isGeneralizedEigencharacter_reverse
    {ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ}
    (hψ : IsGeneralizedEigencharacter ((T.normalizedRefinedJacquet C D ρ).comp
      ((flattenedLeviEquiv F.Carrier C D).toMonoidHom.comp
        ((C.flatten D).blockScalarLevi F.Carrier))) ψ) :
    IsGeneralizedEigencharacter
      (((T.normalizedRefinedOppositeJacquet C (reverseRefinement C D) ρ).comp
        (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)).toMonoidHom).comp
          ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier))
      (ψ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm)) := by
  obtain ⟨k, y, hy0, hy⟩ := (isGeneralizedEigencharacter_iff _ _).mp hψ
  refine (isGeneralizedEigencharacter_iff _ _).mpr ⟨k, toOpposite C D F.Carrier ρ y, ?_, ?_⟩
  · intro h0
    apply hy0
    rw [← fromOpposite_toOpposite C D F.Carrier ρ y, h0, map_zero]
  · intro c
    have hy' : (((T.normalizedRefinedJacquet C D ρ (flattenedLeviEquiv F.Carrier C D
        ((C.flatten D).blockScalarLevi F.Carrier (c ∘ (reverseLabel C D).symm)))) -
        (ψ (c ∘ (reverseLabel C D).symm) : ℂ) • 1) ^ k) y = 0 := hy _
    have key := map_pow_sub_smul (toOpposite C D F.Carrier ρ)
      (fun x => toOpposite_normalizedRefinedJacquet T C D ρ c x)
      (ψ (c ∘ (reverseLabel C D).symm) : ℂ) k y
    rw [hy', map_zero] at key
    exact key.symm

end Padic

end ProductLeviDualOpposite

open ProductLeviDualOpposite in
/-- The upper generalized-exponent form of product-Levi tempered sufficiency
implies its opposite dual-eigenfunctional form. -/
theorem glProductLeviDualOppositeTemperedSufficiency_of_core
    (h : GLProductLeviTemperedExponentSufficiencyStatement.{uF, uV}) :
    GLProductLeviDualOppositeTemperedSufficiencyStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn C S ω hirr hadm hω hunit hdual
  refine h p F T n hn C S ω hirr hadm hω hunit ?_
  intro D ψ hψ hgen a ha
  let := T.moduleTopology
  let : IsTopologicalRing F.Carrier := IsModuleTopology.isTopologicalRing (Padic p) F.Carrier
  have : IsTopologicalGroup ((C.flatten (reverseRefinement C D)).Levi F.Carrier) :=
    T.leviTopologicalGroup _
  have hgen' := isGeneralizedEigencharacter_reverse T C D S.ρ hgen
  have hadm' : IsAdmissible ((T.normalizedRefinedOppositeJacquet C (reverseRefinement C D)
      S.ρ).comp (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)).toMonoidHom) :=
    isAdmissible_comp_continuousMulEquiv _
      (flattenedLeviEquivContinuous F.Carrier C (reverseRefinement C D))
      (Parabolic.isAdmissible_normalizedRefinedOppositeJacquet F T C (reverseRefinement C D)
        _ S.ρ hadm)
  have hcof : CompactOpenCofinal ((C.flatten (reverseRefinement C D)).Levi F.Carrier) :=
    fun K =>
      let L := T.leviCompactOpen (C.flatten (reverseRefinement C D)) K
        (K.isOpen.mem_nhds K.one_mem)
      ⟨L.1, L.2.1, fun x hx => L.2.2 hx⟩
  obtain ⟨φ, hφ, heig⟩ :=
    DualEigenfunctional.exists_dualEigenfunctional_of_isGeneralizedEigencharacter _ hadm' hcof
      ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier)
      (fun a => (C.flatten (reverseRefinement C D)).blockScalarLevi_mem_center F.Carrier a)
      _ hgen'
  have hcont : Continuous (MaximalConeAssembly.precomp (M := F.Carrierˣ)
      (reverseLabel C D).symm) := by
    change Continuous fun c : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ =>
      fun k => c ((reverseLabel C D).symm k)
    exact continuous_pi fun k => continuous_apply _
  have hψ' : IsOpen ((ψ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm)).ker :
      Set (Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ)) :=
    hψ.preimage hcont
  obtain ⟨s, hs⟩ := T.exists_isRealPartOf _ hψ'
  have heig' : ∀ (b : Fin (C.flatten (reverseRefinement C D)).length → F.Carrierˣ) (v : S),
      φ (T.normalizedRefinedOppositeJacquet C (reverseRefinement C D) S.ρ
          (flattenedLeviEquiv F.Carrier C (reverseRefinement C D)
            ((C.flatten (reverseRefinement C D)).blockScalarLevi F.Carrier b))
          (refinedOppositeJacquetMk C (reverseRefinement C D) S.ρ v)) =
        ((ψ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm)) b : ℂ) *
          φ (refinedOppositeJacquetMk C (reverseRefinement C D) S.ρ v) :=
    fun b v => heig b _
  have hpre := hdual (reverseRefinement C D) _ s φ hψ' hφ heig' hs
  have hzero : ∀ j, ∑ i : Fin (D j).length,
      s (C.flattenBlockEquiv (reverseRefinement C D) ⟨j, i⟩) = 0 := by
    intro j
    have := T.sum_fibre_eq_zero_of_unitary C (reverseRefinement C D) S.ρ hω hunit hφ heig' hs j
    rwa [BlockShape.sum_filter_flattenOuter] at this
  have hpos : ∀ k, 0 < T.normalizedAbs (a k : F.Carrier) := fun k =>
    T.normalizedAbs_pos (a k).ne_zero
  have hψa : ψ a = (ψ.comp (MaximalConeAssembly.precomp (reverseLabel C D).symm))
      (a ∘ reverseLabel C D) := by
    change ψ a = ψ ((a ∘ reverseLabel C D) ∘ (reverseLabel C D).symm)
    congr 1
    funext k
    simp
  rw [hψa, hs]
  have hexp : ∏ b, T.normalizedAbs (((a ∘ reverseLabel C D) b : F.Carrierˣ) : F.Carrier) ^ s b =
      Real.exp (∑ b, s b * Real.log (T.normalizedAbs (a (reverseLabel C D b) : F.Carrier))) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Function.comp_apply, Real.rpow_def_of_pos (hpos _), mul_comm]
  rw [hexp, Real.exp_le_one_iff, ← (C.flattenBlockEquiv (reverseRefinement C D)).sum_comp,
    Fintype.sum_sigma]
  refine Finset.sum_nonpos fun j _ => ?_
  simp only [reverseLabel_apply]
  exact ParabolicConeUniqueness.sum_mul_nonpos_of_antitone _ _
    (fun i i' hii' => Real.log_le_log (hpos _) (ha j (Fin.rev_le_rev.mpr hii')))
    (hpre j) (hzero j)

end Langlands
