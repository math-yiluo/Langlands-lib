import Langlands.GroupScheme.Dynamic.StarLeviIwasawa
import Langlands.Group.TwoPowerUnitaryConjugation
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Internal two-power unitarization of cocharacters -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.LinearAlgebra

variable {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n] {idx : Type*} [DecidableEq idx]

/-- A normal matrix need only separate the finite support of a complete
projector family in order to make all projectors Hermitian. -/
theorem hermitian_projectors_of_normal_separating_support
    (F : idx → Matrix n n 𝕜)
    (hF : ∀ a b, F a * F b = if a = b then F a else 0)
    (s : Finset idx) (hs : ∑ a ∈ s, F a = 1)
    (hzero : ∀ a ∉ s, F a = 0)
    (A : Matrix n n 𝕜) [IsStarNormal A] (c : idx → 𝕜)
    (hc : Set.InjOn c (s : Set idx)) (hA : ∀ a, A * F a = c a • F a) :
    ∀ a, (F a).IsHermitian := by
  have hsub : ∀ a : s, (F a).IsHermitian := by
    refine hermitian_projectors_of_normal_separating_action
      (fun a : s => F a) ?_ Finset.univ ?_ A (fun a : s => c a) ?_ ?_
    · intro a b
      simpa only [Subtype.ext_iff] using hF a b
    · simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hs
    · intro a b h
      exact Subtype.ext (hc a.property b.property h)
    · intro a
      exact hA a
  intro a
  by_cases ha : a ∈ s
  · exact hsub ⟨a, ha⟩
  · rw [hzero a ha]
    exact Matrix.isHermitian_zero

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme.GeneralLinear

variable {𝕜 : Type u} [RCLike 𝕜]

/-- A sufficiently high primitive root of two-power order separates any given
finite set of integer exponents. -/
theorem exists_two_power_unit_separating [IsAlgClosed 𝕜] (s : Finset ℤ) :
    ∃ (r : ℕ) (t : 𝕜ˣ), t ^ (2 ^ r) = 1 ∧
      Set.InjOn (fun a : ℤ => (t : 𝕜) ^ a) (s : Set ℤ) := by
  let N : ℕ := s.sup Int.natAbs
  let r : ℕ := 2 * N + 1
  have hlarge : 2 * N < 2 ^ r :=
    lt_trans (by change 2 * N < 2 * N + 1; omega) (r.lt_two_pow_self)
  have hn : 2 ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  let : NeZero ((2 ^ r : ℕ) : 𝕜) := ⟨by exact_mod_cast hn⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot 𝕜 (2 ^ r)
  let t : 𝕜ˣ := (hζ.isUnit hn).unit
  have ht : IsPrimitiveRoot t (2 ^ r) := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa only [t, IsUnit.unit_spec] using hζ
  refine ⟨r, t, ht.pow_eq_one, ?_⟩
  intro a ha b hb hab
  have hab' : t ^ a = t ^ b := by
    apply Units.ext
    simpa only [Units.val_zpow_eq_zpow_val] using hab
  have hdvd : ((2 ^ r : ℕ) : ℤ) ∣ a - b := by
    apply (ht.zpow_eq_one_iff_dvd (a - b)).mp
    rw [zpow_sub, hab', mul_inv_cancel]
  have haN : a.natAbs ≤ N := Finset.le_sup ha
  have hbN : b.natAbs ≤ N := Finset.le_sup hb
  have hbound : |a - b| < ((2 ^ r : ℕ) : ℤ) := by
    have habs : |a - b| ≤ |a| + |b| := abs_sub a b
    rw [← Int.natCast_natAbs a, ← Int.natCast_natAbs b] at habs
    exact lt_of_le_of_lt habs (by exact_mod_cast
      (lt_of_le_of_lt (Nat.add_le_add haN hbN) (by simpa [two_mul] using hlarge)))
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd hbound)

variable {n : Type} [Fintype n] [DecidableEq n]
  (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ groupScheme n (CommRingCat.of 𝕜))

/-- Normality at a scalar unit separating the actual finite Laurent support
makes every weight projector Hermitian. -/
theorem hasHermitianWeightProjectors_of_normal_separating_unit
    (t : 𝕜ˣ)
    (ht : Set.InjOn (fun a : ℤ => (t : 𝕜) ^ a)
      (cocharacterWeightSupport χ : Set ℤ))
    [IsStarNormal (cocharacterUnitsHom χ 𝕜 t : Matrix n n 𝕜)] :
    HasHermitianWeightProjectors χ := by
  apply Langlands.LinearAlgebra.hermitian_projectors_of_normal_separating_support
    (weightProjector χ) (fun a b => by
      rw [weightProjector_mul]
      split_ifs with hab
      · subst b; rfl
      · rfl)
    (cocharacterWeightSupport χ) (sum_weightProjector χ)
    (fun _ ha => weightProjector_eq_zero χ ha)
    (cocharacterUnitsHom χ 𝕜 t : Matrix n n 𝕜)
    (fun a => (t : 𝕜) ^ a) ht
  exact cocharacterUnitsHom_mul_weightProjector χ t

/-- A base-matrix conjugation conjugates every actual Laurent weight projector. -/
theorem weightProjector_innerIso_baseOfMatrix (g : GL n 𝕜) (a : ℤ) :
    weightProjector
      (χ ≫ (innerIso (groupScheme n (CommRingCat.of 𝕜))
        (baseOfMatrix (CommRingCat.of 𝕜) g)).hom) a =
      g.val * weightProjector χ a * (g⁻¹).val := by
  ext i j
  rw [weightProjector_apply, weightMatrix_innerIso, ← map_inv]
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.map_apply, Matrix.mul_apply,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
    AddMonoidAlgebra.coeff_mul_single_zero, AddMonoidAlgebra.coeff_single_zero_mul,
    AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  rfl

/-- Conjugation cannot introduce a new Laurent weight. -/
theorem cocharacterWeightSupport_innerIso_subset (g : GL n 𝕜) :
    cocharacterWeightSupport
      (χ ≫ (innerIso (groupScheme n (CommRingCat.of 𝕜))
        (baseOfMatrix (CommRingCat.of 𝕜) g)).hom) ⊆ cocharacterWeightSupport χ := by
  intro a ha
  by_contra h
  have hz := weightProjector_eq_zero χ h
  have hz' : weightProjector
      (χ ≫ (innerIso (groupScheme n (CommRingCat.of 𝕜))
        (baseOfMatrix (CommRingCat.of 𝕜) g)).hom) a = 0 := by
    rw [weightProjector_innerIso_baseOfMatrix, hz, Matrix.mul_zero, Matrix.zero_mul]
  simp only [cocharacterWeightSupport, Finset.mem_biUnion, Finset.mem_univ,
    true_and] at ha
  obtain ⟨⟨i, j⟩, hij⟩ := ha
  have hij' := congrArg (fun A : Matrix n n 𝕜 => A i j) hz'
  exact (Finsupp.mem_support_iff.mp hij) hij'

/-- The matrix of a conjugated cocharacter at a base-field scalar unit is
conjugated by that same base matrix. -/
theorem cocharacterUnitsHom_innerIso_baseOfMatrix (g : GL n 𝕜) (t : 𝕜ˣ) :
    cocharacterUnitsHom
      (χ ≫ (innerIso (groupScheme n (CommRingCat.of 𝕜))
        (baseOfMatrix (CommRingCat.of 𝕜) g)).hom) 𝕜 t =
      g * cocharacterUnitsHom χ 𝕜 t * g⁻¹ := by
  rw [cocharacterUnitsHom_apply, Grp.comp_hom_hom, ← Category.assoc,
    comp_innerIso_hom, map_mul, map_mul, map_inv,
    affinePointsEquiv_constantPoint_baseOfMatrix]
  simp only [Algebra.algebraMap_self, Matrix.GeneralLinearGroup.map_id,
    MonoidHom.id_apply]
  rfl

/-- The actual cocharacter has Hermitian Laurent weights after conjugation
by an element of the specified matrix subgroup. -/
def HasInternalHermitianConjugate (H : Subgroup (GL n 𝕜)) : Prop :=
  ∃ g : GL n 𝕜, g ∈ H ∧ HasHermitianWeightProjectors
    (χ ≫ (innerIso (groupScheme n (CommRingCat.of 𝕜))
      (baseOfMatrix (CommRingCat.of 𝕜) g)).hom)

/-- Over algebraically closed `RCLike` coefficients, internal two-power
unitarization makes the weights of an actual cocharacter Hermitian. -/
theorem hasInternalHermitianConjugate [IsAlgClosed 𝕜]
    (H : Subgroup (GL n 𝕜))
    (hH : Langlands.Group.AlgebraicMatrixPowers.IsPolynomiallyDefined H)
    (hstar : ∀ g ∈ H, star g ∈ H)
    (hχ : ∀ t : 𝕜ˣ, cocharacterUnitsHom χ 𝕜 t ∈ H) :
    HasInternalHermitianConjugate χ H := by
  obtain ⟨r, t, ht, hsep⟩ := exists_two_power_unit_separating
    (𝕜 := 𝕜) (cocharacterWeightSupport χ)
  have hpow : (cocharacterUnitsHom χ 𝕜 t) ^ (2 ^ r) = 1 := by
    rw [← map_pow, ht, map_one]
  obtain ⟨g, hg, hgu⟩ :=
    Langlands.Group.TwoPowerUnitaryConjugation.exists_conjugator_of_two_power_eq_one
      H hH hstar r (cocharacterUnitsHom χ 𝕜 t) (hχ t) hpow
  let ψ := χ ≫ (innerIso (groupScheme n (CommRingCat.of 𝕜))
    (baseOfMatrix (CommRingCat.of 𝕜) g)).hom
  have hψu : (cocharacterUnitsHom ψ 𝕜 t : Matrix n n 𝕜) ∈
      Matrix.unitaryGroup n 𝕜 := by
    simpa only [ψ, cocharacterUnitsHom_innerIso_baseOfMatrix] using hgu
  let : IsStarNormal (cocharacterUnitsHom ψ 𝕜 t : Matrix n n 𝕜) :=
    isStarNormal_of_mem_unitary hψu
  refine ⟨g, hg, hasHermitianWeightProjectors_of_normal_separating_unit ψ t ?_⟩
  exact hsep.mono (cocharacterWeightSupport_innerIso_subset χ g)

end Langlands.GroupScheme.GeneralLinear

namespace Langlands.GroupScheme.MatrixRepresentation

variable {𝕜 : Type u} [RCLike 𝕜]
  {G : GroupScheme (Spec (CommRingCat.of 𝕜))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Conjugating by an element of the actual matrix image preserves that image. -/
theorem conjugate_baseOfMatrix_range_eq_of_mem
    (ρ : MatrixRepresentation G n) (g : GL n 𝕜)
    (hg : g ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range) :
    ((ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of 𝕜) g)).affineMatrix
      (CommAlgCat.of 𝕜 𝕜)).range =
        (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range := by
  obtain ⟨z, hz⟩ := hg
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨z * x * z⁻¹, ?_⟩
    rw [map_mul, map_mul, map_inv, hz, conjugate_baseOfMatrix_affineMatrix]
  · rintro ⟨x, rfl⟩
    refine ⟨z⁻¹ * x * z, ?_⟩
    rw [conjugate_baseOfMatrix_affineMatrix, map_mul, map_mul, map_inv, hz]
    group

/-- Internal conjugation gives Hermitian cocharacter weights without changing
the actual star-stable image of a closed representation. -/
theorem exists_internal_conjugate_hermitian [IsAlgClosed 𝕜]
    (ρ : MatrixRepresentation G n) (hρ : IsClosedSubgroup ρ)
    (hstar : ∀ g ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range,
      star g ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range)
    (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ G) :
    ∃ g : GL n 𝕜, g ∈ (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range ∧
      GeneralLinear.HasHermitianWeightProjectors
        (χ ≫ ρ.conjugate (GeneralLinear.baseOfMatrix (CommRingCat.of 𝕜) g)) := by
  let : IsClosedImmersion ρ.hom.hom.left := hρ
  have hχ := GeneralLinear.hasInternalHermitianConjugate (χ ≫ ρ)
    (ρ.affineMatrix (CommAlgCat.of 𝕜 𝕜)).range
    (ρ.affineMatrix_range_isPolynomiallyDefined 𝕜) hstar
    (fun t => ⟨Dynamic.cocharacterPointHom χ (CommAlgCat.of 𝕜 𝕜) t,
      ρ.affineMatrix_cocharacterPointHom_eq_cocharacterUnitsHom χ t⟩)
  obtain ⟨g, hg, hgw⟩ := hχ
  exact ⟨g, hg, by simpa only [MatrixRepresentation.conjugate, Category.assoc] using hgw⟩

end Langlands.GroupScheme.MatrixRepresentation
