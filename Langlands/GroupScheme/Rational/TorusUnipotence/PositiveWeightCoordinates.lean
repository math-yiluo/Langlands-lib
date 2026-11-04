import Langlands.CommutativeAlgebra.WeightGradedFormallySmoothPolynomial
import Langlands.GroupScheme.Rational.TorusUnipotence.CoordinateGlue

/-! # Torus-eigen polynomial coordinates on groups with positive weights

For a smooth affine group `H` of finite type over a field with an action of a split torus `S`
whose augmentation weights all pair positively with a cocharacter `ν`, the coordinate algebra
of `H` is a polynomial algebra on `S`-eigenfunctions, and the group law is triangular in these
coordinates. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct MvPolynomial Finsupp
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusUnipotence

section Polynomial

variable {k C σ τ Λ : Type*} [CommRing k] [CommRing C] [Algebra k C] [AddCommMonoid Λ]

/-- Evaluating a weighted homogeneous polynomial at homogeneous elements of a graded family
gives a homogeneous element of the same weight. -/
theorem aeval_mem_graded_of_isWeightedHomogeneous (𝒜 : Λ → Submodule k C) [SetLike.GradedMonoid 𝒜]
    {w : σ → Λ} {y : σ → C} (hy : ∀ j, y j ∈ 𝒜 (w j)) {p : MvPolynomial σ k} {χ : Λ}
    (hp : IsWeightedHomogeneous w p χ) : aeval y p ∈ 𝒜 χ := by
  classical
  rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hmχ : weight w m = χ := hp (MvPolynomial.mem_support_iff.1 hm)
  rw [aeval_monomial, ← Algebra.smul_def, ← hmχ, weight_apply]
  exact Submodule.smul_mem _ _ (SetLike.prod_pow_mem_graded 𝒜 w y m (fun j _ => hy j))

/-- Renaming variables preserves weighted homogeneity. -/
theorem isWeightedHomogeneous_rename {w : τ → Λ} {f : σ → τ} {p : MvPolynomial σ k} {χ : Λ}
    (hp : IsWeightedHomogeneous (w ∘ f) p χ) : IsWeightedHomogeneous w (rename f p) χ := by
  have := WeightedHomogeneousSubmodule.gradedMonoid (R := k) (w := w)
  rw [rename_eq_aeval]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).1
    (aeval_mem_graded_of_isWeightedHomogeneous (weightedHomogeneousSubmodule k w)
      (fun j => isWeightedHomogeneous_X k w (f j)) hp)

end Polynomial

section Group

open CoordinateWeights Langlands.Algebra.WeightGradedFormallySmooth

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom H.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of k))}

local notation "A" => CharacterUnits.Coord H

/-- If the zero character is not an augmentation weight, the weight-zero coordinates are the
constants. -/
theorem weightSpace_zero_eq (b : AutomorphicAction S.toGrp H)
    (h0 : (0 : characterLattice S) ∉ CoordinateWeights.support b) :
    CoordinateWeights.weightSpace b 0 = LinearMap.range (Algebra.linearMap k A) := by
  apply le_antisymm
  · intro f hf
    refine ⟨coordCounit H f, ?_⟩
    by_contra hne
    have hz : f - algebraMap k A (coordCounit H f) ∈ augmentation H := by
      rw [mem_augmentation]
      change coordCounit H (f - algebraMap k A (coordCounit H f)) = 0
      rw [map_sub, AlgHom.commutes]
      exact sub_self _
    have hc : algebraMap k A (coordCounit H f) ∈ CoordinateWeights.weightSpace b 0 := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_weightSpace_zero b)
    refine h0 ⟨⟨_, hz⟩, fun h => hne ?_, sub_mem hf hc⟩
    have h' := congrArg Subtype.val h
    exact (sub_eq_zero.1 h').symm
  · rintro _ ⟨c, rfl⟩
    rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (one_mem_weightSpace_zero b)

/-- A nonzero eigenfunction of nonzero weight has an augmentation weight. -/
theorem mem_support_of_mem_weightSpace (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp H) {χ : characterLattice S} (hχ : χ ≠ 0) {f : A}
    (hf : f ∈ CoordinateWeights.weightSpace b χ) (hf0 : f ≠ 0) :
    χ ∈ CoordinateWeights.support b :=
  ⟨⟨f, coordCounit_eq_zero b hS hχ hf⟩, fun h => hf0 (congrArg Subtype.val h), hf⟩

open scoped Classical in
/-- The character grading of the coordinate algebra, as a graded algebra. -/
@[instance_reducible]
def weightGradedAlgebra (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp H) : GradedAlgebra (CoordinateWeights.weightSpace b) :=
  { toGradedMonoid :=
      { one_mem := one_mem_weightSpace_zero b
        mul_mem := fun _ _ _ _ hf hg => mul_mem_weightSpace b hf hg }
    toDecomposition :=
      (coordinateWeightDecomposition k H inferInstance S hS b).1.chooseDecomposition }

/-- **Polynomial eigen-coordinates.** Let a split torus `S` act on a smooth affine group `H`
of finite type over a field, and let `ν` be a cocharacter pairing positively with every
augmentation weight. Then the coordinate algebra of `H` is a polynomial algebra on
eigenfunctions `t j` of weights `w j` with `⟨w j, ν⟩ > 0`, listed in nondecreasing order of
`⟨w j, ν⟩`, all vanishing at the identity. -/
theorem exists_positiveWeight_coordinates [LocallyOfFiniteType H.X.hom] [Smooth H.X.hom]
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp H) (ν : cocharacterLattice S)
    (hsupp : ∀ χ ∈ CoordinateWeights.support b, 0 < latticePairing S χ ν) :
    ∃ (d : ℕ) (w : Fin d → characterLattice S) (t : Fin d → A),
      Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A) ∧
      (∀ j, t j ∈ CoordinateWeights.weightSpace b (w j)) ∧ (∀ j, coordCounit H (t j) = 0) ∧
      (∀ j, 0 < latticePairing S (w j) ν) ∧ Monotone (fun j => latticePairing S (w j) ν) := by
  classical
  have : Algebra.FiniteType k A := Lie.coordinateAlgebraFiniteType H
  have := formallySmooth_coord (H := H)
  have : Nontrivial A := RingHom.domain_nontrivial (coordCounit H).toRingHom
  let _ : GradedAlgebra (CoordinateWeights.weightSpace b) := weightGradedAlgebra hS b
  let h : characterLattice S →+ ℤ := ((latticePairing S).flip ν).toAddMonoidHom
  have h0 : CoordinateWeights.weightSpace b 0 = LinearMap.range (Algebra.linearMap k A) :=
    weightSpace_zero_eq b fun h0 => by
      have := hsupp 0 h0
      rw [map_zero, LinearMap.zero_apply] at this
      exact lt_irrefl _ this
  have hpos : ∀ χ, χ ≠ 0 → ∀ a ∈ CoordinateWeights.weightSpace b χ, a ≠ 0 → 0 < h χ :=
    fun χ hχ a ha ha0 => hsupp χ (mem_support_of_mem_weightSpace hS b hχ ha ha0)
  obtain ⟨n, w, x, hw, hmono, hx, hbij⟩ :=
    exists_weight_aeval_bijective (CoordinateWeights.weightSpace b) h h0 hpos
  refine ⟨n, w, x, hbij, hx, fun j => coordCounit_eq_zero b hS ?_ (hx j), hw, hmono⟩
  intro hj
  have := hw j
  rw [hj, map_zero] at this
  exact lt_irrefl _ this

/-- **Triangular group law.** In polynomial eigen-coordinates of positive, nondecreasing
heights, the group law is `(x y)_j = x_j + y_j + P_j`, where the polynomial `P_j` only involves
the coordinates of index `< j` of `x` and `y`. -/
theorem exists_triangular_mul (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp H)
    (ν : cocharacterLattice S) {d : ℕ} {w : Fin d → characterLattice S} {t : Fin d → A}
    (ht : Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] A))
    (htw : ∀ j, t j ∈ CoordinateWeights.weightSpace b (w j)) (hε : ∀ j, coordCounit H (t j) = 0)
    (hw : ∀ j, 0 < latticePairing S (w j) ν)
    (hmono : Monotone (fun j => latticePairing S (w j) ν)) :
    ∃ P : Fin d → MvPolynomial (Fin d ⊕ Fin d) k,
      (∀ j, ∀ v ∈ (P j).vars, Sum.elim id id v < j) ∧
      ∀ (B : Type u) [CommRing B] [Algebra k B] (x y : Lie.AffinePoints H B) (j : Fin d),
        Lie.pointCoordinates H (x * y) (t j) =
          Lie.pointCoordinates H x (t j) + Lie.pointCoordinates H y (t j) +
            aeval (Sum.elim (fun i => Lie.pointCoordinates H x (t i))
              (fun i => Lie.pointCoordinates H y (t i))) (P j) := by
  classical
  let _ : GradedAlgebra (CoordinateWeights.weightSpace b) := weightGradedAlgebra hS b
  let h : characterLattice S →+ ℤ := ((latticePairing S).flip ν).toAddMonoidHom
  let e : MvPolynomial (Fin d) k ≃ₐ[k] A := AlgEquiv.ofBijective (aeval t) ht
  have he : ∀ i, e.symm (t i) = X i := fun i => by
    rw [AlgEquiv.symm_apply_eq]
    simp [e]
  let fL : A →ₐ[k] MvPolynomial (Fin d ⊕ Fin d) k := (rename Sum.inl).comp e.symm.toAlgHom
  let fR : A →ₐ[k] MvPolynomial (Fin d ⊕ Fin d) k := (rename Sum.inr).comp e.symm.toAlgHom
  let L : A ⊗[k] A →ₐ[k] MvPolynomial (Fin d ⊕ Fin d) k :=
    Algebra.TensorProduct.lift fL fR fun _ _ => Commute.all _ _
  let Q : Fin d → MvPolynomial (Fin d ⊕ Fin d) k := fun j => L (coordComul H (t j))
  -- The group law in terms of `Q`.
  have hQ : ∀ (B : Type u) [CommRing B] [Algebra k B] (x y : Lie.AffinePoints H B)
      (j : Fin d), Lie.pointCoordinates H (x * y) (t j) =
        aeval (Sum.elim (fun i => Lie.pointCoordinates H x (t i))
          (fun i => Lie.pointCoordinates H y (t i))) (Q j) := by
    intro B _ _ x y j
    set φ : MvPolynomial (Fin d ⊕ Fin d) k →ₐ[k] B :=
      aeval (Sum.elim (fun i => Lie.pointCoordinates H x (t i))
        (fun i => Lie.pointCoordinates H y (t i))) with hφ
    have hcomp : ∀ (f : Fin d → Fin d ⊕ Fin d) (z : Lie.AffinePoints H B),
        (∀ i, φ (X (f i)) = Lie.pointCoordinates H z (t i)) →
        ∀ a : A, φ (rename f (e.symm a)) = Lie.pointCoordinates H z a := by
      intro f z hf a
      obtain ⟨p, rfl⟩ := e.surjective a
      rw [AlgEquiv.symm_apply_apply]
      induction p using MvPolynomial.induction_on with
      | C c => simp [e]
      | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
      | mul_X p i hp => rw [map_mul, map_mul, hp, rename_X, hf, map_mul, map_mul]; simp [e]
    have hx : ∀ a : A, φ (fL a) = Lie.pointCoordinates H x a :=
      hcomp Sum.inl x fun i => by simp [hφ]
    have hy : ∀ a : A, φ (fR a) = Lie.pointCoordinates H y a :=
      hcomp Sum.inr y fun i => by simp [hφ]
    let l := Algebra.TensorProduct.lift (Lie.pointCoordinates H x) (Lie.pointCoordinates H y)
      fun _ _ => Commute.all _ _
    have hmul : Lie.pointCoordinates H (x * y) = l.comp (CharacterUnits.comul H) := by
      have hpt := pt_comp_comul H l (f := Lie.pointCoordinates H x)
        (g := Lie.pointCoordinates H y)
        (Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _)
        (Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _)
      simp only [pt, Equiv.symm_apply_apply] at hpt
      rw [← hpt, Equiv.apply_symm_apply]
    have key : ∀ z : A ⊗[k] A, φ (L z) = l z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a a' =>
        simp only [L, l, Algebra.TensorProduct.lift_tmul, map_mul, hx, hy]
      | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
    rw [hmul, AlgHom.comp_apply, ← key]
    rfl
  -- `Q j` is weighted homogeneous of weight `w j`.
  let w' : Fin d ⊕ Fin d → characterLattice S := fun v => w (Sum.elim id id v)
  have hhom : ∀ j, IsWeightedHomogeneous w' (Q j) (w j) := by
    intro j
    have hsym : ∀ {χ : characterLattice S} {a : A}, a ∈ CoordinateWeights.weightSpace b χ →
        IsWeightedHomogeneous w (e.symm a) χ := fun {χ a} ha =>
      isWeightedHomogeneous_of_aeval_mem (CoordinateWeights.weightSpace b) htw ht.1 (by
        change e (e.symm a) ∈ _
        rwa [AlgEquiv.apply_symm_apply])
    have hle : (⨆ α, Submodule.map₂ (TensorProduct.mk k A A) (CoordinateWeights.weightSpace b α)
        (CoordinateWeights.weightSpace b (w j - α))) ≤
        (weightedHomogeneousSubmodule k w' (w j)).comap L.toLinearMap := by
      refine iSup_le fun α => Submodule.map₂_le.2 fun a ha a' ha' => ?_
      change IsWeightedHomogeneous w' (L (a ⊗ₜ a')) (w j)
      have h1 : IsWeightedHomogeneous w' (fL a) α :=
        isWeightedHomogeneous_rename (w := w') (f := Sum.inl) (hsym ha)
      have h2 : IsWeightedHomogeneous w' (fR a') (w j - α) :=
        isWeightedHomogeneous_rename (w := w') (f := Sum.inr) (hsym ha')
      have h3 := h1.mul h2
      rw [add_sub_cancel] at h3
      simpa [L] using h3
    exact hle (coordComul_mem_iSup b hS (htw j))
  -- The linear coefficients of `Q j`.
  have h1 : ∀ i, Lie.pointCoordinates H (1 : Lie.AffinePoints H (MvPolynomial (Fin d) k)) (t i)
      = 0 := fun i => by
    rw [Lie.pointCoordinates_one, AlgHom.comp_apply]
    change algebraMap k _ (coordCounit H (t i)) = 0
    rw [hε i, map_zero]
  let x₀ : Lie.AffinePoints H (MvPolynomial (Fin d) k) :=
    (Lie.pointCoordinates H).symm e.symm.toAlgHom
  have hx₀ : ∀ i, Lie.pointCoordinates H x₀ (t i) = X i := fun i => by
    simp only [x₀, Equiv.apply_symm_apply]
    exact he i
  have hkillL : (killCompl (Sum.inl_injective (α := Fin d) (β := Fin d)) :
      MvPolynomial (Fin d ⊕ Fin d) k →ₐ[k] MvPolynomial (Fin d) k) = aeval (Sum.elim X 0) := by
    apply algHom_ext
    rintro (i | i)
    · rw [aeval_X, Sum.elim_inl, ← rename_X (R := k) Sum.inl i, killCompl_rename_app]
    · simp [killCompl]
  have hkillR : (killCompl (Sum.inr_injective (α := Fin d) (β := Fin d)) :
      MvPolynomial (Fin d ⊕ Fin d) k →ₐ[k] MvPolynomial (Fin d) k) =
        aeval (Sum.elim (0 : Fin d → MvPolynomial (Fin d) k) X) := by
    apply algHom_ext
    rintro (i | i)
    · simp [killCompl]
    · rw [aeval_X, Sum.elim_inr, ← rename_X (R := k) Sum.inr i, killCompl_rename_app]
  have hlinL : ∀ (j i : Fin d), (Q j).coeff (Finsupp.single (Sum.inl i) 1) =
      if i = j then 1 else 0 := by
    intro j i
    have hq := hQ _ x₀ 1 j
    rw [mul_one] at hq
    have hel : (Sum.elim (fun i => Lie.pointCoordinates H x₀ (t i))
        (fun i => Lie.pointCoordinates H 1 (t i)) :
          Fin d ⊕ Fin d → MvPolynomial (Fin d) k) = Sum.elim X 0 := by
      funext v
      rcases v with i | i
      · simp [hx₀]
      · simp [h1]
    rw [hel, ← hkillL, hx₀] at hq
    rw [← Finsupp.mapDomain_single, ← coeff_killCompl Sum.inl_injective, ← hq, coeff_X]
    simp only [Finsupp.single_left_inj one_ne_zero, eq_comm]
  have hlinR : ∀ (j i : Fin d), (Q j).coeff (Finsupp.single (Sum.inr i) 1) =
      if i = j then 1 else 0 := by
    intro j i
    have hq := hQ _ 1 x₀ j
    rw [one_mul] at hq
    have hel : (Sum.elim (fun i => Lie.pointCoordinates H 1 (t i))
        (fun i => Lie.pointCoordinates H x₀ (t i)) :
          Fin d ⊕ Fin d → MvPolynomial (Fin d) k) =
        Sum.elim (0 : Fin d → MvPolynomial (Fin d) k) X := by
      funext v
      rcases v with i | i
      · simp [h1]
      · simp [hx₀]
    rw [hel, ← hkillR, hx₀] at hq
    rw [← Finsupp.mapDomain_single, ← coeff_killCompl Sum.inr_injective, ← hq, coeff_X]
    simp only [Finsupp.single_left_inj one_ne_zero, eq_comm]
  -- The triangular remainder.
  refine ⟨fun j => Q j - X (Sum.inl j) - X (Sum.inr j), fun j v hv => ?_, ?_⟩
  · have hv' : v ∈ (Q j - X (Sum.inl j) - X (Sum.inr j)).vars := hv
    obtain ⟨m, hm, hmv⟩ := (mem_vars_iff_mem_support v).1 hv'
    rw [MvPolynomial.mem_support_iff, coeff_sub, coeff_sub, coeff_X, coeff_X] at hm
    rw [Finsupp.mem_support_iff] at hmv
    have hsingle : ∀ u, m ≠ Finsupp.single u 1 := by
      rintro (i | i) rfl
      · apply hm
        rw [hlinL]
        by_cases hij : i = j
        · subst hij
          simp [Finsupp.single_left_inj one_ne_zero]
        · simp [Finsupp.single_left_inj one_ne_zero, hij, Ne.symm hij]
      · apply hm
        rw [hlinR]
        by_cases hij : i = j
        · subst hij
          simp [Finsupp.single_left_inj one_ne_zero]
        · simp [Finsupp.single_left_inj one_ne_zero, hij, Ne.symm hij]
    rw [ite_eq_right (Ne.symm (hsingle (Sum.inl j))), ite_eq_right (Ne.symm (hsingle (Sum.inr j))),
      sub_zero, sub_zero] at hm
    have hwm : weight w' m = w j := hhom j hm
    have hw' : ∀ u, 0 < h (w' u) := fun u => hw _
    have hlt := height_lt_of_ne_single hw' hmv (hsingle v)
    rw [hwm] at hlt
    exact lt_of_not_ge fun hle => absurd (hmono hle) (not_le.2 hlt)
  · intro B _ _ x y j
    rw [hQ B x y j]
    simp only [map_sub, aeval_X, Sum.elim_inl, Sum.elim_inr]
    ring

end Group

end Langlands.GroupScheme.TorusUnipotence
