import Langlands.BruhatTits.IntegralModels.NormOneTorusDepthZero
import Langlands.CommutativeAlgebra.FiniteSeparableLiftedPolynomialModel

/-! # Depth-zero regression: the unramified quadratic norm-one torus

This module instantiates `NormOneTorusDepthZero` with concrete data. Let `F`
be a nonarchimedean local field and `f = X ^ 2 + b X + c` a monic quadratic
over `𝒪[F]` whose discriminant `b ^ 2 - 4 c` is a unit and whose reduction is
irreducible over `𝓀[F]` (`UnramifiedQuadraticData F`). Then
`B = 𝒪[F][X] / (f)` is finite free over `𝒪[F]`, `E = F[X] / (f)` is a
separable quadratic field extension of `F`, and `𝓀[F][X] / (f̄)` is a
quadratic field extension of `𝓀[F]`. The norm-one kernel of `B` is smooth,
because `B ⊗ B ≃ B × B` by the Chinese remainder theorem for the two roots
`α` and `-b - α` of `f` in `B`, which differ by a unit.

Such data exist for every `F` (`UnramifiedQuadraticData.nonempty`): lift an
irreducible monic quadratic over the finite residue field. Hence every
nonarchimedean local field has an anisotropic norm-one torus with smooth
model data whose depth-zero quotient has order `q + 1`
(`exists_unramifiedQuadraticNormOne`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj TensorProduct ValuativeRel

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme WeilGm Langlands.CommutativeAlgebra

section Quadratic

variable {R : Type*} [CommRing R] (b c : R)

/-- The monic quadratic polynomial `X ^ 2 + b X + c`. -/
noncomputable def monicQuadratic : R[X] := X ^ 2 + C b * X + C c

theorem monicQuadratic_monic : (monicQuadratic b c).Monic := by
  unfold monicQuadratic
  monicity!

theorem natDegree_monicQuadratic [Nontrivial R] : (monicQuadratic b c).natDegree = 2 := by
  unfold monicQuadratic
  compute_degree!

theorem map_monicQuadratic {S : Type*} [CommRing S] (f : R →+* S) :
    (monicQuadratic b c).map f = monicQuadratic (f b) (f c) := by
  simp [monicQuadratic]

theorem eval_monicQuadratic (x : R) :
    (monicQuadratic b c).eval x = x ^ 2 + b * x + c := by
  simp [monicQuadratic]

theorem derivative_monicQuadratic :
    derivative (monicQuadratic b c) = 2 * X + C b := by
  simp [monicQuadratic]
  ring

/-- A monic quadratic with unit discriminant is separable. -/
theorem monicQuadratic_separable (h : IsUnit (b ^ 2 - 4 * c)) :
    (monicQuadratic b c).Separable := by
  obtain ⟨u, hu⟩ := h
  refine ⟨C (-4 * (↑u⁻¹ : R)), C (↑u⁻¹ : R) * derivative (monicQuadratic b c), ?_⟩
  rw [derivative_monicQuadratic]
  have h1 : C (↑u⁻¹ : R) * C (↑u : R) = 1 := by rw [← C_mul, Units.inv_mul, C_1]
  rw [hu] at h1
  simp only [map_mul, map_sub, map_pow, map_ofNat] at h1
  simp only [monicQuadratic, map_mul, map_neg, map_ofNat]
  linear_combination h1

/-- If `X ^ 2 + b X + c` has a root `α` and unit discriminant, its quotient
ring splits as two copies of the coefficient ring, by the Chinese remainder
theorem for the coprime factors `X - α` and `X + b + α`. -/
noncomputable def adjoinRootMonicQuadraticSplit (α : R) (hα : (monicQuadratic b c).eval α = 0)
    (h : IsUnit (b ^ 2 - 4 * c)) :
    AdjoinRoot (monicQuadratic b c) ≃ₐ[R] (Fin 2 → R) :=
  let r : Fin 2 → R := ![α, -b - α]
  have hα' : α ^ 2 + b * α + c = 0 := by rwa [eval_monicQuadratic] at hα
  have hsub : IsUnit (α - (-b - α)) := by
    have : (α - (-b - α)) ^ 2 = b ^ 2 - 4 * c := by linear_combination 4 * hα'
    exact (isUnit_pow_iff two_ne_zero).1 (this ▸ h)
  have hcop : Pairwise fun i j =>
      IsCoprime (Ideal.span {X - C (r i)}) (Ideal.span {X - C (r j)}) := by
    intro i j hij
    simp only [Ideal.isCoprime_span_singleton_iff]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact isCoprime_X_sub_C_of_isUnit_sub hsub
    · exact isCoprime_X_sub_C_of_isUnit_sub (by rw [← neg_sub]; exact hsub.neg)
    · exact absurd rfl hij
  have hprod : ∏ i, (X - C (r i)) = monicQuadratic b c := by
    have hC : C (α ^ 2 + b * α + c) = 0 := by rw [hα', C_0]
    simp only [map_add, map_mul, map_pow] at hC
    simp only [Fin.prod_univ_two, r, Matrix.cons_val_zero, Matrix.cons_val_one,
      monicQuadratic, map_sub, map_neg]
    linear_combination (-1 : R[X]) * hC
  have hI : Ideal.span {monicQuadratic b c} = ⨅ i, Ideal.span {X - C (r i)} := by
    rw [Ideal.iInf_span_singleton
      (fun i j hij => (Ideal.isCoprime_span_singleton_iff _ _).1 (hcop hij)), hprod]
  (Ideal.quotientEquivAlgOfEq R hI).trans
    ((AlgEquiv.ofRingEquiv (f := Ideal.quotientInfRingEquivPiQuotient _ hcop) (fun x => rfl)).trans
      (AlgEquiv.piCongrRight fun i => Polynomial.quotientSpanXSubCAlgEquiv (r i)))

section FiniteField

variable {K : Type*} [Field K] [Finite K]

/-- Over a finite field, a monic quadratic with zero discriminant has a root:
`-b / 2` if the characteristic is not two, and a square root of `c` if it is
(then `b = 0`). -/
theorem exists_eval_monicQuadratic_eq_zero_of_disc_eq_zero {b c : K}
    (h : b ^ 2 - 4 * c = 0) : ∃ x, (monicQuadratic b c).eval x = 0 := by
  simp only [eval_monicQuadratic]
  by_cases h2 : ringChar K = 2
  · have h20 : (2 : K) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := K)
      rw [h2] at this
      exact_mod_cast this
    have hb : b = 0 := by
      have : b ^ 2 = 0 := by linear_combination h + 2 * c * h20
      exact (pow_eq_zero_iff two_ne_zero).1 this
    obtain ⟨d, hd⟩ := FiniteField.isSquare_of_char_two h2 c
    refine ⟨d, ?_⟩
    rw [hb, hd]
    linear_combination d * d * h20
  · have : NeZero (2 : K) := ⟨Ring.two_ne_zero h2⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (a := (1 : K)) (b := b) (c := c) one_ne_zero
      ⟨0, by rw [discrim]; linear_combination h⟩
    exact ⟨x, by linear_combination hx⟩

/-- An irreducible monic quadratic over a finite field has nonzero
discriminant. -/
theorem disc_ne_zero_of_irreducible_monicQuadratic {b c : K}
    (h : Irreducible (monicQuadratic b c)) : b ^ 2 - 4 * c ≠ 0 := by
  intro h0
  obtain ⟨x, hx⟩ := exists_eval_monicQuadratic_eq_zero_of_disc_eq_zero h0
  have h1 := natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root h hx)
  rw [natDegree_monicQuadratic] at h1
  norm_num at h1

variable (K) in
/-- Every finite field has an irreducible monic quadratic: the minimal
polynomial of a primitive element of its quadratic extension. -/
theorem exists_irreducible_monicQuadratic : ∃ b c : K, Irreducible (monicQuadratic b c) := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  obtain ⟨α, hα⟩ :=
    Field.exists_primitive_element_of_finite_bot K (FiniteField.Extension K (ringChar K) 2)
  have hint := IsIntegral.of_finite K α
  have hdeg : (minpoly K α).natDegree = 2 :=
    ((Field.primitive_element_iff_minpoly_natDegree_eq K α).1 hα).trans
      (FiniteField.finrank_extension K (ringChar K) 2)
  refine ⟨(minpoly K α).coeff 1, (minpoly K α).coeff 0, ?_⟩
  have heq : monicQuadratic ((minpoly K α).coeff 1) ((minpoly K α).coeff 0) = minpoly K α := by
    conv_rhs => rw [(minpoly.monic hint).as_sum, hdeg]
    simp [monicQuadratic, Finset.sum_range_succ]
    ring
  rw [heq]
  exact minpoly.irreducible hint

end FiniteField

end Quadratic

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Coefficients of a monic quadratic `X ^ 2 + b X + c` over `𝒪[F]` with unit
discriminant and irreducible reduction. Such a polynomial presents an
unramified quadratic extension of `F`; "unramified" is not defined or proved
in this module, which works with the quotient rings directly. -/
structure UnramifiedQuadraticData where
  b : 𝒪[F]
  c : 𝒪[F]
  isUnit_disc : IsUnit (b ^ 2 - 4 * c)
  irreducible_residue : Irreducible ((monicQuadratic b c).map (algebraMap 𝒪[F] 𝓀[F]))

namespace UnramifiedQuadraticData

variable {F} (D : UnramifiedQuadraticData F)

/-- The integral quadratic polynomial. -/
abbrev polynomial : 𝒪[F][X] := monicQuadratic D.b D.c

/-- The finite free `𝒪[F]`-algebra `𝒪[F][X] / (X ^ 2 + b X + c)`. -/
abbrev Carrier : Type u := AdjoinRoot D.polynomial

instance : Module.Finite 𝒪[F] D.Carrier := (monicQuadratic_monic _ _).finite_adjoinRoot

instance : Module.Free 𝒪[F] D.Carrier := (monicQuadratic_monic _ _).free_adjoinRoot

instance : Nontrivial D.Carrier :=
  (AdjoinRoot.nontrivial_iff_of_monic (monicQuadratic_monic _ _)).2 (by
    rw [degree_eq_natDegree (monicQuadratic_monic _ _).ne_zero, natDegree_monicQuadratic]
    norm_num)

/-- The generic quadratic is irreducible, by Gauss's lemma from its
irreducible reduction. -/
theorem irreducible_generic : Irreducible (D.polynomial.map (algebraMap 𝒪[F] F)) :=
  ((monicQuadratic_monic _ _).irreducible_iff_irreducible_map_fraction_map).1
    (Monic.irreducible_of_irreducible_map (φ := algebraMap 𝒪[F] 𝓀[F]) _
      (monicQuadratic_monic _ _) D.irreducible_residue)

instance : Fact (Irreducible (D.polynomial.map (algebraMap 𝒪[F] F))) := ⟨D.irreducible_generic⟩

instance : Fact (Irreducible (D.polynomial.map (algebraMap 𝒪[F] 𝓀[F]))) :=
  ⟨D.irreducible_residue⟩

/-- The unramified quadratic extension `E = F[X] / (X ^ 2 + b X + c)`. -/
abbrev GenericField : Type u := AdjoinRoot (D.polynomial.map (algebraMap 𝒪[F] F))

/-- The quadratic residue extension `𝓀[F][X] / (X ^ 2 + b̄ X + c̄)`. -/
abbrev ResidueField : Type u := AdjoinRoot (D.polynomial.map (algebraMap 𝒪[F] 𝓀[F]))

instance : FiniteDimensional F D.GenericField :=
  ((monicQuadratic_monic _ _).map _).finite_adjoinRoot

instance : Algebra.IsSeparable F D.GenericField := by
  have hsep : IsSeparable F (AdjoinRoot.root (D.polynomial.map (algebraMap 𝒪[F] F))) := by
    rw [IsSeparable, AdjoinRoot.minpoly_root D.irreducible_generic.ne_zero,
      ((monicQuadratic_monic _ _).map _).leadingCoeff, inv_one, C_1, mul_one]
    exact (monicQuadratic_separable _ _ D.isUnit_disc).map
  have := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F _).2 hsep
  rw [IntermediateField.adjoin_root_eq_top] at this
  exact (IntermediateField.isSeparable_top F _).1 this

/-- The generic fibre of the quotient algebra is the unramified quadratic
extension. -/
noncomputable abbrev genericEquiv : F ⊗[𝒪[F]] D.Carrier ≃ₐ[F] D.GenericField :=
  adjoinRootBaseChangeEquiv 𝒪[F] F D.polynomial

/-- The special fibre of the quotient algebra is the quadratic residue
extension. -/
noncomputable abbrev residueEquiv : 𝓀[F] ⊗[𝒪[F]] D.Carrier ≃ₐ[𝓀[F]] D.ResidueField :=
  adjoinRootBaseChangeEquiv 𝒪[F] 𝓀[F] D.polynomial

/-- The residue extension has degree two. -/
theorem finrank_residueField : Module.finrank 𝓀[F] D.ResidueField = 2 := by
  rw [(AdjoinRoot.powerBasis (f := D.polynomial.map (algebraMap 𝒪[F] 𝓀[F]))
      D.irreducible_residue.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
    map_monicQuadratic, natDegree_monicQuadratic]

/-- The norm-one kernel of `B = 𝒪[F][X] / (X ^ 2 + b X + c)` is smooth: after
the faithfully flat base change to `B` itself, `B ⊗ B ≃ B × B`. -/
theorem smooth : Smooth (normOne (CommRingCat.of 𝒪[F]) D.Carrier).X.hom := by
  have hroot : (monicQuadratic (algebraMap 𝒪[F] D.Carrier D.b)
      (algebraMap 𝒪[F] D.Carrier D.c)).eval (AdjoinRoot.root D.polynomial) = 0 := by
    rw [← map_monicQuadratic, Polynomial.eval_map, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root]
  let e : CommRingCat.of D.Carrier ⊗[CommRingCat.of 𝒪[F]] D.Carrier ≃ₐ[CommRingCat.of D.Carrier]
      (ULift.{u} (Fin 2) → CommRingCat.of D.Carrier) :=
    (adjoinRootBaseChangeEquiv 𝒪[F] D.Carrier D.polynomial).trans
      ((AdjoinRoot.algEquivOfEq D.Carrier _ _ (map_monicQuadratic _ _ _)).trans
        ((adjoinRootMonicQuadraticSplit _ _ _ hroot (by
          simpa [map_sub, map_pow, map_mul, map_ofNat] using
            D.isUnit_disc.map (algebraMap 𝒪[F] D.Carrier))).trans
          (AlgEquiv.piCongrLeft D.Carrier (fun _ => D.Carrier) Equiv.ulift.symm)))
  exact normOne_smooth_of_decomposition (CommRingCat.of 𝒪[F]) D.Carrier
    (CommRingCat.of D.Carrier) (ULift.{u} (Fin 2)) e

/-- The relative-component model data of the unramified quadratic norm-one
torus `R¹_{E/F} G_m`. -/
noncomputable def modelData :
    RelativeComponentModelData 𝒪[F] F (normOne (CommRingCat.of F) D.GenericField) :=
  normOneModelData F D.Carrier D.GenericField D.genericEquiv D.smooth D.ResidueField D.residueEquiv

/-- The special-fibre quotient data: the identity quotient. -/
noncomputable def quotientData : SpecialFibreQuotientData D.modelData :=
  normOneQuotientData F D.Carrier D.GenericField D.genericEquiv D.smooth D.ResidueField
    D.residueEquiv

/-- The identity quotient is a reductive quotient of the special fibre. -/
theorem quotientData_isReductiveQuotient : D.quotientData.IsReductiveQuotient :=
  normOneQuotientData_isReductiveQuotient F _ _ _ _ _ _

/-- The generic torus `R¹_{E/F} G_m` is anisotropic. -/
theorem isAnisotropic : IsAnisotropic (normOne (CommRingCat.of F) D.GenericField) :=
  normOne_isAnisotropic F _

/-- The depth-zero quotient `G^0(𝒪) / G(F)^{0+}` of the unramified quadratic
norm-one torus has order `q + 1`. -/
theorem index_positivePoints_subgroupOf :
    (D.quotientData.positivePoints.subgroupOf D.modelData.neutral.integralPoints).index =
      Nat.card 𝓀[F] + 1 :=
  normOne_index_positivePoints_subgroupOf_of_finrank_eq_two F _ _ _ _ _ _ D.finrank_residueField

variable (F) in
/-- Unramified quadratic data exist over every nonarchimedean local field: lift
the coefficients of an irreducible monic quadratic over the finite residue
field; its discriminant is nonzero, so the lifted discriminant is a unit. -/
theorem nonempty : Nonempty (UnramifiedQuadraticData F) := by
  obtain ⟨b₀, c₀, hirr⟩ := exists_irreducible_monicQuadratic 𝓀[F]
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b₀
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective c₀
  refine ⟨⟨b, c, ?_, ?_⟩⟩
  · rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sub, map_pow, map_mul, map_ofNat]
    exact disc_ne_zero_of_irreducible_monicQuadratic hirr
  · rw [map_monicQuadratic, IsLocalRing.ResidueField.algebraMap_eq]
    exact hirr

end UnramifiedQuadraticData

/-- Every nonarchimedean local field `F` has an anisotropic norm-one torus
`R¹_{E/F} G_m`, for an unramified quadratic extension `E / F`, with smooth
relative-component model data whose identity quotient is reductive and whose
depth-zero quotient `G^0(𝒪) / G(F)^{0+}` has order `q + 1`. -/
theorem exists_unramifiedQuadraticNormOne :
    ∃ D : UnramifiedQuadraticData F,
      IsAnisotropic (normOne (CommRingCat.of F) D.GenericField) ∧
      D.modelData.neutral.IsSmooth ∧ D.quotientData.IsReductiveQuotient ∧
      (D.quotientData.positivePoints.subgroupOf D.modelData.neutral.integralPoints).index =
        Nat.card 𝓀[F] + 1 := by
  obtain ⟨D⟩ := UnramifiedQuadraticData.nonempty F
  exact ⟨D, D.isAnisotropic, D.smooth, D.quotientData_isReductiveQuotient,
    D.index_positivePoints_subgroupOf⟩

end Langlands.BruhatTits.IntegralModels

end
