import Langlands.Representation.Unramified.SphericalHeckeCommutativity
import Langlands.Representation.Unramified.StandardHeckeSum
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-! # Standard Hecke scalars of invariantly paired spherical vectors -/

noncomputable section

namespace Langlands.Unramified

open Correspondence MeasureTheory MeasureTheory.Measure GeneralLinear.Iwasawa MinusculeCosets

universe uF uV uW

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

namespace PairedHecke

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The spherical corner action on the fixed vectors of a smooth representation. -/
abbrev corner (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsSmooth ρ) :
    SphericalHeckeAlgebra F r →ₐ[ℂ]
      Module.End ℂ (fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) :=
  Hecke.cornerAction (sphericalHaar F r) ρ hρ (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r)

/-- Every linear functional computes the corner action by a scalar integral. -/
theorem functional_corner (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (c : SphericalHeckeAlgebra F r)
    (x : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) (L : V →ₗ[ℂ] ℂ) :
    L (corner F ρ hρ c x : V) = ∫ g, c g * L (ρ g x) ∂(sphericalHaar F r) := by
  rw [Hecke.cornerAction_apply, Hecke.heckeAction_apply, Hecke.integratedAction_dual]
  rfl

/-- The normalized spherical averaging projection onto the fixed vectors. -/
abbrev sphericalProjection (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) : V →ₗ[ℂ] fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup :=
  Hecke.fixedProjection (sphericalHaar F r) ρ hρ (sphericalOpenSubgroup F r)
    (sphericalOpenSubgroup_isCompact F r)

/-- The defect of the spherical projection of a vector from having scalar `l` under `c`. -/
def heckeDefect (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : IsSmooth ρ)
    (c : SphericalHeckeAlgebra F r) (l : ℂ) : V →ₗ[ℂ] V :=
  (fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup).subtype ∘ₗ
    (corner F ρ hρ c - l • 1) ∘ₗ sphericalProjection F ρ hρ

theorem heckeDefect_apply_fixed (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (c : SphericalHeckeAlgebra F r) (l : ℂ)
    (x : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup) :
    heckeDefect F ρ hρ c l x = (corner F ρ hρ c x : V) - l • (x : V) := by
  simp only [heckeDefect, LinearMap.comp_apply, Hecke.fixedProjection_fixed,
    Submodule.subtype_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    Submodule.coe_sub, Submodule.coe_smul]

/-- Vanishing defect on a fixed vector is the scalar relation. -/
theorem corner_eq_smul_of_heckeDefect (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (c : SphericalHeckeAlgebra F r) (l : ℂ)
    (x : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup)
    (h : heckeDefect F ρ hρ c l x = 0) : corner F ρ hρ c x = l • x := by
  rw [heckeDefect_apply_fixed, sub_eq_zero] at h
  exact Subtype.ext h

/-- The defect vanishes identically when `c` acts by `l` on all fixed vectors. -/
theorem heckeDefect_eq_zero (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (c : SphericalHeckeAlgebra F r) (l : ℂ)
    (h : ∀ x : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup,
      corner F ρ hρ c x = l • x) (y : V) : heckeDefect F ρ hρ c l y = 0 := by
  simp only [heckeDefect, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, h, sub_self, map_zero]

/-- Intertwiners commute with the defect. -/
theorem heckeDefect_intertwiner (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsSmooth σ) (T : ρ.IntertwiningMap σ) (c : SphericalHeckeAlgebra F r) (l : ℂ)
    (x : V) : T (heckeDefect F ρ hρ c l x) = heckeDefect F σ hσ c l (T x) := by
  have h1 := Hecke.fixedProjection_intertwiner (sphericalHaar F r) ρ hρ
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) hσ T x
  have h2 := Hecke.cornerAction_intertwiner (sphericalHaar F r) ρ hρ
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) hσ T c
    (sphericalProjection F ρ hρ x)
  simp only [heckeDefect, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, Submodule.subtype_apply, map_sub, map_smul]
  rw [← h1, ← h2]
  rfl

/-- Pairing a spherical projection against a fixed vector forgets the projection. -/
theorem pairing_sphericalProjection (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g x y, B (ρ g x) (σ g y) = B x y) (y : V)
    (w : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup) :
    B (sphericalProjection F ρ hρ y) w = B y w := by
  let K := sphericalOpenSubgroup F r
  have hK := sphericalOpenSubgroup_isCompact F r
  have hfix : ∀ g ∈ (K : Set (GeneralLinear (r + 1) F.Carrier)), B (ρ g y) w = B y w := by
    intro g hg
    have hw : σ g w = w := w.property ⟨g, hg⟩
    conv_lhs => rw [← hw]
    exact hB g y w
  have h := Hecke.integratedAction_dual (sphericalHaar F r) ρ hρ
    (Hecke.HeckeAlgebra.toTestFunction _ (Hecke.HeckeAlgebra.normalizedIndicator
      (sphericalHaar F r) K hK)) y (B.flip w)
  change B.flip w (sphericalProjection F ρ hρ y : V) = B.flip w y
  rw [Hecke.fixedProjection_apply, Hecke.heckeAction_apply, h]
  have e : (fun g => (Hecke.HeckeAlgebra.toTestFunction _ (Hecke.HeckeAlgebra.normalizedIndicator
      (sphericalHaar F r) K hK) : GeneralLinear (r + 1) F.Carrier → ℂ) g * B.flip w (ρ g y)) =
      (K : Set (GeneralLinear (r + 1) F.Carrier)).indicator
        (fun _ => ((sphericalHaar F r).real (K : Set (GeneralLinear (r + 1) F.Carrier)) : ℂ)⁻¹ *
          B y w) := by
    funext g
    change Hecke.HeckeAlgebra.normalizedIndicator (sphericalHaar F r) K hK g * B (ρ g y) w = _
    rw [Hecke.HeckeAlgebra.normalizedIndicator_apply]
    by_cases hg : g ∈ (K : Set (GeneralLinear (r + 1) F.Carrier))
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hfix g hg, mul_one]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero, zero_mul]
  rw [e, integral_indicator_const _ K.isOpen.measurableSet, Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ (Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero _ K hK), one_mul]
  rfl

/-! ### The central standard diagonal and the reversed double cosets -/

open GeneralLinear.Cartan in
/-- The standard diagonal with all entries uniformizers is central. -/
theorem standardDiagonal_last_commute (g : GeneralLinear (r + 1) F.Carrier) :
    standardDiagonal F r (Fin.last (r + 1)) * g = g * standardDiagonal F r (Fin.last (r + 1)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [standardDiagonal, diagonalUnits_mul_apply, mul_diagonalUnits_apply]
  simp [Fin.is_le, mul_comm]

open GeneralLinear.Cartan in
/-- Dividing the central diagonal by `t_j` gives the reversal conjugate of `t_(n-j)`. -/
theorem last_mul_inv_standardDiagonal (j : Fin (r + 2)) :
    standardDiagonal F r (Fin.last (r + 1)) * (standardDiagonal F r j)⁻¹ =
      permGL Fin.revPerm * standardDiagonal F r j.rev * permGL Fin.revPerm := by
  apply Matrix.GeneralLinearGroup.ext
  intro a b
  rw [permGL_mul_mul_apply, standardDiagonal, standardDiagonal, standardDiagonal, ← map_inv,
    diagonalUnits_mul_apply]
  simp only [GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    simp only [Fin.revPerm_symm, Fin.revPerm_apply, ite_true, Fin.val_last, Fin.val_rev, Pi.inv_apply]
    have ha : (a.val < r + 1) = True := eq_true a.is_lt
    by_cases haj : a.val < j.val
    · have h1 : (r + 1 - (a.val + 1) < r + 2 - (j.val + 1)) = False := eq_false (by omega)
      simp only [ha, haj, h1, ite_true, ite_false, Units.mul_inv, Units.val_one]
    · have h1 : (r + 1 - (a.val + 1) < r + 2 - (j.val + 1)) = True := eq_true (by omega)
      simp only [ha, haj, h1, ite_true, ite_false, inv_one, Units.val_one, mul_one]
  · have hab' : Fin.revPerm a ≠ Fin.revPerm.symm b := by
      simpa [Fin.revPerm_symm] using hab
    simp [hab]

/-- Inverting a point of `K t_j K` and multiplying by the central diagonal lands in
`K t_(n-j) K`. -/
theorem mem_doubleCoset_rev_of_mem {j : Fin (r + 2)} {x : GeneralLinear (r + 1) F.Carrier}
    (hx : x ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
      (standardDiagonal F r j)) :
    standardDiagonal F r (Fin.last (r + 1)) * x⁻¹ ∈
      Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
        (standardDiagonal F r j.rev) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Hecke.TestFunction.mem_doubleCosetSet _ _ _).1 hx
  have hw : (GeneralLinear.Cartan.permGL Fin.revPerm : GeneralLinear (r + 1) F.Carrier) ∈
      sphericalOpenSubgroup F r :=
    GeneralLinear.Cartan.permGL_mem (v := ValuativeRel.valuation F.Carrier) _
  rw [Hecke.TestFunction.mem_doubleCosetSet]
  refine ⟨k₂⁻¹ * GeneralLinear.Cartan.permGL Fin.revPerm, mul_mem (inv_mem hk₂) hw,
    GeneralLinear.Cartan.permGL Fin.revPerm * k₁⁻¹, mul_mem hw (inv_mem hk₁), ?_⟩
  rw [mul_inv_rev, mul_inv_rev, ← mul_assoc, ← mul_assoc,
    standardDiagonal_last_commute F k₂⁻¹, mul_assoc k₂⁻¹, last_mul_inv_standardDiagonal]
  simp only [mul_assoc]

/-- The standard Hecke element at an inverse is the reversed one at the central
translate. -/
theorem standardHeckeElement_inv (j : Fin (r + 2)) (g : GeneralLinear (r + 1) F.Carrier) :
    standardHeckeElement F r j g⁻¹ =
      standardHeckeElement F r j.rev (standardDiagonal F r (Fin.last (r + 1)) * g) := by
  rw [standardHeckeElement_apply, standardHeckeElement_apply]
  by_cases h : g⁻¹ ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r)
      (standardDiagonal F r j)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem]
    simpa using mem_doubleCoset_rev_of_mem F h
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem]
    intro h'
    apply h
    have e : standardDiagonal F r (Fin.last (r + 1)) *
        (standardDiagonal F r (Fin.last (r + 1)) * g)⁻¹ = g⁻¹ := by
      rw [mul_inv_rev, ← mul_assoc, standardDiagonal_last_commute F g⁻¹, mul_inv_cancel_right]
    have h'' := mem_doubleCoset_rev_of_mem F h'
    rwa [e, Fin.rev_rev] at h''

/-- On a spherical vector, the Hecke element of the central diagonal acts by that
diagonal. -/
theorem corner_last (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W) (hσ : IsSmooth σ)
    (b : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup) :
    (corner F σ hσ (standardHeckeElement F r (Fin.last (r + 1))) b : W) =
      σ (standardDiagonal F r (Fin.last (r + 1))) b := by
  classical
  set t := standardDiagonal F r (Fin.last (r + 1)) with ht
  let K := sphericalOpenSubgroup F r
  let s : Set (GeneralLinear (r + 1) F.Carrier) :=
    (fun y => t⁻¹ * y) ⁻¹' (K : Set (GeneralLinear (r + 1) F.Carrier))
  have hs : MeasurableSet s :=
    (K.isOpen.preimage (continuous_const.mul continuous_id)).measurableSet
  have hμ : sphericalHaar F r s = 1 := by
    rw [measure_preimage_mul]
    exact sphericalHaar_self F r
  have hfix : ∀ k ∈ (K : Set (GeneralLinear (r + 1) F.Carrier)), σ k b = b :=
    fun k hk => b.property ⟨k, hk⟩
  change Hecke.heckeAction (sphericalHaar F r) σ hσ
    (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra _ _ _
      (standardHeckeElement F r (Fin.last (r + 1)))) (b : W) = _
  rw [Hecke.heckeAction_apply]
  rw [Hecke.integratedAction_eq_sum_of_presentation _ σ hσ _ (b : W)
    (Finset.univ : Finset Unit) (fun _ => s) (fun _ => σ t b) (fun _ _ => hs)
    (fun _ _ _ => by rw [hμ]; exact ENNReal.one_lt_top)]
  · simp [hμ]
  intro y
  change standardHeckeElement F r _ y • σ y b = _
  rw [standardHeckeElement_apply, Finset.univ_unique, Finset.sum_singleton]
  by_cases hy : y ∈ Hecke.TestFunction.doubleCosetSet (sphericalOpenSubgroup F r) t
  · obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (Hecke.TestFunction.mem_doubleCosetSet _ _ _).1 hy
    have hmem : k₁ * t * k₂ ∈ s := by
      change t⁻¹ * (k₁ * t * k₂) ∈ (K : Set (GeneralLinear (r + 1) F.Carrier))
      rw [← standardDiagonal_last_commute F k₁, ← ht, mul_assoc, inv_mul_cancel_left]
      exact mul_mem hk₁ hk₂
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hmem, one_smul]
    rw [← standardDiagonal_last_commute F k₁, ← ht, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, hfix _ hk₂, hfix _ hk₁]
  · have hmem : y ∉ s := by
      intro hy'
      apply hy
      rw [Hecke.TestFunction.mem_doubleCosetSet]
      exact ⟨1, one_mem _, t⁻¹ * y, hy', by rw [one_mul, mul_inv_cancel_left]⟩
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hmem, zero_smul]

/-! ### Adjointness of the standard Hecke scalars -/

/-- If spherical eigenvectors of the standard Hecke elements are paired nontrivially by
an invariant pairing, then their scalars satisfy `λ'_j = λ'_n λ_(n-j)`. -/
theorem scalar_adjoint (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsSmooth σ) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g x y, B (ρ g x) (σ g y) = B x y)
    (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup)
    (b : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup) (l l' : Fin (r + 2) → ℂ)
    (ha : ∀ i, corner F ρ hρ (standardHeckeElement F r i) a = l i • a)
    (hb : ∀ i, corner F σ hσ (standardHeckeElement F r i) b = l' i • b)
    (hab : B a b ≠ 0) (j : Fin (r + 2)) :
    l' j = l' (Fin.last (r + 1)) * l j.rev := by
  set t := standardDiagonal F r (Fin.last (r + 1)) with ht
  set θ := sphericalInverseTranspose F r
  let K := sphericalOpenSubgroup F r
  let c : GeneralLinear (r + 1) F.Carrier → ℂ := fun g => B (ρ g a) b
  have hfixa : ∀ k : K, ρ k a = a := fun k => a.property ⟨k, k.2⟩
  have hfixb : ∀ k : K, σ k b = b := fun k => b.property ⟨k, k.2⟩
  have hc : ∀ (k₁ k₂ : K) g, c (k₁ * g * k₂) = c g := by
    intro k₁ k₂ g
    change B (ρ (k₁ * g * k₂) a) b = B (ρ g a) b
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfixa k₂]
    conv_lhs => rw [← hfixb k₁]
    exact hB _ _ _
  have htb : σ t b = l' (Fin.last (r + 1)) • (b : W) := by
    rw [← corner_last F σ hσ, hb]
    rfl
  have hct : ∀ g, c g = l' (Fin.last (r + 1)) * c (t * g) := by
    intro g
    change B (ρ g a) b = _ * B (ρ (t * g) a) b
    rw [← hB t (ρ g a) b, htb, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
  have hsym : ∀ u, standardHeckeElement F r j (θ u) * c (θ u)⁻¹ =
      standardHeckeElement F r j u⁻¹ * c u := by
    intro u
    obtain ⟨k₁, k₂, hu⟩ := sphericalInverseTranspose_mem_doubleCoset_inv F r u
    rw [hu, Hecke.HeckeAlgebra.Corner.apply_mul_mul]
    congr 1
    have e : ((k₁ : GeneralLinear (r + 1) F.Carrier) * u⁻¹ * k₂)⁻¹ = (k₂⁻¹ : K) * u * (k₁⁻¹ : K) := by
      simp [mul_assoc]
    rw [e, hc]
  have h1 : l' j * B a b = ∫ g, standardHeckeElement F r j g * c g⁻¹ ∂(sphericalHaar F r) := by
    have h := functional_corner F σ hσ (standardHeckeElement F r j) b (B a)
    rw [hb, Submodule.coe_smul, map_smul, smul_eq_mul] at h
    rw [h]
    congr 1
    funext g
    congr 1
    change B a (σ g b) = B (ρ g⁻¹ a) b
    rw [← hB g⁻¹ a (σ g b), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  have h2 : ∫ g, standardHeckeElement F r j.rev g * c g ∂(sphericalHaar F r) =
      l j.rev * B a b := by
    have h := functional_corner F ρ hρ (standardHeckeElement F r j.rev) a (B.flip b)
    rw [ha, Submodule.coe_smul, map_smul, smul_eq_mul] at h
    exact h.symm
  have key : l' j * B a b = l' (Fin.last (r + 1)) * l j.rev * B a b := by
    calc l' j * B a b
        = ∫ g, standardHeckeElement F r j g * c g⁻¹ ∂(sphericalHaar F r) := h1
      _ = ∫ u, standardHeckeElement F r j (θ u) * c (θ u)⁻¹ ∂(sphericalHaar F r) :=
          ((sphericalHaar_measurePreserving_inverseTranspose F r).integral_comp
            θ.toHomeomorph.measurableEmbedding
            (fun g => standardHeckeElement F r j g * c g⁻¹)).symm
      _ = ∫ u, l' (Fin.last (r + 1)) *
            (standardHeckeElement F r j.rev (t * u) * c (t * u)) ∂(sphericalHaar F r) := by
          congr 1
          funext u
          rw [hsym, standardHeckeElement_inv, ← ht, hct u]
          ring
      _ = l' (Fin.last (r + 1)) * l j.rev * B a b := by
          rw [integral_const_mul, integral_mul_left_eq_self
            (fun u => standardHeckeElement F r j.rev u * c u) t, h2, mul_assoc]
  exact mul_right_cancel₀ hab key

/-! ### From adjoint scalars to inverse eigenvalues -/

section Polynomial

open Polynomial

theorem reverse_multiset_prod (m : Multiset ℂ[X]) : m.prod.reverse = (m.map reverse).prod := by
  induction m using Multiset.induction_on with
  | empty => rw [Multiset.prod_zero, Multiset.map_zero, Multiset.prod_zero, ← C_1, reverse_C]
  | cons a m ih =>
      rw [Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons, Multiset.prod_cons]

theorem reverse_one_sub_C_mul_X (z : ℂˣ) : (1 - C (z : ℂ) * X).reverse = X - C (z : ℂ) := by
  have e : (1 : ℂ[X]) - C (z : ℂ) * X = C (-(z : ℂ)) * X + C 1 := by
    rw [map_neg, C_1]
    ring
  rw [e, reverse_add_C, reverse_mul_X, reverse_C,
    natDegree_C_mul_X _ (neg_ne_zero.2 z.ne_zero), pow_one, C_1, one_mul, map_neg]
  ring

/-- The reverse of the Euler polynomial `∏ (1 - z X)` is `∏ (X - z)`. -/
theorem eulerPolynomial_reverse {n : ℕ} (s : Eigenvalues n) :
    (Eigenvalues.eulerPolynomial s).reverse =
      ((s : Multiset ℂˣ).map fun z : ℂˣ => X - C (z : ℂ)).prod := by
  rw [Eigenvalues.eulerPolynomial, reverse_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro z _
  exact reverse_one_sub_C_mul_X z

/-- The Euler polynomial of the inverse spectrum is a scalar multiple of the reverse. -/
theorem C_mul_eulerPolynomial_map_inv {n : ℕ} (s : Eigenvalues n) :
    C (((s : Multiset ℂˣ).map fun z : ℂˣ => -(z : ℂ)).prod) *
        Eigenvalues.eulerPolynomial (s.map fun z => z⁻¹) =
      (Eigenvalues.eulerPolynomial s).reverse := by
  rw [eulerPolynomial_reverse, Eigenvalues.eulerPolynomial, Sym.coe_map, Multiset.map_map,
    map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro z _
  simp only [Function.comp_apply, Units.val_inv_eq_inv_val]
  have hz : -(z : ℂ) * (z : ℂ)⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel₀ z.ne_zero]
  calc C (-(z : ℂ)) * (1 - C (z : ℂ)⁻¹ * X)
      = C (-(z : ℂ)) - C (-(z : ℂ) * (z : ℂ)⁻¹) * X := by rw [map_mul]; ring
    _ = X - C (z : ℂ) := by rw [hz, map_neg, map_neg, map_one]; ring

/-- Spectra whose standard Hecke scalars satisfy the adjoint relation are inverse. -/
theorem eq_map_inv_of_standardHeckeScalar (s s' : Eigenvalues (r + 1))
    (h : ∀ j, standardHeckeScalar F s' j =
      standardHeckeScalar F s' (Fin.last (r + 1)) * standardHeckeScalar F s j.rev) :
    s' = s.map fun z => z⁻¹ := by
  apply Eigenvalues.eulerPolynomial_injective
  set P := Eigenvalues.eulerPolynomial s with hP
  set P' := Eigenvalues.eulerPolynomial s' with hP'
  set c' := P'.coeff (r + 1)
  set A : ℂ := (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) with hAdef
  have hA : A ≠ 0 := by
    have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
      exact_mod_cast Nat.zero_lt_of_lt F.canonicalTopologicalData.residueCardinality_gt_one
    rw [hAdef]
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hcoef : ∀ j : ℕ, j ≤ r + 1 → P'.coeff j = c' * P.coeff (r + 1 - j) := by
    intro j hj
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hj
    have hj' : j < r + 2 := by omega
    have e2 : r + 1 - j = m := by omega
    have h1 : A ^ (j * m) * ((-1) ^ j * P'.coeff j) =
        ((-1) ^ (r + 1) * c') * (A ^ (j * m) * ((-1) ^ m * P.coeff m)) := by
      have h0 := h ⟨j, hj'⟩
      simp only [standardHeckeScalar, elementaryCoefficient, Fin.val_last, Fin.val_rev,
        Nat.sub_self, mul_zero, pow_zero, one_mul] at h0
      rw [show r + 2 - (j + 1) = m by omega, show r + 1 - m = j by omega, e2,
        Nat.mul_comm m j] at h0
      exact h0
    rw [e2]
    have hs : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow]
      norm_num
    have hr : (-1 : ℂ) ^ (r + 1) = (-1) ^ j * (-1) ^ m := by rw [hm, pow_add]
    rw [hr] at h1
    have h2 : (A ^ (j * m) * (-1) ^ j) * P'.coeff j =
        (A ^ (j * m) * (-1) ^ j) * (c' * P.coeff m) := by
      linear_combination h1 + A ^ (j * m) * (-1) ^ j * c' * P.coeff m * hs
    exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ (by norm_num))) h2
  have hrev : P' = C c' * P.reverse := by
    ext j
    rw [coeff_C_mul, coeff_reverse, hP, Eigenvalues.eulerPolynomial_natDegree, ← hP]
    by_cases hj : j ≤ r + 1
    · rw [revAt_le hj]
      exact hcoef j hj
    · have hj' : r + 1 < j := by omega
      rw [revAt_eq_self_of_lt hj', coeff_eq_zero_of_natDegree_lt (by
          rw [hP', Eigenvalues.eulerPolynomial_natDegree]; exact hj'),
        coeff_eq_zero_of_natDegree_lt (by
          rw [hP, Eigenvalues.eulerPolynomial_natDegree]; exact hj'), mul_zero]
  have hQ := C_mul_eulerPolynomial_map_inv s
  set d := ((s : Multiset ℂˣ).map fun z : ℂˣ => -(z : ℂ)).prod
  rw [← hP] at hQ
  rw [← hQ, ← mul_assoc, ← map_mul] at hrev
  have h0 : c' * d = 1 := by
    have e := congrArg (fun f : ℂ[X] => f.coeff 0) hrev
    simp only [coeff_zero_eq_eval_zero, hP', eval_mul, eval_C,
      Eigenvalues.eulerPolynomial_eval_zero, mul_one] at e
    exact e.symm
  rw [hrev, h0, map_one, one_mul]

end Polynomial

/-- Invariantly paired spherical eigenvectors of the standard Hecke elements have inverse
spectra. -/
theorem eq_map_inv_of_pairing (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hσ : IsSmooth σ) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB : ∀ g x y, B (ρ g x) (σ g y) = B x y)
    (a : fixedVectors ρ (sphericalOpenSubgroup F r).toSubgroup)
    (b : fixedVectors σ (sphericalOpenSubgroup F r).toSubgroup) (s s' : Eigenvalues (r + 1))
    (ha : ∀ i, corner F ρ hρ (standardHeckeElement F r i) a = standardHeckeScalar F s i • a)
    (hb : ∀ i, corner F σ hσ (standardHeckeElement F r i) b = standardHeckeScalar F s' i • b)
    (hab : B a b ≠ 0) :
    s' = s.map fun z => z⁻¹ :=
  eq_map_inv_of_standardHeckeScalar F s s'
    (scalar_adjoint F ρ hρ σ hσ B hB a b _ _ ha hb hab)

end PairedHecke

end Langlands.Unramified
