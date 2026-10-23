import Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
import Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
import Langlands.Representation.Hecke.CornerAction
import Langlands.Algebra.SandwichDimensionBoundStatement
import Langlands.Algebra.SeparatedMatrixRepresentations
import Langlands.Representation.Smooth.SmallRealizationProof

/-!
# Fixed-level finiteness of compact-coefficient classes from a corner dimension bound

Bernstein--Zelevinsky (1976), 4.16, page 41, for an arbitrary topological group `G` with
a left Haar measure and a compact open subgroup `N`. For a class with compact smooth-dual
coefficients and a nonzero `N`-fixed vector, the fixed space is finite-dimensional and
simple over the corner `H_N`, and some element of `H_N` acts nontrivially on it and
trivially on the fixed space of every other such class. A uniform bound on the
dimensions of finite-dimensional simple `H_N`-modules, together with finite generation
of `H_N`, then gives finiteness of the fixed-level stratum.
-/

noncomputable section

namespace Langlands.CompactCoefficientClass

open MeasureTheory ComplexConjugate Hecke
open HarmonicAnalysis (SchwartzBruhat)

universe uG uV uW

section CornerSimple

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (N : OpenSubgroup G) (hN : IsCompact (N : Set G))

/-- The projection to `N`-fixed vectors of a translate `ρ g w` of an `N`-fixed vector `w`
is obtained from `w` by the corner action. -/
theorem exists_cornerAction_eq_fixedProjection (w : fixedVectors ρ N.toSubgroup) (g : G) :
    ∃ f : HeckeAlgebra.Corner μ N hN,
      cornerAction μ ρ hρ N hN f w = fixedProjection μ ρ hρ N hN (ρ g w) := by
  refine ⟨HeckeAlgebra.Corner.project μ N hN ((HeckeAlgebra.toTestFunction μ).symm
    (TestFunction.leftTranslate g
      (HeckeAlgebra.toTestFunction μ (HeckeAlgebra.normalizedIndicator μ N hN)))), ?_⟩
  rw [cornerAction_project, heckeAction_apply, LinearEquiv.apply_symm_apply,
    integratedAction_leftTranslate, ← heckeAction_apply,
    heckeAction_normalizedIndicator_of_fixed μ ρ hρ N hN w.property]

include μ hρ hN in
/-- Bernstein--Zelevinsky (1976), 2.10: the nonzero `N`-fixed vectors of an irreducible
smooth representation form a simple module over the corner `H_N`. -/
theorem isSimpleModule_fixedVectors (hirr : ρ.IsIrreducible)
    (h0 : fixedVectors ρ N.toSubgroup ≠ ⊥) :
    letI := cornerModule μ ρ hρ N hN
    IsSimpleModule (HeckeAlgebra.Corner μ N hN) (fixedVectors ρ N.toSubgroup) := by
  let _ := cornerModule μ ρ hρ N hN
  rw [isSimpleModule_iff_toSpanSingleton_surjective]
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr h0, fun w hw v => ?_⟩
  let Φ : HeckeAlgebra.Corner μ N hN →ₗ[ℂ] fixedVectors ρ N.toSubgroup :=
    LinearMap.applyₗ w ∘ₗ (cornerAction μ ρ hρ N hN).toLinearMap
  let S : Submodule ℂ V := (LinearMap.range Φ).comap (fixedProjection μ ρ hρ N hN)
  have hw0 : (w : V) ≠ 0 := fun h => hw (Subtype.ext h)
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← span_range_orbit_eq_top hirr hw0, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    obtain ⟨f, hf⟩ := exists_cornerAction_eq_fixedProjection μ ρ hρ N hN w g
    exact ⟨f, hf⟩
  have hv : (v : V) ∈ S := hS ▸ Submodule.mem_top
  obtain ⟨f, hf⟩ := hv
  refine ⟨f, ?_⟩
  rw [LinearMap.toSpanSingleton_apply, cornerModule_smul]
  rw [fixedProjection_fixed] at hf
  exact hf

end CornerSimple

section Separation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [IsTopologicalGroup G] in
/-- A continuous compactly supported function that is nonzero somewhere has a nonzero
integral of its squared modulus. -/
theorem integral_mul_conj_ne_zero {φ : G → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {x : G} (hx : φ x ≠ 0) :
    ∫ g, φ g * conj (φ g) ∂μ ≠ 0 := by
  have hpt : (fun g => φ g * conj (φ g)) = fun g => ((Complex.normSq (φ g) : ℝ) : ℂ) := by
    funext g
    rw [Complex.mul_conj]
  rw [hpt, integral_complex_ofReal, Complex.ofReal_ne_zero]
  exact (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (Complex.continuous_normSq.comp hφ) (hφc.comp_left Complex.normSq_zero)
    (fun g => Complex.normSq_nonneg (φ g)) (Complex.normSq_pos.mpr hx).ne').ne'

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- A functional invariant under a compact open subgroup is a smooth dual vector. -/
theorem isSmoothVector_dual_of_invariant (ρ : Representation ℂ G V) (N : OpenSubgroup G)
    {Λ : Module.Dual ℂ V} (hΛ : ∀ k ∈ N, ∀ y, Λ (ρ k y) = Λ y) :
    IsSmoothVector ρ.dual Λ := by
  refine ⟨N, fun k => ?_⟩
  apply LinearMap.ext
  intro y
  change Λ (ρ ((k : G)⁻¹) y) = Λ y
  exact hΛ _ (N.toSubgroup.inv_mem k.property) y

variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
  (hc : HasCompactSmoothDualCoefficients ρ) (ℓ : Module.Dual ℂ V)
  (hℓ : IsSmoothVector ρ.dual ℓ)

include hρ hc hℓ in
theorem invariantForm_integrable (x y : V) :
    Integrable (fun g => ℓ (ρ g⁻¹ x) * conj (ℓ (ρ g⁻¹ y))) μ :=
  ((inverseCoefficient ρ hρ hc ℓ hℓ x).continuous.mul
    (Complex.continuous_conj.comp (inverseCoefficient ρ hρ hc ℓ hℓ y).continuous)).integrable_of_hasCompactSupport
    (inverseCoefficient ρ hρ hc ℓ hℓ x).hasCompactSupport.mul_right

/-- The left-invariant Hermitian form `⟨x, y⟩ = ∫ ℓ (ρ g⁻¹ x) * conj (ℓ (ρ g⁻¹ y)) dμ(g)`
attached to a smooth functional `ℓ`, as the linear functional `x ↦ ⟨x, y⟩`. -/
def invariantForm (y : V) : Module.Dual ℂ V where
  toFun x := ∫ g, ℓ (ρ g⁻¹ x) * conj (ℓ (ρ g⁻¹ y)) ∂μ
  map_add' x z := by
    simp only [map_add, add_mul]
    exact integral_add (invariantForm_integrable μ ρ hρ hc ℓ hℓ x y)
      (invariantForm_integrable μ ρ hρ hc ℓ hℓ z y)
  map_smul' c x := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul _ _

theorem invariantForm_apply (x y : V) :
    invariantForm μ ρ hρ hc ℓ hℓ y x = ∫ g, ℓ (ρ g⁻¹ x) * conj (ℓ (ρ g⁻¹ y)) ∂μ := rfl

/-- The form is invariant under `G`, by left invariance of `μ`. -/
theorem invariantForm_rho (h : G) (x y : V) :
    invariantForm μ ρ hρ hc ℓ hℓ (ρ h y) (ρ h x) = invariantForm μ ρ hρ hc ℓ hℓ y x := by
  rw [invariantForm_apply, invariantForm_apply]
  have hpt : ∀ g : G, ρ g⁻¹ (ρ h x) = ρ (h⁻¹ * g)⁻¹ x := fun g => by
    rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
  have hpt' : ∀ g : G, ρ g⁻¹ (ρ h y) = ρ (h⁻¹ * g)⁻¹ y := fun g => by
    rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
  simp only [hpt, hpt']
  exact integral_mul_left_eq_self (fun g => ℓ (ρ g⁻¹ x) * conj (ℓ (ρ g⁻¹ y))) h⁻¹

/-- The form is Hermitian. -/
theorem invariantForm_conj (x y : V) :
    invariantForm μ ρ hρ hc ℓ hℓ x y = conj (invariantForm μ ρ hρ hc ℓ hℓ y x) := by
  rw [invariantForm_apply, invariantForm_apply, ← integral_conj]
  congr 1
  funext g
  rw [map_mul, Complex.conj_conj, mul_comm]

/-- The form is positive on a vector on which `ℓ` does not vanish. -/
theorem invariantForm_self_ne_zero {v : V} (hv : ℓ v ≠ 0) :
    invariantForm μ ρ hρ hc ℓ hℓ v v ≠ 0 := by
  rw [invariantForm_apply]
  refine integral_mul_conj_ne_zero μ (inverseCoefficient ρ hρ hc ℓ hℓ v).continuous
    (inverseCoefficient ρ hρ hc ℓ hℓ v).hasCompactSupport (x := 1) ?_
  rwa [inv_one, map_one, Module.End.one_apply]

end Separation

section SeparatingElement

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable (N : OpenSubgroup G) (hN : IsCompact (N : Set G))

/-- Bernstein--Zelevinsky (1976), 4.16: for a class with a nonzero `N`-fixed vector there is
an element of the corner `H_N` acting nontrivially on its `N`-fixed vectors and trivially
on the `N`-fixed vectors of every other class. -/
theorem exists_separating_corner_element (D : IrreducibleCompactCoefficientRep.{uG, uV} G)
    (hD : fixedVectors D.obj.representation N.toSubgroup ≠ ⊥) :
    ∃ f : HeckeAlgebra.Corner μ N hN,
      cornerAction μ D.obj.representation D.obj.isSmooth N hN f ≠ 0 ∧
      ∀ E : IrreducibleCompactCoefficientRep.{uG, uV} G, ofRep D ≠ ofRep E →
        cornerAction μ E.obj.representation E.obj.isSmooth N hN f = 0 := by
  classical
  let ρ := D.obj.representation
  have hρ : IsSmooth ρ := D.obj.isSmooth
  have hc : HasCompactSmoothDualCoefficients ρ := D.property.2
  obtain ⟨v₀, hv₀N, hv₀⟩ := (Submodule.ne_bot_iff _).mp hD
  have hex : ¬ ∀ ℓ₀ : Module.Dual ℂ D.obj, ℓ₀ v₀ = 0 := fun h =>
    hv₀ ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp h)
  obtain ⟨ℓ₀, hℓ₀⟩ := not_forall.mp hex
  let ℓ := dualAverage μ ρ hρ N hN ℓ₀
  have hℓ : IsSmoothVector ρ.dual ℓ := dualAverage_isSmoothVector μ ρ hρ N hN ℓ₀
  have hℓv : ℓ v₀ ≠ 0 := by
    rw [dualAverage_apply_of_fixed μ ρ hρ N hN ℓ₀ hv₀N]
    exact hℓ₀
  let Λ := invariantForm μ ρ hρ hc ℓ hℓ v₀
  have hΛN : ∀ k ∈ N, ∀ y, Λ (ρ k y) = Λ y := by
    intro k hk y
    change invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ k y) = invariantForm μ ρ hρ hc ℓ hℓ v₀ y
    conv_lhs => rw [← apply_eq_of_mem_fixedVectors hv₀N hk]
    exact invariantForm_rho μ ρ hρ hc ℓ hℓ k y v₀
  have hΛ : IsSmoothVector ρ.dual Λ := isSmoothVector_dual_of_invariant ρ N hΛN
  let φ := inverseCoefficient ρ hρ hc Λ hΛ v₀
  have hφ : φ ∈ TestFunction.biInvariant N.toSubgroup N.toSubgroup :=
    inverseCoefficient_mem_biInvariant hΛN hv₀N
  let f : HeckeAlgebra.Corner μ N hN := ⟨(HeckeAlgebra.toTestFunction μ).symm φ, hφ⟩
  have hφconj : ∀ g, Λ (ρ g v₀) = conj (φ g) := by
    intro g
    change invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ g v₀) =
      conj (invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ g⁻¹ v₀))
    rw [← invariantForm_rho μ ρ hρ hc ℓ hℓ g⁻¹ (ρ g v₀) v₀, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply, invariantForm_conj]
  refine ⟨f, fun hf => ?_, fun E hDE => ?_⟩
  · have h1 : (cornerAction μ ρ hρ N hN f ⟨v₀, hv₀N⟩ : D.obj) = 0 := by
      rw [hf]
      rfl
    rw [cornerAction_apply, heckeAction_apply] at h1
    have h2 := congrArg Λ h1
    rw [integratedAction_dual, map_zero] at h2
    refine integral_mul_conj_ne_zero μ φ.continuous φ.hasCompactSupport (x := 1) ?_ ?_
    · change invariantForm μ ρ hρ hc ℓ hℓ v₀ (ρ 1⁻¹ v₀) ≠ 0
      rw [inv_one, map_one, Module.End.one_apply]
      exact invariantForm_self_ne_zero μ ρ hρ hc ℓ hℓ hℓv
    · rw [← h2]
      congr 1
      funext g
      rw [hφconj]
      rfl
  · let σ := E.obj.representation
    have hσ : IsSmooth σ := E.obj.isSmooth
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [cornerAction_apply, heckeAction_apply]
    change integratedAction μ σ hσ φ w = 0
    let S : ρ.IntertwiningMap σ := LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ
      (LinearMap.applyₗ (w : E.obj) ∘ₗ integratedAction μ σ hσ ∘ₗ
        inverseCoefficient ρ hρ hc Λ hΛ)
      (fun h v => by
        simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]
        rw [inverseCoefficient_apply_rho, integratedAction_leftTranslate])
    have hS : S = 0 := intertwiningMap_eq_zero_of_ne hDE S
    exact congrArg (fun T : ρ.IntertwiningMap σ => T v₀) hS

end SeparatingElement

section Finiteness

/-- An algebra spanned by sandwich products `x i * m * x j`, with `m` in the subalgebra
generated by the `a k`, is generated by the `x i` together with the `a k`. -/
theorem adjoin_range_append_eq_top {R : Type*} [Ring R] [Algebra ℂ R] {q l : ℕ}
    (x : Fin q → R) (a : Fin l → R)
    (hspan : Submodule.span ℂ
      {y | ∃ i j, ∃ m ∈ Algebra.adjoin ℂ (Set.range a), y = x i * m * x j} = ⊤) :
    Algebra.adjoin ℂ (Set.range (Fin.append x a)) = ⊤ := by
  let A := Algebra.adjoin ℂ (Set.range (Fin.append x a))
  have hx : ∀ i, x i ∈ A := fun i =>
    Algebra.subset_adjoin ⟨Fin.castAdd l i, Fin.append_left x a i⟩
  have ha : Algebra.adjoin ℂ (Set.range a) ≤ A := by
    apply Algebra.adjoin_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨Fin.natAdd q k, Fin.append_right x a k⟩
  have hle : Submodule.span ℂ
      {y | ∃ i j, ∃ m ∈ Algebra.adjoin ℂ (Set.range a), y = x i * m * x j} ≤
        Subalgebra.toSubmodule A := by
    rw [Submodule.span_le]
    rintro _ ⟨i, j, m, hm, rfl⟩
    exact A.mul_mem (A.mul_mem (hx i) (ha hm)) (hx j)
  rw [eq_top_iff]
  intro r _
  have hr : r ∈ (⊤ : Submodule ℂ R) := Submodule.mem_top
  rw [← hspan] at hr
  exact hle hr

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
variable (N : OpenSubgroup G) (hN : IsCompact (N : Set G))

/-- Bernstein--Zelevinsky (1976), 4.16: if the corner `H_N` has a sandwich structure, then
the dimension bound for simple modules over sandwich algebras implies that only finitely
many compact-coefficient classes have a nonzero `N`-fixed vector. -/
theorem fixedStratum_finite_of_sandwich
    (hB : SandwichSimpleModuleDimensionBoundStatement.{uG, uV})
    {q l : ℕ} (x : Fin q → HeckeAlgebra.Corner μ N hN)
    (a : Fin l → HeckeAlgebra.Corner μ N hN) (ha : ∀ i j, Commute (a i) (a j))
    (hspan : Submodule.span ℂ
      {y | ∃ i j, ∃ m ∈ Algebra.adjoin ℂ (Set.range a), y = x i * m * x j} = ⊤) :
    (fixedStratum.{uG, uV} N.toSubgroup).Finite := by
  classical
  let S := fixedStratum.{uG, uV} (G := G) N.toSubgroup
  have hout : ∀ c : CompactCoefficientClass.{uG, uV} G, ofRep c.out = c := Quotient.out_eq
  have hfix : ∀ c ∈ S, fixedVectors c.out.obj.representation N.toSubgroup ≠ ⊥ := by
    intro c hc
    rw [← hasFixedVector_ofRep, hout]
    exact hc
  have hfd : ∀ c : CompactCoefficientClass.{uG, uV} G,
      FiniteDimensional ℂ (fixedVectors c.out.obj.representation N.toSubgroup) := fun c =>
    finiteDimensional_fixedVectors μ c.out.obj.representation c.out.obj.isSmooth N hN
      c.out.property.1 c.out.property.2
  let dim : CompactCoefficientClass.{uG, uV} G → ℕ := fun c =>
    Module.finrank ℂ (fixedVectors c.out.obj.representation N.toSubgroup)
  have hdim : ∀ c ∈ S, dim c ≤ q ^ (2 ^ l) := by
    intro c hc
    let _ := cornerModule μ c.out.obj.representation c.out.obj.isSmooth N hN
    have := cornerModule_isScalarTower μ c.out.obj.representation c.out.obj.isSmooth N hN
    exact hB (HeckeAlgebra.Corner μ N hN) q l x a ha hspan
      (fixedVectors c.out.obj.representation N.toSubgroup)
      (isSimpleModule_fixedVectors μ c.out.obj.representation c.out.obj.isSmooth N hN
        c.out.property.1 (hfix c hc)) (hfd c)
  have hgen := adjoin_range_append_eq_top x a hspan
  have hlevel : ∀ s : ℕ, {c | c ∈ S ∧ dim c = s}.Finite := by
    intro s
    let ι := {c // c ∈ S ∧ dim c = s}
    have hsep : ∀ i : ι, ∃ f : HeckeAlgebra.Corner μ N hN,
        cornerAction μ i.1.out.obj.representation i.1.out.obj.isSmooth N hN f ≠ 0 ∧
        ∀ E : IrreducibleCompactCoefficientRep.{uG, uV} G, ofRep i.1.out ≠ ofRep E →
          cornerAction μ E.obj.representation E.obj.isSmooth N hN f = 0 := fun i =>
      exists_separating_corner_element μ N hN i.1.out (hfix i.1 i.2.1)
    choose f hfself hfother using hsep
    let b : ∀ i : ι,
        Module.Basis (Fin s) ℂ (fixedVectors i.1.out.obj.representation N.toSubgroup) :=
      fun i => haveI := hfd i.1; Module.finBasisOfFinrankEq ℂ _ i.2.2
    let ψ : ι → HeckeAlgebra.Corner μ N hN →ₐ[ℂ] Matrix (Fin s) (Fin s) ℂ := fun i =>
      (LinearMap.toMatrixAlgEquiv (b i)).toAlgHom.comp
        (cornerAction μ i.1.out.obj.representation i.1.out.obj.isSmooth N hN)
    have : Finite ι := finite_of_separated_matrixRepresentations (Fin.append x a) hgen ψ f
      (fun i h => hfself i ((LinearMap.toMatrixAlgEquiv (b i)).injective (by
        rw [map_zero]
        exact h)))
      (fun i j hij => by
        have hne : ofRep i.1.out ≠ ofRep j.1.out := by
          rw [hout, hout]
          exact fun h => hij (Subtype.ext h)
        change LinearMap.toMatrixAlgEquiv (b j)
          (cornerAction μ j.1.out.obj.representation j.1.out.obj.isSmooth N hN (f i)) = 0
        rw [hfother i j.1.out hne, map_zero])
    exact Set.finite_coe_iff.mp this
  have hcover : S ⊆ ⋃ s ∈ Finset.range (q ^ (2 ^ l) + 1), {c | c ∈ S ∧ dim c = s} := by
    intro c hc
    simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq]
    exact ⟨dim c, Nat.lt_succ_of_le (hdim c hc), hc, rfl⟩
  exact (Set.Finite.biUnion (Finset.range _).finite_toSet fun s _ => hlevel s).subset hcover

end Finiteness

end Langlands.CompactCoefficientClass
