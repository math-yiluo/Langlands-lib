import Langlands.AlgebraicGeometry.DvrSmoothening.DefectTransport
import Langlands.AlgebraicGeometry.DvrSmoothening.DilatationDefectStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.DilatationRelations
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-! # The defect drops under the dilatation of a good centre -/

open scoped TensorProduct

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

section Blowup

open GroupScheme.Dilatation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (ϖ : R) (J : Ideal A)

/-- Every element of the centre is divisible by `ϖ` in the dilatation algebra. -/
theorem blowupAlgebra_exists_div {j : A} (hj : j ∈ J) :
    ∃ t : blowupAlgebra ϖ J, algebraMap R (blowupAlgebra ϖ J) ϖ * t =
      algebraMap A (blowupAlgebra ϖ J) j := by
  refine ⟨dividedElement (algebraMap R A ϖ) J ⟨j, hj⟩, ?_⟩
  rw [IsScalarTower.algebraMap_apply R A (blowupAlgebra ϖ J)]
  exact mul_dividedElement _ J ⟨j, hj⟩

/-- The dilatation algebra is generated over `A` by the quotients of elements of the centre by
`ϖ`. -/
theorem blowupAlgebra_adjoin_eq_top :
    Algebra.adjoin A {t : blowupAlgebra ϖ J | ∃ j ∈ J,
      algebraMap R (blowupAlgebra ϖ J) ϖ * t = algebraMap A (blowupAlgebra ϖ J) j} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  set S' := Algebra.adjoin A {t : blowupAlgebra ϖ J | ∃ j ∈ J,
    algebraMap R (blowupAlgebra ϖ J) ϖ * t = algebraMap A (blowupAlgebra ϖ J) j} with hS'
  have hle : coordinateAlgebra (algebraMap R A ϖ) J ≤
      S'.map (coordinateAlgebra (algebraMap R A ϖ) J).val := by
    rw [coordinateAlgebra_le_iff]
    intro f hf
    refine ⟨dividedElement (algebraMap R A ϖ) J ⟨f, hf⟩, Algebra.subset_adjoin ⟨f, hf, ?_⟩, rfl⟩
    rw [IsScalarTower.algebraMap_apply R A (blowupAlgebra ϖ J)]
    exact mul_dividedElement _ J ⟨f, hf⟩
  obtain ⟨x', hx', hxx'⟩ := hle x.2
  have : x' = x := Subtype.ext hxx'
  rw [← this]
  exact hx'

/-- The dilatation algebra has no `ϖ`-torsion. -/
theorem blowupAlgebra_eq_zero_of_mul (y : blowupAlgebra ϖ J)
    (hy : algebraMap R (blowupAlgebra ϖ J) ϖ * y = 0) : y = 0 := by
  apply Subtype.ext
  have h := congrArg Subtype.val hy
  have hu : IsUnit (algebraMap A (Localization.Away (algebraMap R A ϖ)) (algebraMap R A ϖ)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h' : algebraMap A (Localization.Away (algebraMap R A ϖ)) (algebraMap R A ϖ) *
      (y : Localization.Away (algebraMap R A ϖ)) = 0 := by
    rw [← IsScalarTower.algebraMap_apply]
    simpa using h
  simpa using (hu.mul_right_eq_zero).mp h'

/-- The kernel of `A → A[J/ϖ]` consists of `ϖ`-power torsion. -/
theorem blowupAlgebra_exists_pow_mul_eq_zero (a : A)
    (ha : algebraMap A (blowupAlgebra ϖ J) a = 0) :
    ∃ v : ℕ, algebraMap R A ϖ ^ v * a = 0 := by
  have h := congrArg Subtype.val ha
  have h' : algebraMap A (Localization.Away (algebraMap R A ϖ)) a = 0 := by simpa using h
  obtain ⟨⟨_, v, rfl⟩, hv⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap R A ϖ)) _ a).mp h'
  exact ⟨v, hv⟩

end Blowup

/-- **The defect drop for an abstract dilatation.** Let `A` be of finite type over a discrete
valuation ring and `J` a good centre as in `DilatationDefectStatement`. Let `A'` be an
`A`-algebra without `ϖ`-torsion in which every element of `J` becomes divisible by `ϖ`, generated
over `A` by the quotients `j / ϖ` of elements `j ∈ J`, such that the kernel of `A → A'` is
`ϖ`-power torsion. Then for every point `φ' : A' → R'` of
ramification index one lifting a point `φ` of `A` with positive defect whose closed point lies on
the centre, the defect of `φ'` is smaller than that of `φ`. -/
theorem pointDefect_lt_of_dilatation {R A A' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A] {ϖ : R}
    (hϖ : Irreducible ϖ) (J : Ideal A) (S : Set (Ideal A)) (hJ : J = sInf S)
    (hS : ∀ p ∈ S, ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'')
      (_ : IsDiscreteValuationRing R'') (_ : Algebra R R'') (_ : IsLocalHom (algebraMap R R''))
      (ψ : A →ₐ[R] R''), IsRamificationIndexOne R R'' ∧
        (IsLocalRing.maximalIdeal R'').comap ψ = p)
    (hB : Algebra.Smooth (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] (A ⧸ J)))
    (hfree : Module.Free (A ⧸ J) ((A ⧸ J) ⊗[A] Ω[A⁄R]))
    [CommRing A'] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (hdiv : ∀ j ∈ J, ∃ t : A', algebraMap R A' ϖ * t = algebraMap A A' j)
    (hgen : Algebra.adjoin A {t : A' | ∃ j ∈ J, algebraMap R A' ϖ * t = algebraMap A A' j} = ⊤)
    (htf : ∀ y : A', algebraMap R A' ϖ * y = 0 → y = 0)
    (hkerA : ∀ a : A, algebraMap A A' a = 0 → ∃ v : ℕ, algebraMap R A ϖ ^ v * a = 0)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')] (hram : IsRamificationIndexOne R R')
    (φ : A →ₐ[R] R') (hφJ : J ≤ (IsLocalRing.maximalIdeal R').comap φ)
    (φ' : A' →ₐ[R] R') (hφ' : φ'.comp (IsScalarTower.toAlgHom R A A') = φ)
    (hδ : pointDefect φ ≠ 0) :
    pointDefect φ' < pointDefect φ := by
  classical
  obtain ⟨N, π0, hπ0⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  letI : Algebra (MvPolynomial (Fin N) R) A := π0.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin N) R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (π0.commutes r).symm
  letI : Algebra A R' := φ.toRingHom.toAlgebra
  have : IsScalarTower R A R' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  letI : Algebra (MvPolynomial (Fin N) R) R' := (φ.toRingHom.comp π0.toRingHom).toAlgebra
  have : IsScalarTower (MvPolynomial (Fin N) R) A R' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R (MvPolynomial (Fin N) R) R' := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R R' r = φ (π0 (algebraMap R _ r))
    rw [π0.commutes, φ.commutes]
  have hJu : J ≤ (IsLocalRing.maximalIdeal R').comap (algebraMap A R') := hφJ
  obtain ⟨n, m, z, w, hw, hz, hliK, hI, hJgen⟩ :=
    exists_dilatation_relations hϖ J S hJ hS hB hfree (R' := R') hπ0 hJu
  have hT : Submodule.torsion R' (R' ⊗[A] Ω[A⁄R]) ≠ ⊥ := by
    intro h
    apply hδ
    change torsionLength R' (R' ⊗[A] Ω[A⁄R]) = 0
    exact torsionLength_eq_zero_iff.mpr h
  have hφ'a : ∀ a : A, φ' (algebraMap A A' a) = φ a := fun a => congrArg (· a) hφ'
  -- the prime of the closed point and the localized dilatation
  set u := (IsLocalRing.maximalIdeal R').comap (algebraMap A R') with hudef
  have : u.IsPrime := Ideal.comap_isPrime _ _
  have hunitA : ∀ a : A, a ∉ u → IsUnit (φ a) := fun a ha =>
    IsLocalRing.notMem_maximalIdeal.mp ha
  set Mu := Algebra.algebraMapSubmonoid A' u.primeCompl with hMudef
  have hMu : ∀ y : Mu, IsUnit (φ' y) := by
    rintro ⟨_, a, ha, rfl⟩
    rw [hφ'a]
    exact hunitA a ha
  let φ2 : Localization Mu →ₐ[R] R' := IsLocalization.liftAlgHom (M := Mu) hMu
  have hφ2 : ∀ x : A', φ2 (algebraMap A' (Localization Mu) x) = φ' x := fun x =>
    IsLocalization.lift_eq hMu x
  have hφ2comp : φ2.comp (IsScalarTower.toAlgHom R A' (Localization Mu)) = φ' :=
    AlgHom.ext hφ2
  have : Algebra.FormallyEtale A' (Localization Mu) := Algebra.FormallyEtale.of_isLocalization Mu
  have hδ' : pointDefect φ' = pointDefect φ2 := by
    rw [← hφ2comp]
    exact pointDefect_comp_formallyEtale φ2
  rw [hδ']
  -- the presentation of the localized dilatation
  set 𝔭 := u.comap (algebraMap (MvPolynomial (Fin N) R) A) with h𝔭def
  have : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  let ι0 : MvPolynomial (Fin N) R →ₐ[R] MvPolynomial (Fin N ⊕ Fin n) R :=
    MvPolynomial.rename Sum.inl
  let T : Submonoid (MvPolynomial (Fin N ⊕ Fin n) R) := 𝔭.primeCompl.map ι0
  letI : Algebra (MvPolynomial (Fin N) R) (Localization T) :=
    ((algebraMap (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T)).comp ι0.toRingHom).toAlgebra
  letI : SMul (MvPolynomial (Fin N) R) (Localization T) := Algebra.toSMul
  letI : Module (MvPolynomial (Fin N) R) (Localization T) := Algebra.toModule
  have hιP2 : ∀ p, algebraMap (MvPolynomial (Fin N) R) (Localization T) p =
      algebraMap (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T) (ι0 p) := fun _ => rfl
  have : IsScalarTower R (MvPolynomial (Fin N) R) (Localization T) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [hιP2, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  choose tA htA using fun j => hdiv _ (hz j)
  let t : Fin n → Localization Mu := fun j => algebraMap A' (Localization Mu) (tA j)
  let πQ : MvPolynomial (Fin N ⊕ Fin n) R →ₐ[R] Localization Mu :=
    MvPolynomial.aeval (Sum.elim (fun i => algebraMap A (Localization Mu) (π0 (MvPolynomial.X i))) t)
  have hπQι : ∀ p, πQ (ι0 p) = algebraMap A (Localization Mu) (π0 p) := by
    intro p
    have : (MvPolynomial.aeval (Sum.elim (fun i => algebraMap A (Localization Mu)
        (π0 (MvPolynomial.X i))) t ∘ Sum.inl) : MvPolynomial (Fin N) R →ₐ[R] Localization Mu) =
        (IsScalarTower.toAlgHom R A (Localization Mu)).comp π0 :=
      MvPolynomial.algHom_ext fun i => by simp
    simp only [πQ, ι0, MvPolynomial.aeval_rename]
    exact congrArg (· p) this
  have hπQX : ∀ j, πQ (MvPolynomial.X (Sum.inr j)) = t j := fun j => by
    simp [πQ]
  have hunitP : ∀ p : MvPolynomial (Fin N) R, p ∈ 𝔭.primeCompl →
      IsUnit (algebraMap (MvPolynomial (Fin N) R) R' p) := fun p hp => hunitA _ hp
  have hTunit : ∀ q : T, IsUnit (πQ q) := by
    rintro ⟨_, p, hp, rfl⟩
    change IsUnit (πQ (ι0 p))
    rw [hπQι, IsScalarTower.algebraMap_apply A A' (Localization Mu)]
    exact IsLocalization.map_units (Localization Mu) (⟨_, π0 p, hp, rfl⟩ : Mu)
  let π2 : Localization T →ₐ[R] Localization Mu := IsLocalization.liftAlgHom (M := T) hTunit
  have hπ2 : ∀ q, π2 (algebraMap _ (Localization T) q) = πQ q := fun q =>
    IsLocalization.lift_eq hTunit q
  letI : Algebra (Localization T) (Localization Mu) := π2.toRingHom.toAlgebra
  have : IsScalarTower R (Localization T) (Localization Mu) :=
    IsScalarTower.of_algebraMap_eq fun r => (π2.commutes r).symm
  letI : Algebra (MvPolynomial (Fin N) R) (Localization Mu) :=
    ((algebraMap A (Localization Mu)).comp (algebraMap (MvPolynomial (Fin N) R) A)).toAlgebra
  letI : SMul (MvPolynomial (Fin N) R) (Localization Mu) := Algebra.toSMul
  letI : Module (MvPolynomial (Fin N) R) (Localization Mu) := Algebra.toModule
  have : IsScalarTower (MvPolynomial (Fin N) R) (Localization T) (Localization Mu) :=
    IsScalarTower.of_algebraMap_eq fun p => by
      change algebraMap A (Localization Mu) (π0 p) = π2 (algebraMap _ (Localization T) (ι0 p))
      rw [hπ2, hπQι]
  letI : Algebra (Localization Mu) R' := φ2.toRingHom.toAlgebra
  letI : Algebra (Localization T) R' := (φ2.toRingHom.comp π2.toRingHom).toAlgebra
  have : IsScalarTower (Localization T) (Localization Mu) R' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (MvPolynomial (Fin N) R) (Localization T) R' :=
    IsScalarTower.of_algebraMap_eq fun p => by
      change φ (π0 p) = φ2 (π2 (algebraMap _ (Localization T) (ι0 p)))
      rw [hπ2, hπQι, IsScalarTower.algebraMap_apply A A' (Localization Mu), hφ2, hφ'a]
  -- the hypotheses of the presentation theorem
  have hϖ' : Irreducible (algebraMap R R' ϖ) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hram.1, hϖ.maximalIdeal_eq,
      Ideal.map_span, Set.image_singleton]
  have : Algebra.FormallyEtale (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T) :=
    Algebra.FormallyEtale.of_isLocalization T
  let e2 := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R
    (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T)
  let b2 := (Algebra.TensorProduct.basis (Localization T)
    (KaehlerDifferential.mvPolynomialBasis R (Fin N ⊕ Fin n))).map e2
  have hb2 : ∀ k, b2 k = KaehlerDifferential.D R (Localization T)
      (algebraMap (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T) (MvPolynomial.X k)) := by
    intro k
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.map_D]
    exact one_smul (Localization T) (KaehlerDifferential.D R (Localization T)
      (algebraMap (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T) (MvPolynomial.X k)))
  let X2 : Fin n → Localization T := fun j =>
    algebraMap (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T) (MvPolynomial.X (Sum.inr j))
  have hb : ∀ i, KaehlerDifferential.map R R (MvPolynomial (Fin N) R) (Localization T)
      (KaehlerDifferential.mvPolynomialBasis R (Fin N) i) = b2 (Sum.inl i) := by
    intro i
    rw [KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D, hb2, hιP2]
    simp [ι0]
  have hbX : ∀ j, b2 (Sum.inr j) = KaehlerDifferential.D R (Localization T) (X2 j) :=
    fun j => hb2 _
  have hϖA2 : ∀ y : Localization Mu, ϖ • y =
      algebraMap A' (Localization Mu) (algebraMap R A' ϖ) * y := fun y => by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  have hX : ∀ j, algebraMap (Localization T) (Localization Mu)
      (algebraMap (MvPolynomial (Fin N) R) (Localization T) (z j) - ϖ • X2 j) = 0 := by
    intro j
    rw [map_sub, ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin N) R) (Localization T)
      (Localization Mu), Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply R (Localization T) (Localization Mu)]
    change algebraMap A (Localization Mu) (π0 (z j)) -
      algebraMap R (Localization Mu) ϖ * π2 (X2 j) = 0
    rw [hπ2, hπQX, IsScalarTower.algebraMap_apply R A' (Localization Mu), ← map_mul, htA,
      ← IsScalarTower.algebraMap_apply]
    exact sub_eq_zero.mpr rfl
  have hfac : ∀ f, algebraMap (MvPolynomial (Fin N) R) A f = 0 →
      algebraMap (MvPolynomial (Fin N) R) (Localization Mu) f = 0 := fun f hf => by
    change algebraMap A (Localization Mu) (algebraMap _ A f) = 0
    rw [hf, map_zero]
  have htf2 : ∀ y : Localization Mu, ϖ • y = 0 → y = 0 := by
    intro y hy
    obtain ⟨⟨x, m⟩, rfl⟩ := IsLocalization.mk'_surjective Mu y
    change ϖ • IsLocalization.mk' (Localization Mu) x m = 0 at hy
    rw [hϖA2, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨c, hc⟩ := hy
    have : (c : A') * x = 0 := htf _ (by rw [mul_left_comm]; exact hc)
    change IsLocalization.mk' (Localization Mu) x m = 0
    exact (IsLocalization.mk'_eq_zero_iff x m).mpr ⟨c, this⟩
  have hker2 : ∀ c : MvPolynomial (Fin N) R,
      algebraMap (MvPolynomial (Fin N) R) (Localization Mu) c = 0 →
      ∃ e, IsUnit (algebraMap (MvPolynomial (Fin N) R) R' e) ∧
        ∃ v : ℕ, algebraMap (MvPolynomial (Fin N) R) A (ϖ ^ v • (e * c)) = 0 := by
    intro c hc
    change algebraMap A (Localization Mu) (π0 c) = 0 at hc
    rw [IsScalarTower.algebraMap_apply A A' (Localization Mu),
      IsLocalization.map_eq_zero_iff Mu] at hc
    obtain ⟨⟨_, a, ha, rfl⟩, hac⟩ := hc
    obtain ⟨v, hv⟩ := hkerA (a * π0 c) (by rw [map_mul]; exact hac)
    obtain ⟨e, rfl⟩ := hπ0 a
    refine ⟨e, hunitP e ha, v, ?_⟩
    change π0 (ϖ ^ v • (e * c)) = 0
    rw [map_smul, map_mul, Algebra.smul_def, map_pow]
    exact hv
  have hgen2 : ∀ g : Localization T, ∃ e : MvPolynomial (Fin N) R,
      IsUnit (algebraMap (MvPolynomial (Fin N) R) R' e) ∧ ∃ (v : ℕ) (c : MvPolynomial (Fin N) R),
        ϖ ^ v • (algebraMap (MvPolynomial (Fin N) R) (Localization T) e * g) -
          algebraMap (MvPolynomial (Fin N) R) (Localization T) c ∈
          Ideal.span (Set.range fun j =>
            algebraMap (MvPolynomial (Fin N) R) (Localization T) (z j) - ϖ • X2 j) := by
    set K2 := Ideal.span (Set.range fun j =>
      algebraMap (MvPolynomial (Fin N) R) (Localization T) (z j) - ϖ • X2 j) with hK2
    have key : ∀ q : MvPolynomial (Fin N ⊕ Fin n) R, ∃ (v : ℕ) (c : MvPolynomial (Fin N) R),
        ϖ ^ v • algebraMap _ (Localization T) q -
          algebraMap (MvPolynomial (Fin N) R) (Localization T) c ∈ K2 := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C r =>
        refine ⟨0, MvPolynomial.C r, ?_⟩
        rw [pow_zero, one_smul, hιP2]
        simp [ι0]
      | add p q hp hq =>
        obtain ⟨v₁, c₁, h₁⟩ := hp
        obtain ⟨v₂, c₂, h₂⟩ := hq
        refine ⟨v₁ + v₂, ϖ ^ v₂ • c₁ + ϖ ^ v₁ • c₂, ?_⟩
        have : ϖ ^ (v₁ + v₂) • algebraMap _ (Localization T) (p + q) -
            algebraMap (MvPolynomial (Fin N) R) (Localization T) (ϖ ^ v₂ • c₁ + ϖ ^ v₁ • c₂) =
            algebraMap R (Localization T) (ϖ ^ v₂) * (ϖ ^ v₁ • algebraMap _ (Localization T) p -
              algebraMap (MvPolynomial (Fin N) R) (Localization T) c₁) +
            algebraMap R (Localization T) (ϖ ^ v₁) * (ϖ ^ v₂ • algebraMap _ (Localization T) q -
              algebraMap (MvPolynomial (Fin N) R) (Localization T) c₂) := by
          simp only [Algebra.smul_def, map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
          ring
        rw [this]
        exact K2.add_mem (K2.mul_mem_left _ h₁) (K2.mul_mem_left _ h₂)
      | mul_X p k hp =>
        obtain ⟨v, c, h⟩ := hp
        rcases k with i | j
        · refine ⟨v, c * MvPolynomial.X i, ?_⟩
          have : ϖ ^ v • algebraMap _ (Localization T) (p * MvPolynomial.X (Sum.inl i)) -
              algebraMap (MvPolynomial (Fin N) R) (Localization T) (c * MvPolynomial.X i) =
              (ϖ ^ v • algebraMap _ (Localization T) p -
                algebraMap (MvPolynomial (Fin N) R) (Localization T) c) *
              algebraMap (MvPolynomial (Fin N ⊕ Fin n) R) (Localization T)
                (MvPolynomial.X (Sum.inl i)) := by
            rw [map_mul, map_mul, hιP2 (MvPolynomial.X i)]
            simp only [ι0, MvPolynomial.rename_X, Algebra.smul_def]
            ring
          rw [this]
          exact K2.mul_mem_right _ h
        · refine ⟨v + 1, c * z j, ?_⟩
          have hmemj : algebraMap (MvPolynomial (Fin N) R) (Localization T) (z j) - ϖ • X2 j ∈ K2 :=
            Ideal.subset_span ⟨j, rfl⟩
          have : ϖ ^ (v + 1) • algebraMap _ (Localization T) (p * MvPolynomial.X (Sum.inr j)) -
              algebraMap (MvPolynomial (Fin N) R) (Localization T) (c * z j) =
              (ϖ ^ v • algebraMap _ (Localization T) p -
                algebraMap (MvPolynomial (Fin N) R) (Localization T) c) * (ϖ • X2 j) -
              algebraMap (MvPolynomial (Fin N) R) (Localization T) c *
                (algebraMap (MvPolynomial (Fin N) R) (Localization T) (z j) - ϖ • X2 j) := by
            simp only [X2, Algebra.smul_def, map_mul, map_pow]
            ring
          rw [this]
          exact K2.sub_mem (K2.mul_mem_right _ h) (K2.mul_mem_left _ hmemj)
    intro g
    obtain ⟨⟨q, ⟨_, p0, hp0, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective T g
    dsimp only
    obtain ⟨v, c, hc⟩ := key q
    refine ⟨p0, hunitP p0 hp0, v, c, ?_⟩
    have : algebraMap (MvPolynomial (Fin N) R) (Localization T) p0 *
        IsLocalization.mk' (Localization T) q (⟨ι0 p0, p0, hp0, rfl⟩ : T) =
        algebraMap _ (Localization T) q := by
      rw [hιP2, mul_comm]
      exact IsLocalization.mk'_spec (Localization T) q _
    rw [this]
    exact hc
  have hsurj2 : Function.Surjective (algebraMap (Localization T) (Localization Mu)) := by
    -- every element of `A'` is in the image of `A[t]` up to a unit-valued multiplier
    have hclaim : ∀ x : A', ∃ s : MvPolynomial (Fin N) R, s ∈ 𝔭.primeCompl ∧
        ∃ q : MvPolynomial (Fin N ⊕ Fin n) R,
          algebraMap A (Localization Mu) (π0 s) * algebraMap A' (Localization Mu) x = πQ q := by
      intro x
      have hx : x ∈ Algebra.adjoin A {t : A' | ∃ j ∈ J,
          algebraMap R A' ϖ * t = algebraMap A A' j} := hgen ▸ Algebra.mem_top
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨j, hj, hxj⟩ := hx
        obtain ⟨e, he, hej⟩ := hJgen j hj
        obtain ⟨b, hb, r, hr, hbr⟩ := Submodule.mem_sup.mp hej
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hb
        obtain ⟨bz, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hr
        have he' : e ∈ 𝔭.primeCompl := fun h => (IsLocalRing.mem_maximalIdeal _).mp h he
        refine ⟨e, he', ?_⟩
        obtain ⟨a', rfl⟩ := hπ0 a
        choose bz' hbz' using fun i => hπ0 (bz i)
        refine ⟨ι0 a' + ∑ i, ι0 (bz' i) * MvPolynomial.X (Sum.inr i), ?_⟩
        have htA' : ∀ i, algebraMap R A' ϖ * tA i = algebraMap A A' (π0 (z i)) := htA
        have hbr' : π0 a' * algebraMap R A ϖ + ∑ i, bz i * π0 (z i) = π0 e * j := hbr
        have hA' : algebraMap A A' (π0 e) * x =
            algebraMap A A' (π0 a') + ∑ i, algebraMap A A' (bz i) * tA i := by
          apply eq_of_sub_eq_zero
          apply htf
          have e1 : algebraMap R A' ϖ * (algebraMap A A' (π0 e) * x) =
              algebraMap A A' (π0 e * j) := by rw [map_mul, ← hxj]; ring
          have e2 : ∀ i, algebraMap R A' ϖ * (algebraMap A A' (bz i) * tA i) =
              algebraMap A A' (bz i * π0 (z i)) := fun i => by
            rw [map_mul, ← htA' i]; ring
          have e3 : algebraMap R A' ϖ * algebraMap A A' (π0 a') =
              algebraMap A A' (π0 a' * algebraMap R A ϖ) := by
            rw [map_mul, ← IsScalarTower.algebraMap_apply]; ring
          rw [mul_sub, mul_add, Finset.mul_sum, e1, e3, Finset.sum_congr rfl fun i _ => e2 i,
            ← map_sum, ← map_add, hbr', sub_self]
        rw [IsScalarTower.algebraMap_apply A A' (Localization Mu) (π0 e), ← map_mul, hA', map_add,
          map_sum, map_add, map_sum, hπQι, ← IsScalarTower.algebraMap_apply]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, map_mul, hπQι, hπQX, hbz', ← IsScalarTower.algebraMap_apply]
      | algebraMap a =>
        obtain ⟨a', rfl⟩ := hπ0 a
        refine ⟨1, 𝔭.primeCompl.one_mem, ι0 a', ?_⟩
        rw [hπQι, map_one, map_one, one_mul, ← IsScalarTower.algebraMap_apply]
      | add x y _ _ hx hy =>
        obtain ⟨s₁, hs₁, q₁, hq₁⟩ := hx
        obtain ⟨s₂, hs₂, q₂, hq₂⟩ := hy
        refine ⟨s₁ * s₂, 𝔭.primeCompl.mul_mem hs₁ hs₂, ι0 s₂ * q₁ + ι0 s₁ * q₂, ?_⟩
        have : πQ (ι0 s₂ * q₁ + ι0 s₁ * q₂) = πQ (ι0 s₂) * πQ q₁ + πQ (ι0 s₁) * πQ q₂ := by
          rw [map_add, map_mul, map_mul]
        rw [this, hπQι, hπQι, ← hq₁, ← hq₂]
        simp only [map_mul, map_add]
        ring
      | mul x y _ _ hx hy =>
        obtain ⟨s₁, hs₁, q₁, hq₁⟩ := hx
        obtain ⟨s₂, hs₂, q₂, hq₂⟩ := hy
        refine ⟨s₁ * s₂, 𝔭.primeCompl.mul_mem hs₁ hs₂, q₁ * q₂, ?_⟩
        rw [show πQ (q₁ * q₂) = πQ q₁ * πQ q₂ from map_mul _ _ _, ← hq₁, ← hq₂]
        simp only [map_mul]
        ring
    intro y
    obtain ⟨⟨x, ⟨_, a, ha, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective Mu y
    dsimp only
    obtain ⟨s, hs, q, hq⟩ := hclaim x
    obtain ⟨a', rfl⟩ := hπ0 a
    have hmem : s * a' ∈ 𝔭.primeCompl := 𝔭.primeCompl.mul_mem hs ha
    refine ⟨IsLocalization.mk' (Localization T) q (⟨ι0 (s * a'), s * a', hmem, rfl⟩ : T), ?_⟩
    change π2 _ = _
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
    change πQ q = πQ (ι0 (s * a')) * _
    rw [hπQι, ← hq, map_mul, map_mul, mul_assoc]
    congr 1
    rw [IsScalarTower.algebraMap_apply A A' (Localization Mu)]
    exact (IsLocalization.mk'_spec' (Localization Mu) x _).symm
  have hli : LinearIndependent (IsLocalRing.ResidueField R')
      (fun k => (1 : IsLocalRing.ResidueField R') ⊗ₜ[R']
        ((1 : R') ⊗ₜ[MvPolynomial (Fin N) R]
          KaehlerDifferential.D R (MvPolynomial (Fin N) R) (Sum.elim z w k))) := by
    let cb := TensorProduct.AlgebraTensorModule.cancelBaseChange (MvPolynomial (Fin N) R) R'
      (IsLocalRing.ResidueField R') (IsLocalRing.ResidueField R') Ω[MvPolynomial (Fin N) R⁄R]
    convert hliK.map' cb.symm.toLinearMap (LinearEquiv.ker _) using 1
    funext k
    simp [cb, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  have key := torsionLength_lt_of_dilatationPresentation (R := R) (ϖ := ϖ) (R' := R')
    (P := MvPolynomial (Fin N) R) (A := A) (P2 := Localization T) (A2 := Localization Mu)
    hϖ' hπ0 hsurj2 (KaehlerDifferential.mvPolynomialBasis R (Fin N)) b2 hb X2 hbX z w hw hX
    hfac htf2 hI hgen2 hker2 hli hT
  exact key

/-- **BLR §3.3, Proposition 5, for points of ramification index one.** The dilatation of a good
centre lowers the defect of every point of ramification index one with positive defect whose
closed point lies on the centre. -/
theorem dilatationDefectStatement : DilatationDefectStatement.{u} := by
  intro R A _ _ _ _ _ _ ϖ hϖ _ J S hJ hS hB hfree R' _ _ _ _ _ hram φ hφJ φ' hφ' hδ
  exact pointDefect_lt_of_dilatation hϖ J S hJ hS hB hfree
    (fun j hj => blowupAlgebra_exists_div ϖ J hj) (blowupAlgebra_adjoin_eq_top ϖ J)
    (blowupAlgebra_eq_zero_of_mul ϖ J) (blowupAlgebra_exists_pow_mul_eq_zero ϖ J) R' hram φ hφJ
    φ' hφ' hδ

end Langlands.AlgebraicGeometry.DvrSmoothening
