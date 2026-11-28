import Langlands.AlgebraicGeometry.DvrSmoothening.DilatationLattice
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Free

/-! # The defect drop for a dilatation, in terms of presentations -/

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.DvrSmoothening

open Module Submodule

section KaehlerPoint

variable (R : Type*) {P S : Type*} (L : Type*) [CommRing R] [CommRing P] [CommRing S]
  [CommRing L] [Algebra R P] [Algebra R S] [Algebra P S] [IsScalarTower R P S]
  [Algebra S L] [Algebra P L] [IsScalarTower P S L]

/-- The map `L ⊗_P Ω_{P/R} → L ⊗_S Ω_{S/R}` induced by an algebra map `P → S`. -/
noncomputable def tensorKaehlerMap : L ⊗[P] Ω[P⁄R] →ₗ[L] L ⊗[S] Ω[S⁄R] :=
  TensorProduct.AlgebraTensorModule.lTensor L L (KaehlerDifferential.mapBaseChange R P S) ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P S L L Ω[P⁄R]).symm.toLinearMap

theorem tensorKaehlerMap_tmul (l : L) (ω : Ω[P⁄R]) :
    tensorKaehlerMap R L (l ⊗ₜ[P] ω) = l ⊗ₜ[S] KaehlerDifferential.map R R P S ω := by
  simp [tensorKaehlerMap, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]

theorem tensorKaehlerMap_tmul_D (l : L) (p : P) :
    tensorKaehlerMap R L (l ⊗ₜ[P] KaehlerDifferential.D R P p) =
      l ⊗ₜ[S] KaehlerDifferential.D R S (algebraMap P S p) := by
  rw [tensorKaehlerMap_tmul, KaehlerDifferential.map_D]

theorem tensorKaehlerMap_surjective (hsurj : Function.Surjective (algebraMap P S)) :
    Function.Surjective (tensorKaehlerMap R L (P := P) (S := S)) := by
  intro y
  obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective L
    (KaehlerDifferential.mapBaseChange_surjective R P S hsurj) y
  exact ⟨TensorProduct.AlgebraTensorModule.cancelBaseChange P S L L Ω[P⁄R] z,
    by simp [tensorKaehlerMap]⟩

/-- The kernel of `L ⊗_P Ω_{P/R} → L ⊗_S Ω_{S/R}` for a surjection `P → S` is spanned by the
differentials of the elements of the kernel of `P → S`. -/
theorem ker_tensorKaehlerMap (hsurj : Function.Surjective (algebraMap P S)) :
    LinearMap.ker (tensorKaehlerMap R L (P := P) (S := S)) =
      span L (Set.range fun g : RingHom.ker (algebraMap P S) =>
        (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (g : P)) := by
  classical
  set W := span L (Set.range fun g : RingHom.ker (algebraMap P S) =>
    (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (g : P))
  let cb := TensorProduct.AlgebraTensorModule.cancelBaseChange P S L L Ω[P⁄R]
  apply le_antisymm
  · intro x hx
    have hg := KaehlerDifferential.mapBaseChange_surjective R P S hsurj
    have hex := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R P S hsurj
    have hex' := lTensor_exact (R := S)
      (M := LinearMap.ker (KaehlerDifferential.mapBaseChange R P S))
      (N := S ⊗[P] Ω[P⁄R]) (P := Ω[S⁄R]) L
      (LinearMap.exact_subtype_ker_map (KaehlerDifferential.mapBaseChange R P S)) hg
    have hy : LinearMap.lTensor L (KaehlerDifferential.mapBaseChange R P S) (cb.symm x) = 0 := hx
    obtain ⟨z, hz⟩ := (hex' _).mp hy
    have : x = cb (LinearMap.lTensor L (LinearMap.ker
        (KaehlerDifferential.mapBaseChange R P S)).subtype z) := by
      rw [hz, LinearEquiv.apply_symm_apply]
    rw [this]
    clear this hz
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add]; exact W.add_mem h₁ h₂
    | tmul l k =>
      obtain ⟨t, ht⟩ := (hex k.1).mp k.2
      obtain ⟨g, rfl⟩ := Ideal.toCotangent_surjective _ t
      rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, ← ht,
        KaehlerDifferential.kerCotangentToTensor_toCotangent,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
      have : l ⊗ₜ[P] KaehlerDifferential.D R P (g : P) =
          l • ((1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (g : P)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact W.smul_mem _ (Submodule.subset_span ⟨g, rfl⟩)
  · rw [span_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, tensorKaehlerMap_tmul_D, RingHom.mem_ker.mp g.2,
      map_zero, TensorProduct.tmul_zero]

omit [Algebra S L] [IsScalarTower P S L] [Algebra P S] [IsScalarTower R P S] in
/-- The Leibniz rule for differentials at a point. -/
theorem one_tmul_D_mul (p q : P) :
    (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (p * q) =
      algebraMap P L p • ((1 : L) ⊗ₜ[P] KaehlerDifferential.D R P q) +
        algebraMap P L q • ((1 : L) ⊗ₜ[P] KaehlerDifferential.D R P p) := by
  rw [Derivation.leibniz, TensorProduct.tmul_add, ← TensorProduct.smul_tmul,
    ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    Algebra.smul_def, Algebra.smul_def, smul_eq_mul, smul_eq_mul, mul_one, mul_one]

omit [Algebra S L] [IsScalarTower P S L] [Algebra P S] [IsScalarTower R P S] in
theorem one_tmul_D_mul_of_eq_zero (p q : P) (hq : algebraMap P L q = 0) :
    (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (p * q) =
      algebraMap P L p • ((1 : L) ⊗ₜ[P] KaehlerDifferential.D R P q) := by
  rw [one_tmul_D_mul, hq, zero_smul, add_zero]

omit [Algebra S L] [IsScalarTower P S L] [Algebra P S] [IsScalarTower R P S] in
theorem one_tmul_smul (p : P) (ω : Ω[P⁄R]) :
    (1 : L) ⊗ₜ[P] (p • ω) = algebraMap P L p • ((1 : L) ⊗ₜ[P] ω) := by
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul,
    mul_one]

omit [Algebra S L] [IsScalarTower P S L] [Algebra P S] [IsScalarTower R P S] in
theorem one_tmul_D_smul (r : R) (p : P) :
    (1 : L) ⊗ₜ[P] KaehlerDifferential.D R P (r • p) =
      algebraMap P L (algebraMap R P r) • ((1 : L) ⊗ₜ[P] KaehlerDifferential.D R P p) := by
  rw [(KaehlerDifferential.D R P).map_smul, ← algebraMap_smul P r, one_tmul_smul]

end KaehlerPoint

section Presentation

variable {R : Type*} [CommRing R] {ϖ : R}
variable {R' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
variable {P A P2 A2 : Type*} [CommRing P] [CommRing A] [CommRing P2] [CommRing A2]
  [Algebra R P] [Algebra R A] [Algebra R P2] [Algebra R A2]
  [Algebra P A] [IsScalarTower R P A] [Algebra P2 A2] [IsScalarTower R P2 A2]
  [Algebra P P2] [IsScalarTower R P P2] [Algebra P A2] [IsScalarTower P P2 A2]
  [Algebra A R'] [Algebra A2 R'] [Algebra P R'] [Algebra P2 R']
  [IsScalarTower P A R'] [IsScalarTower P2 A2 R'] [IsScalarTower P P2 R'] [IsScalarTower R P R']

/-- **The defect drop for a dilatation, in terms of presentations.** Let `P → A` and `P₂ → A₂` be
surjections of `R`-algebras with `P → P₂` compatible, and let `R'` be a discrete valuation ring
which is an algebra over all four rings compatibly, in which `ϖ` is a uniformizer. Suppose
`Ω_{P/R}` and `Ω_{P₂/R}` have finite bases indexed by a finite type `σ` and by `σ ⊕ Fin n`,
compatible with `P → P₂`, the last basis vectors being the differentials of elements `Xⱼ ∈ P₂`
with `ϖ Xⱼ = zⱼ` in `A₂`, for elements `zⱼ ∈ P`. Let `wₗ ∈ P` be relations of `A`. Suppose that
every relation of `A` maps to `0` in `A₂`, `A₂` has no `ϖ`-torsion, every relation of `A` becomes,
after multiplication by an element with unit value, an element of `(ϖ, z)² + (w)`, every element
of `P₂` comes from `P` up to a unit-valued multiplier, a power of `ϖ` and the relations
`zⱼ - ϖ Xⱼ`, the kernel of `P → A₂` is `ϖ`-power torsion in `A` up to unit-valued multipliers, and
the differentials of the `zⱼ, wₗ` are linearly independent at the closed point. If
`R' ⊗_A Ω_{A/R}` has non-zero torsion, then the torsion of `R' ⊗_{A₂} Ω_{A₂/R}` is strictly
shorter. -/
theorem torsionLength_lt_of_dilatationPresentation
    (hϖ : Irreducible (algebraMap R R' ϖ))
    (hsurj : Function.Surjective (algebraMap P A))
    (hsurj2 : Function.Surjective (algebraMap P2 A2))
    {σ : Type*} [Fintype σ] {n m : ℕ}
    (bP : Basis σ P Ω[P⁄R]) (b2 : Basis (σ ⊕ Fin n) P2 Ω[P2⁄R])
    (hb : ∀ i, KaehlerDifferential.map R R P P2 (bP i) = b2 (Sum.inl i))
    (X : Fin n → P2) (hbX : ∀ j, b2 (Sum.inr j) = KaehlerDifferential.D R P2 (X j))
    (z : Fin n → P) (w : Fin m → P)
    (hw : ∀ l, algebraMap P A (w l) = 0)
    (hX : ∀ j, algebraMap P2 A2 (algebraMap P P2 (z j) - ϖ • X j) = 0)
    (hfac : ∀ f, algebraMap P A f = 0 → algebraMap P A2 f = 0)
    (htf : ∀ y : A2, ϖ • y = 0 → y = 0)
    (hI : ∀ f, algebraMap P A f = 0 → ∃ e : P, IsUnit (algebraMap P R' e) ∧
      e * f ∈ (Ideal.span {algebraMap R P ϖ} ⊔ Ideal.span (Set.range z)) ^ 2 ⊔
        Ideal.span (Set.range w))
    (hgen : ∀ g : P2, ∃ e : P, IsUnit (algebraMap P R' e) ∧ ∃ (v : ℕ) (c : P),
      ϖ ^ v • (algebraMap P P2 e * g) - algebraMap P P2 c ∈
        Ideal.span (Set.range fun j => algebraMap P P2 (z j) - ϖ • X j))
    (hker : ∀ c : P, algebraMap P A2 c = 0 → ∃ e : P, IsUnit (algebraMap P R' e) ∧
      ∃ v : ℕ, algebraMap P A (ϖ ^ v • (e * c)) = 0)
    (hli : LinearIndependent (IsLocalRing.ResidueField R')
      (fun k => (1 : IsLocalRing.ResidueField R') ⊗ₜ[R']
        ((1 : R') ⊗ₜ[P] KaehlerDifferential.D R P (Sum.elim z w k))))
    (hT : torsion R' (R' ⊗[A] Ω[A⁄R]) ≠ ⊥) :
    torsionLength R' (R' ⊗[A2] Ω[A2⁄R]) < torsionLength R' (R' ⊗[A] Ω[A⁄R]) := by
  classical
  set ϖ' := algebraMap R R' ϖ with hϖ'
  have hϖ0 : ϖ' ≠ 0 := hϖ.ne_zero
  set ι := algebraMap P P2 with hιdef
  set χ := algebraMap P R' with hχdef
  set χ2 := algebraMap P2 R' with hχ2def
  set π2 := algebraMap P2 A2 with hπ2def
  have hχι : ∀ p, χ2 (ι p) = χ p := fun p => (IsScalarTower.algebraMap_apply P P2 R' p).symm
  have hπ2ι : ∀ p, π2 (ι p) = algebraMap P A2 p :=
    fun p => (IsScalarTower.algebraMap_apply P P2 A2 p).symm
  have hχA : ∀ f, algebraMap P A f = 0 → χ f = 0 := by
    intro f hf
    rw [hχdef, IsScalarTower.algebraMap_apply P A R', hf, map_zero]
  have hχ2A : ∀ g, π2 g = 0 → χ2 g = 0 := by
    intro g hg
    rw [hχ2def, IsScalarTower.algebraMap_apply P2 A2 R', ← hπ2def, hg, map_zero]
  have hχϖ : χ (algebraMap R P ϖ) = ϖ' := (IsScalarTower.algebraMap_apply R P R' ϖ).symm
  have hιϖ : ι (algebraMap R P ϖ) = algebraMap R P2 ϖ :=
    (IsScalarTower.algebraMap_apply R P P2 ϖ).symm
  have hχ2ϖ : χ2 (algebraMap R P2 ϖ) = ϖ' := by rw [← hιϖ, hχι, hχϖ]
  have hπ2ϖ : ∀ y : A2, π2 (algebraMap R P2 ϖ) * y = ϖ • y := by
    intro y
    rw [hπ2def, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  -- differentials at the points
  let dP : P → R' ⊗[P] Ω[P⁄R] := fun p => (1 : R') ⊗ₜ[P] KaehlerDifferential.D R P p
  let d2 : P2 → R' ⊗[P2] Ω[P2⁄R] := fun p => (1 : R') ⊗ₜ[P2] KaehlerDifferential.D R P2 p
  have dP_mul : ∀ p q, dP (p * q) = χ p • dP q + χ q • dP p := one_tmul_D_mul R R'
  have d2_mul : ∀ p q, d2 (p * q) = χ2 p • d2 q + χ2 q • d2 p := one_tmul_D_mul R R'
  have d2_add : ∀ p q, d2 (p + q) = d2 p + d2 q := fun p q => by
    simp only [d2, map_add, TensorProduct.tmul_add]
  have d2_sub : ∀ p q, d2 (p - q) = d2 p - d2 q := fun p q => by
    simp only [d2, map_sub, TensorProduct.tmul_sub]
  have d2_smul : ∀ p, d2 (ϖ • p) = ϖ' • d2 p := fun p => by
    simp only [d2]; rw [one_tmul_D_smul]; exact congrArg (· • _) hχ2ϖ
  have dP_smul : ∀ p, dP (ϖ • p) = ϖ' • dP p := fun p => by
    simp only [dP]; rw [one_tmul_D_smul]; exact congrArg (· • _) hχϖ
  have d2_pow_smul : ∀ (v : ℕ) p, d2 (ϖ ^ v • p) = ϖ' ^ v • d2 p := by
    intro v
    induction v with
    | zero => intro p; simp
    | succ v ih => intro p; rw [pow_succ', mul_smul, d2_smul, ih, pow_succ', mul_smul]
  have d2_sum : ∀ {k : ℕ} (f : Fin k → P2), d2 (∑ i, f i) = ∑ i, d2 (f i) := fun f => by
    simp only [d2, map_sum, TensorProduct.tmul_sum]
  let bF := Algebra.TensorProduct.basis R' bP
  let bF2 := Algebra.TensorProduct.basis R' b2
  let α := tensorKaehlerMap R R' (P := P) (S := P2)
  have hα : ∀ i, α (bF i) = bF2 (Sum.inl i) := by
    intro i
    simp only [bF, bF2, Algebra.TensorProduct.basis_apply, α, tensorKaehlerMap_tmul, hb]
  have hαd : ∀ p, α (dP p) = d2 (ι p) := fun p => tensorKaehlerMap_tmul_D R R' 1 p
  have hbF2 : ∀ j, bF2 (Sum.inr j) = d2 (X j) := by
    intro j
    simp only [bF2, Algebra.TensorProduct.basis_apply, hbX, d2]
  let dz : Fin n → R' ⊗[P] Ω[P⁄R] := fun j => dP (z j)
  let dw : Fin m → R' ⊗[P] Ω[P⁄R] := fun l => dP (w l)
  have hzw : Sum.elim dz dw = fun k => dP (Sum.elim z w k) := by
    funext k; cases k <;> rfl
  have : Module.Free R' (R' ⊗[P] Ω[P⁄R]) := Module.Free.of_basis bF
  have hli' : LinearIndependent R' (Sum.elim dz dw) := by
    rw [hzw]; exact linearIndependent_of_residue hϖ _ hli
  have hsat : ∀ x, ϖ' • x ∈ span R' (Set.range (Sum.elim dz dw)) →
      x ∈ span R' (Set.range (Sum.elim dz dw)) := by
    rw [hzw]; exact mem_span_of_smul_mem_span hϖ _ hli
  -- the kernels and the identifications of the differential modules
  set NP := span R' (Set.range fun g : RingHom.ker (algebraMap P A) => dP (g : P)) with hNPdef
  set N2 := span R' (Set.range fun g : RingHom.ker π2 => d2 (g : P2)) with hN2def
  have hkerP := ker_tensorKaehlerMap R R' (P := P) (S := A) hsurj
  have hkerP2 := ker_tensorKaehlerMap R R' (P := P2) (S := A2) hsurj2
  let eM := (Submodule.quotEquivOfEq _ _ hkerP.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (tensorKaehlerMap_surjective R R' (P := P) (S := A)
      hsurj))
  let eM2 := (Submodule.quotEquivOfEq _ _ hkerP2.symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (tensorKaehlerMap_surjective R R' (P := P2) (S := A2)
      hsurj2))
  rw [← torsionLength_congr eM, ← torsionLength_congr eM2]
  -- the comparison map
  set θ0 := latticeMap ϖ' bF bF2 dz with hθ0def
  have hθb : ∀ k, θ0 (bF2 k) = Sum.elim (fun i => ϖ' ^ 2 • bF i) (fun j => ϖ' • dz j) k :=
    latticeMap_basis ϖ' bF bF2 dz
  have hθα : ∀ x, θ0 (α x) = ϖ' ^ 2 • x := by
    intro x
    have : θ0 ∘ₗ α = ϖ' ^ 2 • LinearMap.id := bF.ext fun i => by
      simp only [LinearMap.coe_comp, Function.comp_apply, hα, hθb, Sum.elim_inl,
        LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    exact LinearMap.congr_fun this x
  have hθz : ∀ j, θ0 (d2 (ι (z j) - ϖ • X j)) = 0 := by
    intro j
    rw [d2_sub, d2_smul, ← hαd, ← hbF2, map_sub, map_smul, hθα, hθb, Sum.elim_inr, smul_smul,
      ← pow_two, sub_self]
  have hzker : ∀ j, ι (z j) - ϖ • X j ∈ RingHom.ker π2 := fun j => hX j
  have hwker : ∀ l, ι (w l) ∈ RingHom.ker π2 := fun l => by
    rw [RingHom.mem_ker, hπ2ι]; exact hfac _ (hw l)
  set W := span R' (Set.range dw) with hWdef
  set K := Ideal.span (Set.range fun j => ι (z j) - ϖ • X j) with hKdef
  have hKker : K ≤ RingHom.ker π2 := Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hzker j)
  set K2 := span R' (Set.range fun j => d2 (ι (z j) - ϖ • X j)) with hK2def
  have hd2K : ∀ κ ∈ K, d2 κ ∈ K2 := by
    intro κ hκ
    obtain ⟨a, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hκ
    rw [d2_sum]
    refine sum_mem fun j _ => ?_
    rw [d2_mul, hχ2A _ (hzker j), zero_smul, add_zero]
    exact K2.smul_mem _ (subset_span ⟨j, rfl⟩)
  have hθK2 : ∀ x ∈ K2, θ0 x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hθz j
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  -- the relations of `A` lift to relations of `A₂` divided by `ϖ²`
  have hQ : (Ideal.span {algebraMap R P ϖ} ⊔ Ideal.span (Set.range z)) ^ 2 ⊔
      Ideal.span (Set.range w) ≤ Ideal.comap ι (Ideal.span {(algebraMap R P2 ϖ) ^ 2} ⊔
        Ideal.span (Set.range fun l => ι (w l)) ⊔ K) := by
    refine sup_le ?_ ?_
    · rw [← Ideal.span_union, pow_two, Ideal.span_mul_span, Ideal.span_le]
      rintro _ ⟨a, ha, b, hb', rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_mul]
      have hmemK : ∀ j, ι (z j) - ϖ • X j ∈ Ideal.span {(algebraMap R P2 ϖ) ^ 2} ⊔
          Ideal.span (Set.range fun l => ι (w l)) ⊔ K :=
        fun j => Ideal.mem_sup_right (Ideal.subset_span ⟨j, rfl⟩)
      have hmemϖ : ∀ y, (algebraMap R P2 ϖ) ^ 2 * y ∈ Ideal.span {(algebraMap R P2 ϖ) ^ 2} ⊔
          Ideal.span (Set.range fun l => ι (w l)) ⊔ K := fun y =>
        Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mul_mem_right _ _
          (Ideal.mem_span_singleton_self _)))
      have hzX : ∀ j, ι (z j) = (ι (z j) - ϖ • X j) + algebraMap R P2 ϖ * X j := by
        intro j; rw [Algebra.smul_def]; ring
      rcases ha with ha | ⟨i, rfl⟩ <;> rcases hb' with hb' | ⟨j, rfl⟩
      · rw [Set.mem_singleton_iff] at ha hb'
        rw [ha, hb', hιϖ, ← pow_two]
        simpa using hmemϖ 1
      · rw [Set.mem_singleton_iff] at ha
        rw [ha, hιϖ, hzX j, mul_add, ← mul_assoc, ← pow_two]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hmemK j)) (hmemϖ _)
      · rw [Set.mem_singleton_iff] at hb'
        rw [hb', hιϖ, hzX i, add_mul, mul_assoc, mul_comm (X i), ← mul_assoc, ← pow_two]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hmemK i)) (hmemϖ _)
      · rw [hzX i, hzX j]
        have : ((ι (z i) - ϖ • X i) + algebraMap R P2 ϖ * X i) *
            ((ι (z j) - ϖ • X j) + algebraMap R P2 ϖ * X j) =
            (ι (z i) - ϖ • X i) * ((ι (z j) - ϖ • X j) + algebraMap R P2 ϖ * X j) +
            (algebraMap R P2 ϖ * X i) * (ι (z j) - ϖ • X j) +
            (algebraMap R P2 ϖ) ^ 2 * (X i * X j) := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hmemK i))
          (Ideal.mul_mem_left _ _ (hmemK j))) (hmemϖ _)
    · rw [Ideal.span_le]
      rintro _ ⟨l, rfl⟩
      exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩))
  have hNP : ∀ x ∈ NP, ∃ y ∈ N2, x - θ0 y ∈ W := by
    have hle : NP ≤ N2.map θ0 ⊔ W := by
      rw [hNPdef, span_le]
      rintro _ ⟨⟨f, hf⟩, rfl⟩
      have hf' : algebraMap P A f = 0 := hf
      obtain ⟨e, he, hef⟩ := hI f hf'
      have hmem := hQ hef
      rw [Ideal.mem_comap] at hmem
      obtain ⟨ab, hab, κ, hκ, hsum⟩ := Submodule.mem_sup.mp hmem
      obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp hab
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hb'
      -- `r` is a relation of `A₂`
      have hr : π2 r = 0 := by
        have h1 : π2 (ι (e * f)) = 0 := by
          rw [hπ2ι]; exact hfac _ (by rw [map_mul, hf', mul_zero])
        rw [← hsum, map_add, map_add, map_mul, map_sum, (hKker hκ : π2 κ = 0), add_zero] at h1
        have h2 : ∑ l, π2 (c l * ι (w l)) = 0 := Finset.sum_eq_zero fun l _ => by
          rw [map_mul, (hwker l : π2 (ι (w l)) = 0), mul_zero]
        rw [h2, add_zero, map_pow, mul_comm, pow_two, mul_assoc, hπ2ϖ, hπ2ϖ] at h1
        exact htf _ (htf _ h1)
      -- differentials
      have hdef : dP (e * f) = χ e • dP f := by
        rw [dP_mul, hχA f hf', zero_smul, add_zero]
      have hkey : ϖ' ^ 2 • dP (e * f) =
          ϖ' ^ 2 • (θ0 (d2 r) + ∑ l, χ2 (c l) • dw l) := by
        rw [← hθα, hαd, ← hsum, d2_add, d2_add, map_add, map_add, hθK2 _ (hd2K κ hκ), add_zero,
          d2_mul, hχ2A r hr, zero_smul, zero_add, map_pow, hχ2ϖ, map_smul, d2_sum, map_sum,
          smul_add, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [d2_mul, hχ2A _ (hwker l), zero_smul, add_zero, map_smul, ← hαd, hθα, smul_comm]
      have hkey' := smul_right_injective (R' ⊗[P] Ω[P⁄R]) (pow_ne_zero 2 hϖ0) hkey
      have hdP : dP f = ((he.unit⁻¹ : R'ˣ) : R') • dP (e * f) := by
        rw [hdef, smul_smul, he.val_inv_mul, one_smul]
      change dP f ∈ _
      rw [hdP, hkey']
      refine (N2.map θ0 ⊔ W).smul_mem _ (add_mem (mem_sup_left ⟨d2 r, ?_, rfl⟩)
        (mem_sup_right (sum_mem fun l _ => W.smul_mem _ (subset_span ⟨l, rfl⟩))))
      exact subset_span ⟨⟨r, hr⟩, rfl⟩
    intro x hx
    obtain ⟨y', ⟨y, hy, rfl⟩, w', hw', hsum⟩ := Submodule.mem_sup.mp (hle hx)
    exact ⟨y, hy, by rw [← hsum, add_sub_cancel_left]; exact hw'⟩
  -- elements of `N₂` come from `N_P` up to powers of `ϖ`
  set W2 := span R' (Set.range fun l => α (dw l)) ⊔
    span R' (Set.range fun j => α (dz j) - ϖ' • bF2 (Sum.inr j)) with hW2def
  have hK2W2 : K2 ≤ W2 := by
    refine le_trans (span_le.mpr ?_) le_sup_right
    rintro _ ⟨j, rfl⟩
    refine subset_span ⟨j, ?_⟩
    simp only [dz, hαd, hbF2, d2_sub, d2_smul]
  have hN2 : ∀ y ∈ N2, ∃ (v : ℕ) (x : R' ⊗[P] Ω[P⁄R]), x ∈ NP ∧ ϖ' ^ v • y - α x ∈ W2 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨g, hg⟩, rfl⟩ := hy
      have hg' : π2 g = 0 := hg
      obtain ⟨e, he, v, c, hc⟩ := hgen g
      set κ := ϖ ^ v • (ι e * g) - ι c with hκdef
      have hπκ : π2 κ = 0 := hKker hc
      have hπc : algebraMap P A2 c = 0 := by
        rw [← hπ2ι]
        have : ι c = ϖ ^ v • (ι e * g) - κ := by rw [hκdef]; abel
        rw [this, map_sub, Algebra.smul_def, map_mul, map_mul, hg', mul_zero, mul_zero, hπκ,
          sub_zero]
      obtain ⟨e', he', v', hc'⟩ := hker c hπc
      set x0 := dP (ϖ ^ v' • (e' * c)) with hx0
      have hx0N : x0 ∈ NP := subset_span ⟨⟨_, hc'⟩, rfl⟩
      have hχc : χ c = 0 := by rw [← hχι, hχ2A _ (by rw [hπ2ι]; exact hπc)]
      have hdc : d2 (ι c) = ϖ' ^ v • χ e • d2 g - d2 κ := by
        rw [hκdef, d2_sub, d2_pow_smul, d2_mul, hχ2A g hg', zero_smul, add_zero, hχι]
        abel
      have dP_pow_smul : ∀ (k : ℕ) p, dP (ϖ ^ k • p) = ϖ' ^ k • dP p := by
        intro k
        induction k with
        | zero => intro p; simp
        | succ k ih => intro p; rw [pow_succ', mul_smul, dP_smul, ih, pow_succ', mul_smul]
      have hαx0 : α x0 = ϖ' ^ v' • χ e' • d2 (ι c) := by
        rw [hx0, dP_pow_smul, dP_mul, hχc, zero_smul, add_zero, map_smul, map_smul, hαd]
      set ui : R' := (((he'.unit * he.unit)⁻¹ : R'ˣ) : R') with hui
      have hui1 : ui * (χ e' * χ e) = 1 := by
        have hu : ((he'.unit * he.unit : R'ˣ) : R') = χ e' * χ e := by
          rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec]
        rw [hui, ← hu, Units.inv_mul]
      refine ⟨v' + v, ui • x0, NP.smul_mem _ hx0N, ?_⟩
      have : ϖ' ^ (v' + v) • d2 g - α (ui • x0) = (ui * ϖ' ^ v' * χ e') • d2 κ := by
        rw [map_smul, hαx0, hdc]
        match_scalars
        · linear_combination (-(ϖ' ^ (v' + v))) * hui1
        · ring
      rw [this]
      exact W2.smul_mem _ (hK2W2 (hd2K κ hc))
    | zero => exact ⟨0, 0, NP.zero_mem, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨v₁, x₁, hx₁, h₁⟩ := h₁
      obtain ⟨v₂, x₂, hx₂, h₂⟩ := h₂
      refine ⟨v₁ + v₂, ϖ' ^ v₂ • x₁ + ϖ' ^ v₁ • x₂,
        NP.add_mem (NP.smul_mem _ hx₁) (NP.smul_mem _ hx₂), ?_⟩
      have : ϖ' ^ (v₁ + v₂) • (y₁ + y₂) - α (ϖ' ^ v₂ • x₁ + ϖ' ^ v₁ • x₂) =
          ϖ' ^ v₂ • (ϖ' ^ v₁ • y₁ - α x₁) + ϖ' ^ v₁ • (ϖ' ^ v₂ • y₂ - α x₂) := by
        simp only [map_add, map_smul, smul_add, smul_sub, smul_smul, ← pow_add]
        rw [add_comm v₂ v₁]
        abel
      rw [this]
      exact W2.add_mem (W2.smul_mem _ h₁) (W2.smul_mem _ h₂)
    | smul r y _ h =>
      obtain ⟨v, x, hx, h⟩ := h
      refine ⟨v, r • x, NP.smul_mem _ hx, ?_⟩
      rw [map_smul, smul_comm, ← smul_sub]
      exact W2.smul_mem _ h
  have hT' : torsion R' ((R' ⊗[P] Ω[P⁄R]) ⧸ NP) ≠ ⊥ := by
    intro hbot
    apply hT
    rw [eq_bot_iff]
    intro t ht
    have h := mem_torsion_map (f := eM.symm.toLinearMap) ht
    rw [hbot, mem_bot] at h
    rw [mem_bot]
    simpa using congrArg eM h
  exact torsionLength_lt_of_presentations hϖ bF bF2 α hα dz dw hli' hsat NP N2
    (fun l => subset_span ⟨⟨w l, hw l⟩, rfl⟩)
    (fun l => by rw [hαd]; exact subset_span ⟨⟨_, hwker l⟩, rfl⟩)
    (fun j => by
      rw [hαd, hbF2, ← d2_smul, ← d2_sub]; exact subset_span ⟨⟨_, hzker j⟩, rfl⟩)
    hNP hN2 hT'

end Presentation

end Langlands.AlgebraicGeometry.DvrSmoothening
