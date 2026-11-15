import Langlands.CommutativeAlgebra.Popescu.FaltingsKernel
import Langlands.CommutativeAlgebra.Popescu.FaltingsSnake

/-! # The core of Faltings' argument (Stacks 07E5, (2) ⇒ (4)) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open IsLocalRing

open scoped TensorProduct

variable {A A' : Type u} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A']
  [Algebra A A'] [IsLocalHom (algebraMap A A')]

/-- The map `β : κ' ⊗_κ (κ ⊗_A Ω_A) → κ' ⊗_{A'} Ω_{A'}`. -/
noncomputable abbrev betaMap (A A' : Type u) [CommRing A] [CommRing A'] [IsLocalRing A]
    [IsLocalRing A'] [Algebra A A'] [IsLocalHom (algebraMap A A')] :
    ResidueField A' ⊗[ResidueField A] (ResidueField A ⊗[A] Ω[A⁄ℤ]) →ₗ[ResidueField A']
      ResidueField A' ⊗[A'] Ω[A'⁄ℤ] :=
  baseMap ℤ A A' (ResidueField A') ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField A')
      (ResidueField A') Ω[A⁄ℤ]).toLinearMap

theorem betaMap_tmul (c : ResidueField A') (d : ResidueField A) (ω : Ω[A⁄ℤ]) :
    betaMap A A' (c ⊗ₜ (d ⊗ₜ ω)) = (d • c) ⊗ₜ KaehlerDifferential.map ℤ ℤ A A' ω := by
  simp only [betaMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The first square commutes: `β ∘ (κ' ⊗ δ_A) = δ_{A'} ∘ (κ' ⊗ H₁(map))`. -/
theorem square_left :
    betaMap A A' ∘ₗ (Algebra.H1Cotangent.δ ℤ A (ResidueField A)).baseChange (ResidueField A') =
      Algebra.H1Cotangent.δ ℤ A' (ResidueField A') ∘ₗ
        (Algebra.H1Cotangent.map A A' (ResidueField A) (ResidueField A')).liftBaseChange
          (ResidueField A') := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul c y =>
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
    rw [map_smul, δ_square,
      show c ⊗ₜ[ResidueField A] Algebra.H1Cotangent.δ ℤ A (ResidueField A) y =
        c • ((1 : ResidueField A') ⊗ₜ Algebra.H1Cotangent.δ ℤ A (ResidueField A) y) by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem kaehler_map_square (ω : Ω[A⁄ℤ]) :
    KaehlerDifferential.map ℤ ℤ (ResidueField A) (ResidueField A')
        (KaehlerDifferential.map ℤ ℤ A (ResidueField A) ω) =
      KaehlerDifferential.map ℤ ℤ A' (ResidueField A') (KaehlerDifferential.map ℤ ℤ A A' ω) := by
  have h : ((KaehlerDifferential.map ℤ ℤ (ResidueField A) (ResidueField A')).restrictScalars A ∘ₗ
      KaehlerDifferential.map ℤ ℤ A (ResidueField A) : Ω[A⁄ℤ] →ₗ[A] Ω[ResidueField A'⁄ℤ]) =
      (KaehlerDifferential.map ℤ ℤ A' (ResidueField A')).restrictScalars A ∘ₗ
        KaehlerDifferential.map ℤ ℤ A A' := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change KaehlerDifferential.map ℤ ℤ (ResidueField A) (ResidueField A')
        (KaehlerDifferential.map ℤ ℤ A (ResidueField A) (KaehlerDifferential.D ℤ A a)) =
      KaehlerDifferential.map ℤ ℤ A' (ResidueField A')
        (KaehlerDifferential.map ℤ ℤ A A' (KaehlerDifferential.D ℤ A a))
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D,
      KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  exact LinearMap.congr_fun h ω

/-- The second square commutes: `γ ∘ (κ' ⊗ p_A) = p_{A'} ∘ β`. -/
theorem square_right :
    KaehlerDifferential.mapBaseChange ℤ (ResidueField A) (ResidueField A') ∘ₗ
        (KaehlerDifferential.mapBaseChange ℤ A (ResidueField A)).baseChange (ResidueField A') =
      KaehlerDifferential.mapBaseChange ℤ A' (ResidueField A') ∘ₗ betaMap A A' := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul c y =>
    induction y using TensorProduct.inductionOn with
    | tmul d ω =>
      rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.comp_apply, betaMap_tmul,
        KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.mapBaseChange_tmul, map_smul, kaehler_map_square,
        ← algebraMap_smul (ResidueField A') d, smul_smul]
      congr 1
      rw [Algebra.smul_def, mul_comm]
    | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

omit [IsLocalRing A] [IsLocalHom (algebraMap A A')] in
theorem baseMap_eq_lTensor (y : ResidueField A' ⊗[A] Ω[A⁄ℤ]) :
    baseMap ℤ A A' (ResidueField A') y =
      (KaehlerDifferential.mapBaseChange ℤ A A').lTensor (ResidueField A')
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange A A' (ResidueField A')
          (ResidueField A') Ω[A⁄ℤ]).symm y) := by
  induction y using TensorProduct.inductionOn with
  | tmul e ω =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.lTensor_tmul,
      KaehlerDifferential.mapBaseChange_tmul, one_smul, LinearMap.liftBaseChange_tmul]
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable (p : ℕ) {n : ℕ} (b : Fin n → A) (Q : Algebra.Generators A A' (Fin n))
  (hker : Q.ker = rootIdeal p b)

include hker in
/-- `ker β` is spanned by the `1 ⊗ 1 ⊗ db_j`. -/
theorem ker_betaMap_le (hp : (p : A') = 0) :
    LinearMap.ker (betaMap A A') ≤ Submodule.span (ResidueField A')
      (Set.range fun j => (1 : ResidueField A') ⊗ₜ[ResidueField A]
        ((1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j))) := by
  set S := Submodule.span (ResidueField A')
    (Set.range fun j => (1 : ResidueField A') ⊗ₜ[ResidueField A]
      ((1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j)))
  let cB := TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A)
    (ResidueField A') (ResidueField A') Ω[A⁄ℤ]
  let cB₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A A' (ResidueField A')
    (ResidueField A') Ω[A⁄ℤ]
  let φ := KaehlerDifferential.mapBaseChange ℤ A A'
  obtain ⟨e, -⟩ := exists_kaehler_basis p b Q hker hp
  have : Module.Projective A' Ω[A'⁄A] := Module.Projective.of_basis e
  have hG1 := ker_lTensor_eq_range φ (KaehlerDifferential.map ℤ A A' A')
    (KaehlerDifferential.exact_mapBaseChange_map ℤ A A') (KaehlerDifferential.map_surjective ℤ A A')
    (ResidueField A')
  have hkerφ : LinearMap.ker φ ≤ Submodule.span A'
      (Set.range fun j => (1 : A') ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j)) := by
    show LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ A A') ≤ _
    rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ A A').linearMap_ker_eq]
    exact range_δ_le_span p b Q hker
  -- the key computation
  have hspan : ∀ v ∈ Submodule.span A'
      (Set.range fun j => (1 : A') ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j)),
      ∀ c : ResidueField A', cB.symm (cB₁ (c ⊗ₜ[A'] v)) ∈ S := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      intro c
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
        show c ⊗ₜ[ResidueField A] ((1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j)) =
          c • ((1 : ResidueField A') ⊗ₜ[ResidueField A]
            ((1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j))) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact S.smul_mem c (Submodule.subset_span ⟨j, rfl⟩)
    | zero => intro c; rw [TensorProduct.tmul_zero, map_zero, map_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      intro c
      rw [TensorProduct.tmul_add, map_add, map_add]
      exact add_mem (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      rw [← TensorProduct.smul_tmul]
      exact hx _
  intro y hy
  have hz : φ.lTensor (ResidueField A') (cB₁.symm (cB y)) = 0 := by
    rw [← baseMap_eq_lTensor]
    exact hy
  rw [← LinearMap.mem_ker, hG1] at hz
  obtain ⟨t, ht⟩ := hz
  have hy' : y = cB.symm (cB₁ ((LinearMap.ker φ).subtype.lTensor (ResidueField A') t)) := by
    rw [ht, LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  rw [hy']
  clear hy' ht
  induction t using TensorProduct.inductionOn with
  | tmul c v =>
    rw [LinearMap.lTensor_tmul]
    exact hspan v.1 (hkerφ v.2) c
  | add x z hx hz =>
    rw [map_add, map_add, map_add]
    exact add_mem hx hz

include hker in
/-- `coker β` has dimension at least `n`: it surjects onto `κ' ⊗ Ω_{A'/A}`. -/
theorem rank_coker_betaMap_ge (hp : (p : A') = 0) :
    (n : Cardinal) ≤ Module.rank (ResidueField A')
      (ResidueField A' ⊗[A'] Ω[A'⁄ℤ] ⧸ LinearMap.range (betaMap A A')) := by
  obtain ⟨e, -⟩ := exists_kaehler_basis p b Q hker hp
  let ψ := (KaehlerDifferential.map ℤ A A' A').baseChange (ResidueField A')
  have hψ : Function.Surjective ψ := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (KaehlerDifferential.map_surjective ℤ A A')
  have hle : LinearMap.range (betaMap A A') ≤ LinearMap.ker ψ := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    induction y using TensorProduct.inductionOn with
    | tmul c y =>
      induction y using TensorProduct.inductionOn with
      | tmul d ω =>
        rw [betaMap_tmul, LinearMap.baseChange_tmul]
        have : KaehlerDifferential.map ℤ A A' A' (KaehlerDifferential.map ℤ ℤ A A' ω) = 0 := by
          have h := (KaehlerDifferential.exact_mapBaseChange_map ℤ A A').apply_apply_eq_zero
            ((1 : A') ⊗ₜ[A] ω)
          rwa [KaehlerDifferential.mapBaseChange_tmul, one_smul] at h
        rw [this, TensorProduct.tmul_zero]
      | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz, add_zero]
    | add x z hx hz => rw [map_add, map_add, hx, hz, add_zero]
  let q := (LinearMap.range (betaMap A A')).liftQ ψ hle
  have hq : Function.Surjective q := by
    intro z
    obtain ⟨y, rfl⟩ := hψ z
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have h1 := LinearMap.rank_le_of_surjective q hq
  rwa [rank_eq_card_basis (e.baseChange (ResidueField A')), Fintype.card_fin] at h1

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
theorem charP_of_algebra {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S] [Algebra R S]
    [hp : Fact p.Prime] [CharP R p] : CharP S p :=
  (CharP.charP_iff_prime_eq_zero hp.out).mpr (by
    rw [← map_natCast (algebraMap R S), CharP.cast_eq_zero, map_zero])

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
theorem rank_ker_gamma {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [Fact p.Prime]
    [CharP K p] [Algebra ℤ K] [Algebra ℤ K']
    [@IsScalarTower ℤ K K' Algebra.toSMul Algebra.toSMul Algebra.toSMul] :
    Module.rank K' (LinearMap.ker (KaehlerDifferential.mapBaseChange ℤ K K')) =
      Module.rank K' (Algebra.H1Cotangent K K') := by
  rw [(Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ K K').linearMap_ker_eq,
    rank_range_of_injective _ (δ_injective_of_charP p)]

omit [IsLocalRing A] [IsLocalRing A'] [IsLocalHom (algebraMap A A')] in
theorem rank_coker_gamma {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [Algebra ℤ K]
    [Algebra ℤ K']
    [@IsScalarTower ℤ K K' Algebra.toSMul Algebra.toSMul Algebra.toSMul] :
    Module.rank K' (Ω[K'⁄ℤ] ⧸ LinearMap.range (KaehlerDifferential.mapBaseChange ℤ K K')) =
      Module.rank K' Ω[K'⁄K] := by
  rw [← (KaehlerDifferential.exact_mapBaseChange_map ℤ K K').linearMap_ker_eq]
  exact (LinearMap.quotKerEquivOfSurjective _ (KaehlerDifferential.map_surjective ℤ K K')).rank_eq

theorem row_injective [Fact p.Prime] [CharP A p] :
    Function.Injective
      ((Algebra.H1Cotangent.δ ℤ A (ResidueField A)).baseChange (ResidueField A')) := by
  have : CharP (ResidueField A) p := charP_of_algebra p (R := A)
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (δ_injective_of_charP p)

theorem row_surjective₀ :
    Function.Surjective (KaehlerDifferential.mapBaseChange ℤ A (ResidueField A)) :=
  mapBaseChange_surjective_of_surjective residue_surjective

theorem row_exact :
    Function.Exact
      ((Algebra.H1Cotangent.δ ℤ A (ResidueField A)).baseChange (ResidueField A'))
      ((KaehlerDifferential.mapBaseChange ℤ A (ResidueField A)).baseChange (ResidueField A')) := by
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
  exact lTensor_exact _ (Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ A (ResidueField A))
    row_surjective₀

theorem row_surjective :
    Function.Surjective
      ((KaehlerDifferential.mapBaseChange ℤ A (ResidueField A)).baseChange (ResidueField A')) := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ row_surjective₀

theorem rank_baseChange_h1 :
    Module.rank (ResidueField A')
      (ResidueField A' ⊗[ResidueField A] Algebra.H1Cotangent A (ResidueField A)) =
      Module.rank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) := by
  rw [Module.rank_baseChange, Cardinal.lift_id]

/-- The snake lemma applied to the two Jacobi–Zariski rows. -/
theorem snake_beta [Fact p.Prime] [CharP A p]
    (hX₁ : Module.rank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) <
      Cardinal.aleph0)
    (hX : Module.rank (ResidueField A') (Algebra.H1Cotangent A' (ResidueField A')) ≤
      Module.rank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)))
    (hcart : Module.rank (ResidueField A')
        (Algebra.H1Cotangent (ResidueField A) (ResidueField A')) =
      Module.rank (ResidueField A') Ω[ResidueField A'⁄ResidueField A])
    (hcartf : Module.rank (ResidueField A') Ω[ResidueField A'⁄ResidueField A] <
      Cardinal.aleph0) :
    Module.rank (ResidueField A') (ResidueField A' ⊗[A'] Ω[A'⁄ℤ] ⧸ LinearMap.range (betaMap A A'))
      ≤ Module.rank (ResidueField A') (LinearMap.ker (betaMap A A')) := by
  have : CharP A' p := charP_of_algebra p (R := A)
  have : CharP (ResidueField A) p := charP_of_algebra p (R := A)
  exact (rank_coker_le_rank_ker
    ((Algebra.H1Cotangent.δ ℤ A (ResidueField A)).baseChange (ResidueField A'))
    ((KaehlerDifferential.mapBaseChange ℤ A (ResidueField A)).baseChange (ResidueField A'))
    (Algebra.H1Cotangent.δ ℤ A' (ResidueField A'))
    (KaehlerDifferential.mapBaseChange ℤ A' (ResidueField A'))
    (row_injective p) row_exact row_surjective
    (δ_injective_of_charP p) (Algebra.H1Cotangent.exact_δ_mapBaseChange ℤ A' (ResidueField A'))
    (mapBaseChange_surjective_of_surjective residue_surjective)
    ((Algebra.H1Cotangent.map A A' (ResidueField A) (ResidueField A')).liftBaseChange
      (ResidueField A'))
    (betaMap A A') (KaehlerDifferential.mapBaseChange ℤ (ResidueField A) (ResidueField A'))
    square_left square_right
    (by rw [rank_baseChange_h1]; exact hX₁) (by rw [rank_ker_gamma p, hcart]; exact hcartf)
    (by rw [rank_baseChange_h1]; exact hX) (by rw [rank_coker_gamma, rank_ker_gamma p, hcart])).1

include hker in
/-- **Core of Faltings' argument.** Let `A → A'` be a local map of local rings of characteristic
`p`, with `A' = A[x]/(x_j^p − b_j)`. Assume `dim H₁(L_{κ'/A'}) ≤ dim H₁(L_{κ/A}) < ∞` and
`dim H₁(L_{κ'/κ}) = dim Ω_{κ'/κ} < ∞`. Then the `1 ⊗ db_j` are linearly independent in
`κ ⊗_A Ω_{A/ℤ}`. -/
theorem faltings_core [Fact p.Prime] [CharP A p]
    (hX₁ : Module.rank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)) <
      Cardinal.aleph0)
    (hX : Module.rank (ResidueField A') (Algebra.H1Cotangent A' (ResidueField A')) ≤
      Module.rank (ResidueField A) (Algebra.H1Cotangent A (ResidueField A)))
    (hcart : Module.rank (ResidueField A')
        (Algebra.H1Cotangent (ResidueField A) (ResidueField A')) =
      Module.rank (ResidueField A') Ω[ResidueField A'⁄ResidueField A])
    (hcartf : Module.rank (ResidueField A') Ω[ResidueField A'⁄ResidueField A] <
      Cardinal.aleph0) :
    LinearIndependent (ResidueField A) fun j =>
      (1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j) := by
  classical
  have : CharP A' p := charP_of_algebra p (R := A)
  have hpA' : (p : A') = 0 := CharP.cast_eq_zero A' p
  have hsnake := snake_beta p hX₁ hX hcart hcartf
  let w : Fin n → ResidueField A' ⊗[ResidueField A] (ResidueField A ⊗[A] Ω[A⁄ℤ]) :=
    fun j => (1 : ResidueField A') ⊗ₜ[ResidueField A]
      ((1 : ResidueField A) ⊗ₜ[A] KaehlerDifferential.D ℤ A (b j))
  have hspan := Submodule.rank_mono (ker_betaMap_le p b Q hker hpA')
  have hspanle : Module.rank (ResidueField A') (Submodule.span (ResidueField A') (Set.range w)) ≤
      n := by
    refine (rank_span_le _).trans ?_
    rw [Cardinal.mk_fintype]
    exact_mod_cast (Fintype.card_range_le _).trans (Fintype.card_fin n).le
  have hge := rank_coker_betaMap_ge p b Q hker hpA'
  have hrank : Module.rank (ResidueField A') (Submodule.span (ResidueField A') (Set.range w)) =
      n := le_antisymm hspanle (hge.trans (hsnake.trans hspan))
  have hliw : LinearIndependent (ResidueField A') w := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    exact (Module.finrank_eq_of_rank_eq hrank).symm
  have hinj : Function.Injective fun r : ResidueField A => r • (1 : ResidueField A') := by
    intro x y hxy
    simp only [Algebra.smul_def, mul_one] at hxy
    exact (algebraMap (ResidueField A) (ResidueField A')).injective hxy
  exact LinearIndependent.of_comp
    (TensorProduct.mk (ResidueField A) (ResidueField A') (ResidueField A ⊗[A] Ω[A⁄ℤ]) 1)
    (hliw.restrict_scalars hinj)

end Faltings

end Langlands.CommutativeAlgebra.Popescu
