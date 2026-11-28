import Langlands.BushnellKutzko.SimpleStratumConjugacyResidual

/-! # Comparison of two cyclic splitting bases

The construction `CriticalDerived.exists_cyclicBasis` lifts bases of the layers
`L_0/L_1, …, L_{g−1}/L_g` over the residual field `k_F[X]/(p)`. Here the number of
generators on the layer `L_i/L_{i+1}` is recorded: it is the dimension of that layer over
`k_F` divided by `deg p`. Two cyclic bases with the same residual polynomial, built for
two pairs `(z₁, τ₁)` and `(z₂, τ₂)`, therefore have the same numbers of generators. The
free modules over the cyclic algebra then coincide, and the composite of the two
transports is a unit of `𝔄` carrying the transported action for the second pair to the
action for the first pair.
-/

noncomputable section

open ValuativeRel IsLocalRing Polynomial

namespace Langlands.BushnellKutzko.SimpleConjugacy

open CriticalDerived StratumEquivalence

universe uF uV uI uJ

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓒 : LatticeChain 𝒪[F] F V)

local notation "k" => ResidueField 𝒪[F]
local notation "L" => 𝓒.lattice
local notation "A" => Module.End F V

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem splits_reindex {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J]
    (B : Module.Basis I F V) (hB : 𝓒.Splits B) (e : I ≃ J) : 𝓒.Splits (B.reindex e) := by
  intro c j hj t
  have hs : ∑ i, c (e i) • B i ∈ L j := by
    rw [← e.sum_comp (fun i => c i • B.reindex e i)] at hj
    simpa only [Module.Basis.reindex_apply, Equiv.symm_apply_apply] using hj
  simpa only [Equiv.apply_symm_apply, Module.Basis.reindex_apply] using
    hB (fun i => c (e i)) j hs (e.symm t)

private def cyclicReindex {g h f : ℕ} (n : Fin g → ℕ) :
    (Σ q : Fin h × Fin g, Fin f × Fin (n q.2)) ≃ CyclicIndex n h f where
  toFun t := (⟨t.1.2, t.2.2⟩, t.1.1, t.2.1)
  invFun t := ⟨(t.2.1, t.1.1), (t.2.2, t.1.2)⟩
  left_inv := by rintro ⟨⟨m, i⟩, l, b⟩; rfl
  right_inv := by rintro ⟨⟨i, b⟩, m, l⟩; rfl

set_option maxHeartbeats 650000 in
/-- The cyclic splitting basis of `CriticalDerived.exists_cyclicBasis`, together with the
number of its generators on each of the first `g` layers: `deg P` times that number is the
dimension of the layer over the residue field. -/
theorem exists_cyclicBasis_count {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {g h : ℕ} (he : 𝓒.period = h * g) (P : Polynomial 𝒪[F])
    (hP : P.Monic) (hp : Irreducible (P.map (residue 𝒪[F])))
    (z : 𝓒.order) (hz : aeval z.val (P.map (algebraMap 𝒪[F] F)) ∈ 𝓒.endFiltration 1)
    (τ : (Module.End F V)ˣ) (hτ : Shifts 𝓒 (g : ℤ) τ) :
    ∃ B : CyclicBasis 𝓒 g h P.natDegree z.val τ,
      ∀ i : Fin g, P.natDegree * B.count i = Module.finrank k (𝓒.Layer (i : ℤ)) := by
  classical
  let D := AdjoinRoot (P.map (residue 𝒪[F]))
  let : Fact (Irreducible (P.map (residue 𝒪[F]))) := ⟨hp⟩
  let : ∀ i : ℤ, Module D (𝓒.Layer i) := fun i => layerRootModule 𝓒 P z hz i
  let : ∀ i : ℤ, IsScalarTower k D (𝓒.Layer i) := fun i => layerRootTower 𝓒 P z hz i
  have hb (i : Fin g) : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) D (𝓒.Layer (i : ℤ))) ∧
      P.natDegree * n = Module.finrank k (𝓒.Layer (i : ℤ)) := by
    let : Module.Finite 𝒪[F] (L (i : ℤ)) := Module.Finite.of_fg (𝓒.fg_lattice (i : ℤ))
    let : Module.Finite 𝒪[F] (𝓒.Layer (i : ℤ)) := inferInstance
    let : Module.Finite k (𝓒.Layer (i : ℤ)) :=
      Module.Finite.of_restrictScalars_finite 𝒪[F] k _
    let : Module.Finite D (𝓒.Layer (i : ℤ)) := Module.Finite.of_restrictScalars_finite k D _
    refine ⟨_, ⟨Module.finBasis D _⟩, ?_⟩
    rw [← Module.finrank_mul_finrank k D (𝓒.Layer (i : ℤ)),
      Module.finrank_eq_card_basis (residuePowerBasis P hP), Fintype.card_fin]
  choose n b hn using fun i => hb i
  let b₀ (i : Fin g) : Module.Basis (Fin P.natDegree × Fin (n i)) k (𝓒.Layer (i : ℤ)) :=
    (residuePowerBasis P hP).smulTower (b i).some
  choose v hv hq using fun (i : Fin g) (j : Fin (n i)) =>
    𝓒.intervalMk_surjective (i : ℤ) ((i : ℤ) + 1) ((b i).some j)
  let E : (Fin h × Fin g) ≃ Fin 𝓒.period := finProdFinEquiv.trans (finCongr he.symm)
  have hE (q : Fin h × Fin g) : (E q : ℤ) = (q.2 : ℤ) + (q.1 : ℤ) * g := by
    change ((q.2.val + g * q.1.val : ℕ) : ℤ) = _
    simp only [Nat.cast_add, Nat.cast_mul, mul_comm]
  let T (m : Fin h) : 𝓒.stabilizer := ⟨τ ^ (m : ℕ), (hτ.pow m).mem_stabilizer⟩
  have hweight (j : Fin 𝓒.period) :
      (j : ℤ) = ((E.symm j).2 : ℤ) + 𝓒.stabilizerValuation (T (E.symm j).1) := by
    rw [(hτ.pow ((E.symm j).1 : ℕ)).stabilizerValuation_eq]
    exact (congrArg (fun l : Fin 𝓒.period => (l : ℤ)) (E.apply_symm_apply j)).symm.trans
      (hE (E.symm j))
  let I (j : Fin 𝓒.period) := Fin P.natDegree × Fin (n (E.symm j).2)
  let b₁ (j : Fin 𝓒.period) : Module.Basis (I j) k (𝓒.Layer (j : ℤ)) :=
    (b₀ (E.symm j).2).map (residueLayerEquiv 𝓒 (T (E.symm j).1) _ _ (hweight j))
  let w (j : Fin 𝓒.period) (t : I j) : V :=
    ((τ : Module.End F V) ^ ((E.symm j).1 : ℕ)) ((z.val ^ (t.1 : ℕ)) (v (E.symm j).2 t.2))
  have hw (j : Fin 𝓒.period) (t : I j) : w j t ∈ L (j : ℤ) := by
    have hzv := 𝓒.mem_order.mp (z ^ (t.1 : ℕ)).prop ((E.symm j).2 : ℤ) _ (hv (E.symm j).2 t.2)
    let v' := (z.val ^ (t.1 : ℕ)) (v (E.symm j).2 t.2)
    exact (hweight j).symm ▸ (𝓒.mem_lattice_stabilizer_iff (T (E.symm j).1) _ v').mpr hzv
  have hbw (j : Fin 𝓒.period) (t : I j) :
      𝓒.intervalMk (j : ℤ) ((j : ℤ) + 1) (w j t) (hw j t) = b₁ j t := by
    change _ = residueLayerEquiv 𝓒 _ _ _ (hweight j) (b₀ _ t)
    rw [show b₀ (E.symm j).2 t =
      ((residuePowerBasis P hP) t.1) • (b (E.symm j).2).some t.2 from
        Module.Basis.smulTower_apply _ _ _]
    rw [residuePowerBasis_apply, ← hq (E.symm j).2 t.2, root_pow_smul_mk, residueLayerEquiv_mk]
    rfl
  obtain ⟨B, hB, hsplit⟩ := exists_splittingBasis_of_layerLifts hϖ 𝓒 b₁ w hw hbw
  let R : Sigma I ≃ CyclicIndex n h P.natDegree :=
    (Equiv.sigmaCongrLeft E.symm).trans (cyclicReindex n)
  refine ⟨⟨n, v, B.reindex R, splits_reindex 𝓒 B hsplit R, ?_, ?_⟩, hn⟩
  · intro t
    obtain ⟨⟨j, l, b'⟩, rfl⟩ := R.surjective t
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
    rfl
  · intro t
    obtain ⟨⟨j, l, b'⟩, rfl⟩ := R.surjective t
    rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, hB]
    have hj : cyclicWeight (R ⟨j, l, b'⟩) = (j : ℤ) := by
      change ((E.symm j).2 : ℤ) + ((E.symm j).1 : ℤ) * g = (j : ℤ)
      rw [← hE, E.apply_symm_apply]
    rw [hj]
    refine ⟨hw j (l, b'), fun hdeep => (b₁ j).ne_zero (l, b') ?_⟩
    rw [← hbw]
    exact (𝓒.intervalMk_eq_zero_iff _).mpr hdeep

section Transport

/-- Two cyclic bases with the same numbers of generators give a unit of `𝔄` carrying the
second basis onto the first; it intertwines the two transported actions of the cyclic
algebra. -/
theorem exists_unit_conj_action {Q : F[X]} {g h f : ℕ} {π : Fˣ} {a : ℤ}
    (M : CyclicAlgebra Q h f π a) {z₁ τ₁ z₂ τ₂ : A} {B₁ : CyclicBasis 𝓒 g h f z₁ τ₁}
    {B₂ : CyclicBasis 𝓒 g h f z₂ τ₂} (hcount : ∀ i, B₂.count i = B₁.count i) :
    ∃ u : Aˣ, Shifts 𝓒 0 u ∧ ∀ x : M.A, (u : A) * B₂.action M x = B₁.action M x * u := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  let σ : (Σ i : Fin g, Fin (B₂.count i)) ≃ (Σ i : Fin g, Fin (B₁.count i)) :=
    Equiv.sigmaCongrRight fun i => finCongr (hcount i)
  let e : B₂.Free M ≃ₗ[M.A] B₁.Free M := Finsupp.domLCongr σ
  let U : V ≃ₗ[F] V :=
    (B₂.transport M).symm.trans ((e.restrictScalars F).trans (B₁.transport M))
  let u : Aˣ := LinearMap.GeneralLinearGroup.ofLinearEquiv U
  have hu (v : V) : (u : A) v = U v := rfl
  have huinv (v : V) : ((u⁻¹ : Aˣ) : A) v = U.symm v := rfl
  have hbasis (t : CyclicIndex B₂.count h f) : U (B₂.basis t) = B₁.basis (σ t.1, t.2) := by
    rw [← B₂.transport_single M t, ← B₁.transport_single M (σ t.1, t.2)]
    simp only [U, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.restrictScalars_apply]
    congr 1
    simp only [e, Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.equivMapDomain_single]
  have hbasis' (t : CyclicIndex B₁.count h f) :
      U.symm (B₁.basis t) = B₂.basis (σ.symm t.1, t.2) := by
    rw [LinearEquiv.symm_apply_eq, hbasis]
    simp only [Equiv.apply_symm_apply]
  refine ⟨u, ⟨?_, ?_⟩, fun x => ?_⟩
  · rw [mem_endFiltration_iff_splittingBasis hϖ 𝓒 B₂.basis B₂.splits cyclicWeight B₂.depth]
    intro t
    rw [hu, hbasis, add_zero]
    exact (B₁.depth (σ t.1, t.2)).1
  · rw [neg_zero,
      mem_endFiltration_iff_splittingBasis hϖ 𝓒 B₁.basis B₁.splits cyclicWeight B₁.depth]
    intro t
    rw [huinv, hbasis', add_zero]
    exact (B₂.depth (σ.symm t.1, t.2)).1
  · apply LinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := (B₂.transport M).surjective v
    rw [Module.End.mul_apply, Module.End.mul_apply, B₂.action_apply, hu, hu]
    simp only [U, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.restrictScalars_apply, map_smul, B₁.action_apply]

end Transport

end Langlands.BushnellKutzko.SimpleConjugacy
