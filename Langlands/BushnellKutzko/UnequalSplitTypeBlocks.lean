import Langlands.BushnellKutzko.UnequalPositiveSplitType
import Langlands.BushnellKutzko.SplitStratumBlocks
import Langlands.BushnellKutzko.PureStratumApproximationImprovementSteps
import Langlands.BushnellKutzko.RefinementProof

/-! # Block data for the corestricted stratum of a split type of level `(x, y)` -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  [FiniteDimensional F E]

/-- A split corestricted stratum `[𝔅, m, m−1, s(c)]` with `m > 0` and `gcd(m, e(𝔅 | 𝔬_E)) = 1`
has block data over `𝔬_E`. -/
theorem nonempty_splitBlockData_corestricted (L : LatticeChain 𝒪[F] F V)
    (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (s : TameCorestriction 𝒪[F] F E V) {m : ℕ} (hm : 0 < m) (c : L.endFiltration (-(m : ℤ)))
    (hcop : Nat.Coprime m (L.subfieldChain E hE).period)
    (hsplit : (L.corestrictedStratum hE s m c).IsSplit) :
    Nonempty (SplitBlockData (L.corestrictedStratum hE s m c)) := by
  have := subfieldIntegers_isDiscreteValuationRing F E
  have := subfieldIntegers_isFractionRing F E
  have := SplitObstruction.henselianRing_subfieldIntegers (F := F) (E := E)
  set D := L.corestrictedStratum hE s m c
  have hb : D.b ∈ D.chain.endFiltration (-D.n) :=
    PureApproximation.mem_endFiltration_of_le_valuation_subfield D.chain
      (by exact_mod_cast D.valuation_ge)
  exact nonempty_splitBlockData D hsplit hb (by change (0 : ℤ) < (m : ℤ); omega)
    (by change Nat.Coprime (m : ℤ).natAbs (L.subfieldChain E hE).period; simpa using hcop)

end Langlands.BushnellKutzko.SplitBlocks

namespace Langlands.BushnellKutzko.SplitBlocks

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  [FiniteDimensional F E]

local notation "A" => Module.End F V

/-- The `F`-linear shadow of block data over `𝔬_E`: complementary idempotents of `𝔄`, the
shift `ζ ∈ 𝔓` and its inverse `ζ' ∈ 𝔓^{−1}` on the first block, all commuting with `E`. -/
structure RestrictedBlockData (L : LatticeChain 𝒪[F] F V) (E : Type uE) [Field E] [Algebra F E]
    [Module E V] [IsScalarTower F E V] where
  /-- The first idempotent. -/
  e₁ : A
  /-- The second idempotent. -/
  e₂ : A
  /-- The shift element on the first block. -/
  ζ : A
  /-- Its inverse on the first block. -/
  ζ' : A
  add_eq : e₁ + e₂ = 1
  mul_eq : e₁ * e₂ = 0
  e₁_ne : e₁ ≠ 0
  e₂_ne : e₂ ≠ 0
  e₁_mem : e₁ ∈ L.endFiltration 0
  e₂_mem : e₂ ∈ L.endFiltration 0
  ζ_mem : ζ ∈ L.endFiltration 1
  ζ'_mem : ζ' ∈ L.endFiltration (-1)
  ζ_mul_ζ' : ζ * ζ' = e₁
  ζ'_mul_ζ : ζ' * ζ = e₁
  e₁_mul_ζ : e₁ * ζ = ζ
  ζ_mul_e₁ : ζ * e₁ = ζ
  e₁_mul_ζ' : e₁ * ζ' = ζ'
  ζ'_mul_e₁ : ζ' * e₁ = ζ'
  e₁_comm : ∀ a : E, Commute e₁ (subfieldEmbedding F E V a)
  e₂_comm : ∀ a : E, Commute e₂ (subfieldEmbedding F E V a)
  ζ_comm : ∀ a : E, Commute ζ (subfieldEmbedding F E V a)
  ζ'_comm : ∀ a : E, Commute ζ' (subfieldEmbedding F E V a)

/-- Restriction of scalars of block data of a stratum over `𝔬_E` on the subfield chain. -/
def SplitBlockData.restrict (L : LatticeChain 𝒪[F] F V)
    (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    {D : Stratum (subfieldIntegers F E) E V} (hD : D.chain = L.subfieldChain E hE)
    (B : SplitBlockData D) : RestrictedBlockData L E where
  e₁ := B.e₁.restrictScalars F
  e₂ := B.e₂.restrictScalars F
  ζ := B.ζ.restrictScalars F
  ζ' := B.ζ'.restrictScalars F
  add_eq := by
    rw [← LinearMap.restrictScalars_add, B.add_eq]
    rfl
  mul_eq := by
    change (B.e₁ * B.e₂).restrictScalars F = 0
    rw [B.mul_eq]
    rfl
  e₁_ne := fun h => B.e₁_ne (LinearMap.restrictScalars_injective F (h.trans rfl))
  e₂_ne := fun h => B.e₂_ne (LinearMap.restrictScalars_injective F (h.trans rfl))
  e₁_mem := (mem_endFiltration_restrictScalars (𝓛 := L) (𝓒 := D.chain)
    (fun i => by rw [hD]; rfl)).mp B.e₁_mem
  e₂_mem := (mem_endFiltration_restrictScalars (𝓛 := L) (𝓒 := D.chain)
    (fun i => by rw [hD]; rfl)).mp B.e₂_mem
  ζ_mem := (mem_endFiltration_restrictScalars (𝓛 := L) (𝓒 := D.chain)
    (fun i => by rw [hD]; rfl)).mp B.ζ_mem
  ζ'_mem := (mem_endFiltration_restrictScalars (𝓛 := L) (𝓒 := D.chain)
    (fun i => by rw [hD]; rfl)).mp B.ζ'_mem
  ζ_mul_ζ' := by
    change (B.ζ * B.ζ').restrictScalars F = _
    rw [B.ζ_mul_ζ']
  ζ'_mul_ζ := by
    change (B.ζ' * B.ζ).restrictScalars F = _
    rw [B.ζ'_mul_ζ]
  e₁_mul_ζ := by
    change (B.e₁ * B.ζ).restrictScalars F = _
    rw [B.e₁_mul_ζ]
  ζ_mul_e₁ := by
    change (B.ζ * B.e₁).restrictScalars F = _
    rw [B.ζ_mul_e₁]
  e₁_mul_ζ' := by
    change (B.e₁ * B.ζ').restrictScalars F = _
    rw [B.e₁_mul_ζ']
  ζ'_mul_e₁ := by
    change (B.ζ' * B.e₁).restrictScalars F = _
    rw [B.ζ'_mul_e₁]
  e₁_comm := restrictScalars_commute B.e₁
  e₂_comm := restrictScalars_commute B.e₂
  ζ_comm := restrictScalars_commute B.ζ
  ζ'_comm := restrictScalars_commute B.ζ'

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
/-- The block-diagonal part of a twisting element has the same corestriction. -/
theorem SplitBlockData.corestriction_diagonal {D : Stratum (subfieldIntegers F E) E V}
    (B : SplitBlockData D) (s : TameCorestriction 𝒪[F] F E V) {c : A} (hc : s c = D.b) :
    s (B.e₁.restrictScalars F * c * B.e₁.restrictScalars F +
      B.e₂.restrictScalars F * c * B.e₂.restrictScalars F) = s c := by
  change s.toAddMonoidHom (_ + _) = _
  rw [map_add]
  change s (_ * c * _) + s (_ * c * _) = _
  have hL (b : Module.End E V) (x : A) :
      s (b.restrictScalars F * x) = b * s x := s.map_mul_left b x
  have hR (b : Module.End E V) (x : A) :
      s (x * b.restrictScalars F) = s x * b := s.map_mul_right x b
  simp only [hR, hL, hc]
  rw [B.e₁_comm.eq, B.e₂_comm.eq]
  simp only [mul_assoc]
  have he₁ : B.e₁ * B.e₁ = B.e₁ := by
    calc B.e₁ * B.e₁ = B.e₁ * (B.e₁ + B.e₂) := by rw [mul_add, B.mul_eq, add_zero]
      _ = B.e₁ := by rw [B.add_eq, mul_one]
  have he₂ : B.e₂ * B.e₂ = B.e₂ := by
    calc B.e₂ * B.e₂ = (B.e₁ + B.e₂) * B.e₂ := by rw [add_mul, B.mul_eq, zero_add]
      _ = B.e₂ := by rw [B.add_eq, one_mul]
  rw [he₁, he₂, ← mul_add, B.add_eq, mul_one]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F E] in
/-- The difference obtained by shifting the first diagonal block has zero corestriction. -/
theorem SplitBlockData.corestriction_shift_sub {D : Stratum (subfieldIntegers F E) E V}
    (B : SplitBlockData D) (s : TameCorestriction 𝒪[F] F E V) {c : A} (hc : s c = D.b) :
    s (B.ζ.restrictScalars F * (B.e₁.restrictScalars F * c * B.e₁.restrictScalars F) *
      B.ζ'.restrictScalars F - B.e₁.restrictScalars F * c * B.e₁.restrictScalars F) = 0 := by
  change s.toAddMonoidHom (_ - _) = 0
  rw [map_sub]
  apply sub_eq_zero.mpr
  change s (_ * (_ * c * _) * _) = s (_ * c * _)
  have hL (b : Module.End E V) (x : A) :
      s (b.restrictScalars F * x) = b * s x := s.map_mul_left b x
  have hR (b : Module.End E V) (x : A) :
      s (x * b.restrictScalars F) = s x * b := s.map_mul_right x b
  simp only [hR, hL, hc]
  calc B.ζ * (B.e₁ * D.b * B.e₁) * B.ζ' =
      (B.ζ * B.e₁) * D.b * (B.e₁ * B.ζ') := by noncomm_ring
    _ = D.b * B.e₁ := by rw [B.ζ_mul_e₁, B.e₁_mul_ζ', B.ζ_comm.eq, mul_assoc, B.ζ_mul_ζ']
    _ = B.e₁ * D.b * B.e₁ := by
      rw [B.e₁_comm.eq, mul_assoc, show B.e₁ * B.e₁ = B.e₁ by
        calc B.e₁ * B.e₁ = B.e₁ * (B.e₁ + B.e₂) := by rw [mul_add, B.mul_eq, add_zero]
          _ = B.e₁ := by rw [B.add_eq, mul_one]]

set_option maxHeartbeats 800000 in
/-- Graded injectivity in the lower corner, expressed using the ambient `F`-endomorphisms. -/
theorem SplitBlockData.graded_commutator_lower_restrict
    (L : LatticeChain 𝒪[F] F V) (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer)
    (s : TameCorestriction 𝒪[F] F E V) {m : ℤ} (d : L.endFiltration (-m))
    (B : SplitBlockData (L.corestrictedStratum hE s m d)) {c : A} (hc : s c = s d)
    {β : E} (hβ : Algebra.adjoin F ({β} : Set E) = ⊤)
    {x : A} (hx : x ∈ centralizerLattice L (subfieldEmbedding F E V β) m)
    (hx₂₁ : B.e₂.restrictScalars F * x * B.e₁.restrictScalars F = x)
    (hcx : (s (c * x - x * c)).restrictScalars F ∈ L.endFiltration 1) :
    x ∈ L.endFiltration (m + 1) := by
  have hcomm : Commute x (subfieldEmbedding F E V β) :=
    (sub_eq_zero.mp (LinearMap.mem_ker.mp hx.2)).symm
  obtain ⟨X, hX⟩ := exists_restrictScalars_of_commute hβ hcomm
  have hfil {a : Module.End E V} {k : ℤ} :
      a ∈ (L.subfieldChain E hE).endFiltration k ↔
        a.restrictScalars F ∈ L.endFiltration k :=
    mem_endFiltration_restrictScalars (𝓛 := L) (𝓒 := L.subfieldChain E hE) (fun _ => rfl)
  have hXP : X ∈ (L.subfieldChain E hE).endFiltration m := hfil.mpr (hX.symm ▸ hx.1)
  have hX₂₁ : B.e₂ * X * B.e₁ = X := by
    apply LinearMap.restrictScalars_injective F
    change B.e₂.restrictScalars F * X.restrictScalars F * B.e₁.restrictScalars F =
      X.restrictScalars F
    rwa [hX]
  have hsx : s (c * x - x * c) = s d * X - X * s d := by
    rw [← hX]
    rw [map_sub]
    change s (_ * X.restrictScalars F) - s (X.restrictScalars F * _) = _
    have hL : s (X.restrictScalars F * c) = X * s c := s.map_mul_left X c
    have hR : s (c * X.restrictScalars F) = s c * X := s.map_mul_right c X
    rw [hR, hL, hc]
  have hbr : (s d * X - X * s d) ∈ (L.subfieldChain E hE).endFiltration 1 :=
    hfil.mpr (by rwa [← hsx])
  have hdepth : X ∈ (L.subfieldChain E hE).endFiltration (m + 1) := by
    apply B.inj₂₁ m X hXP hX₂₁
    change s d * X - X * s d ∈ (L.subfieldChain E hE).endFiltration (m - m + 1)
    simpa only [sub_self, zero_add] using hbr
  exact hX ▸ hfil.mp hdepth

end Langlands.BushnellKutzko.SplitBlocks
