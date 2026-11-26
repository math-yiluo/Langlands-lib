import Langlands.BushnellKutzko.AdjointCriticalExponent
import Langlands.BushnellKutzko.SplittingBasis
import Langlands.BushnellKutzko.SubfieldIntegers

/-! # Adjoint lifting for a sum of translated lattice steps -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uE uV

variable {F : Type uF} [Field F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

local notation "A" => Module.End F V

section Coordinates

variable {ι κ : Type*} (b : Module.Basis ι E V) (c : Module.Basis κ E V)

private def placeBlock (i : ι) (j : κ) (φ : Module.End F E) : A :=
  ((LinearMap.toSpanSingleton E V (b i)).restrictScalars F).comp
    (φ.comp ((c.coord j).restrictScalars F))

private theorem placeBlock_apply (i : ι) (j : κ) (φ : Module.End F E) (v : V) :
    placeBlock b c i j φ v = φ (c.repr v j) • b i := rfl

private def blockProjection (i : ι) (j : κ) (x : A) : A :=
  placeBlock b c i j (((b.coord i).restrictScalars F).comp
    (x.comp ((LinearMap.toSpanSingleton E V (c j)).restrictScalars F)))

private theorem blockProjection_apply (i : ι) (j : κ) (x : A) (v : V) :
    blockProjection b c i j x v = b.repr (x (c.repr v j • c j)) i • b i := rfl

private theorem blockProjection_add (i : ι) (j : κ) (x y : A) :
    blockProjection b c i j (x + y) =
      blockProjection b c i j x + blockProjection b c i j y := by
  ext v
  simp only [blockProjection_apply, LinearMap.add_apply, map_add, Finsupp.add_apply, add_smul]

private theorem sum_blockProjection [Fintype ι] [Fintype κ] (x : A) :
    ∑ p : ι × κ, blockProjection b c p.1 p.2 x = x := by
  ext v
  simp only [Fintype.sum_prod_type, LinearMap.sum_apply, blockProjection_apply]
  rw [Finset.sum_comm]
  simp only [b.sum_repr, ← map_sum, c.sum_repr]

variable [ValuativeRel F]

private theorem blockProjection_adjoint (a : E) (i : ι) (j : κ) (x : A) :
    blockProjection b c i j (adjointMap 𝒪[F] (subfieldEmbedding F E V a) x) =
      adjointMap 𝒪[F] (subfieldEmbedding F E V a) (blockProjection b c i j x) := by
  ext v
  change b.repr (a • x (c.repr v j • c j) - x (a • (c.repr v j • c j))) i • b i =
    a • (b.repr (x (c.repr v j • c j)) i • b i) -
      b.repr (x (c.repr (a • v) j • c j)) i • b i
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    sub_smul, mul_smul]

end Coordinates

section LatticeMaps

variable [ValuativeRel E]

private def latticeMaps (R T : LatticeChain 𝒪[E] E V) (n : ℤ) : AddSubgroup A where
  carrier := {x | ∀ i v, v ∈ R.lattice i → x v ∈ T.lattice (i + n)}
  zero_mem' := by simp
  add_mem' := fun {x y} hx hy i v hv => add_mem (hx i v hv) (hy i v hv)
  neg_mem' := fun {x} hx i v hv => neg_mem (hx i v hv)

private theorem blockProjection_mem_latticeMaps {ι κ : Type*} [Fintype ι] [Fintype κ]
    {b : Module.Basis ι E V} {c : Module.Basis κ E V}
    {R T : LatticeChain 𝒪[E] E V} (hb : T.Splits b) (hc : R.Splits c)
    {n : ℤ} {x : A} (hx : x ∈ latticeMaps R T n) (i : ι) (j : κ) :
    blockProjection b c i j x ∈ latticeMaps R T n := by
  intro l v hv
  have hsrc := hc (fun k => c.repr v k) l (by simpa only [c.sum_repr] using hv) j
  have htgt := hx l _ hsrc
  change b.repr (x (c.repr v j • c j)) i • b i ∈ T.lattice (l + n)
  exact hb _ _ (by simpa only [b.sum_repr] using htgt) i

variable [TopologicalSpace E] [IsNonarchimedeanLocalField E] {π : 𝒪[E]}
  (hπ : Irreducible π)

private theorem placeBlock_mem_latticeMaps_iff
    {ι κ : Type*} [Fintype κ] (b : Module.Basis ι E V) {c : Module.Basis κ E V}
    {R T : LatticeChain 𝒪[E] E V} (hc : R.Splits c) (hper : R.period = T.period)
    (i : ι) (j : κ) (n : ℤ) (φ : Module.End F E) :
    placeBlock b c i j φ ∈ latticeMaps R T n ↔
      ∀ t : E, t ≠ 0 → φ t ≠ 0 →
        R.index hπ (c j) + n - T.index hπ (b i) ≤
          (T.period : ℤ) * ordOf hπ (φ t) - (T.period : ℤ) * ordOf hπ t := by
  constructor
  · intro hf t ht hφt
    have hv := R.mem_lattice_index hπ (smul_ne_zero ht (c.ne_zero j))
    have h := hf _ _ hv
    rw [placeBlock_apply, map_smul, Finsupp.smul_apply, c.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] at h
    rw [T.mem_iff_le_index hπ (smul_ne_zero hφt (b.ne_zero i)),
      R.index_smul hπ ht (c.ne_zero j), T.index_smul hπ hφt (b.ne_zero i), hper] at h
    omega
  · intro hf l v hv
    let t := c.repr v j
    change φ t • b i ∈ T.lattice (l + n)
    by_cases hφt : φ t = 0
    · simp [hφt]
    have ht : t ≠ 0 := fun ht => hφt (by simp [ht])
    have hs : t • c j ∈ R.lattice l :=
      hc (fun k => c.repr v k) l (by simpa only [c.sum_repr] using hv) j
    rw [R.mem_iff_le_index hπ (smul_ne_zero ht (c.ne_zero j)), R.index_smul hπ ht (c.ne_zero j),
      hper] at hs
    rw [T.mem_iff_le_index hπ (smul_ne_zero hφt (b.ne_zero i)), T.index_smul hπ hφt (b.ne_zero i)]
    have h := hf t ht hφt
    omega

omit [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem period_linearEquivMap (L : LatticeChain 𝒪[E] E V) (g : V ≃ₗ[E] V) :
    (L.linearEquivMap g).period = L.period := by
  symm
  apply (L.linearEquivMap g).period_unique
  intro i
  change ((L.lattice (i + L.period)).map _) = Ring.jacobson 𝒪[E] • ((L.lattice i).map
    (g.toLinearMap.restrictScalars 𝒪[E]))
  rw [L.lattice_add_period, Submodule.map_smul'']

variable [ValuativeRel F]

include hπ in
private theorem adjoint_mem_iSup_inf_range {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    [Fintype σ] [Nonempty σ] (b : Module.Basis ι E V) (c : Module.Basis κ E V)
    (R T : σ → LatticeChain 𝒪[E] E V) (n : σ → ℤ)
    (hc : ∀ s, (R s).Splits c) (hb : ∀ s, (T s).Splits b)
    (period : ℕ) (hR : ∀ s, (R s).period = period) (hT : ∀ s, (T s).period = period)
    (a : E) (x : A) (hx : adjointMap 𝒪[F] (subfieldEmbedding F E V a) x ∈
      ⨆ s, latticeMaps (R s) (T s) (n s)) :
    adjointMap 𝒪[F] (subfieldEmbedding F E V a) x ∈
      ⨆ s, latticeMaps (R s) (T s) (n s) ⊓
        (adjointMap 𝒪[F] (subfieldEmbedding F E V a)).toAddMonoidHom.range := by
  classical
  let adj := adjointMap 𝒪[F] (subfieldEmbedding F E V a)
  rw [← sum_blockProjection b c (adj x)]
  refine AddSubgroup.sum_mem _ fun p _ => ?_
  let threshold (s : σ) := (R s).index hπ (c p.2) + n s - (T s).index hπ (b p.1)
  obtain ⟨s, _, hs⟩ := Finset.exists_min_image Finset.univ threshold Finset.univ_nonempty
  refine AddSubgroup.mem_iSup_of_mem s ⟨?_, ?_⟩
  · let block : A →+ A :=
      { toFun := blockProjection b c p.1 p.2
        map_zero' := by ext v; simp [blockProjection_apply]
        map_add' := blockProjection_add b c p.1 p.2 }
    change adj x ∈ (latticeMaps (R s) (T s) (n s)).comap block
    have hle : (⨆ t, latticeMaps (R t) (T t) (n t)) ≤
        (latticeMaps (R s) (T s) (n s)).comap block := by
      apply iSup_le
      intro t y hy
      change blockProjection b c p.1 p.2 y ∈ latticeMaps (R s) (T s) (n s)
      have hblock := blockProjection_mem_latticeMaps (hb t) (hc t) hy p.1 p.2
      let φ := ((b.coord p.1).restrictScalars F).comp
        (y.comp ((LinearMap.toSpanSingleton E V (c p.2)).restrictScalars F))
      change placeBlock b c p.1 p.2 φ ∈ latticeMaps (R t) (T t) (n t) at hblock
      change placeBlock b c p.1 p.2 φ ∈ latticeMaps (R s) (T s) (n s)
      rw [placeBlock_mem_latticeMaps_iff hπ b (hc t) ((hR t).trans (hT t).symm), hT] at hblock
      rw [placeBlock_mem_latticeMaps_iff hπ b (hc s) ((hR s).trans (hT s).symm), hT]
      exact fun z hz hφz => (hs t (Finset.mem_univ t)).trans (hblock z hz hφz)
    exact hle hx
  · exact ⟨blockProjection b c p.1 p.2 x, (blockProjection_adjoint b c a p.1 p.2 x).symm⟩

section LinearPart

variable {κ : Type*} (c : Module.Basis κ E V)

private def basisLinearPart : A →+ A where
  toFun x := (c.constr E (fun j => x (c j))).restrictScalars F
  map_zero' := by
    change (c.constr E (0 : κ → V)).restrictScalars F = 0
    rw [map_zero, LinearMap.restrictScalars_zero]
  map_add' x y := by
    change (c.constr E ((fun j => x (c j)) + (fun j => y (c j)))).restrictScalars F = _
    rw [map_add, LinearMap.restrictScalars_add]

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeRel F] in
private theorem basisLinearPart_eq_self {x : A} (hx : ∀ (a : E) v, x (a • v) = a • x v) :
    basisLinearPart c x = x := by
  let z : Module.End E V := { x with map_smul' := hx }
  change (c.constr E (fun j => z (c j))).restrictScalars F = x
  rw [c.constr_self E]
  rfl

omit [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] in
private theorem adjoint_basisLinearPart (a : E) (x : A) :
    adjointMap 𝒪[F] (subfieldEmbedding F E V a) (basisLinearPart c x) = 0 := by
  ext v
  let z := c.constr E (fun j => x (c j))
  change a • z v - z (a • v) = 0
  rw [map_smul, sub_self]

omit [ValuativeRel F] in
include hπ in
private theorem basisLinearPart_mem_latticeMaps [Fintype κ]
    {R T : LatticeChain 𝒪[E] E V} (hc : R.Splits c) (hper : R.period = T.period)
    {n : ℤ} {x : A} (hx : x ∈ latticeMaps R T n) :
    basisLinearPart c x ∈ latticeMaps R T n := by
  intro l v hv
  change c.constr E (fun j => x (c j)) v ∈ T.lattice (l + n)
  rw [c.constr_apply_fintype E]
  refine Submodule.sum_mem _ fun j _ => ?_
  let t := c.repr v j
  change t • x (c j) ∈ T.lattice (l + n)
  by_cases ht : t = 0
  · simp [ht]
  have hj : t • c j ∈ R.lattice l :=
    hc (fun j => c.repr v j) l (by simpa only [c.sum_repr] using hv) j
  rw [R.smul_mem_iff hπ ht, hper] at hj
  rw [T.smul_mem_iff hπ ht]
  simpa only [sub_add_eq_add_sub] using hx _ _ hj

end LinearPart

end LatticeMaps

section Translations

private abbrev endOfEquiv (g : V ≃ₗ[E] V) : A := g.toLinearMap.restrictScalars F

private theorem endOfEquiv_mul_symm (g : V ≃ₗ[E] V) :
    endOfEquiv (F := F) g * endOfEquiv g.symm = 1 := by
  ext v
  exact g.apply_symm_apply v

private theorem endOfEquiv_symm_mul (g : V ≃ₗ[E] V) :
    endOfEquiv (F := F) g.symm * endOfEquiv g = 1 :=
  endOfEquiv_mul_symm g.symm

variable [ValuativeRel F] (a : E)

local notation "ad" => adjointMap 𝒪[F] (subfieldEmbedding F E V a)

private theorem adjoint_left_mul (g : V ≃ₗ[E] V) (x : A) :
    ad (endOfEquiv g * x) = endOfEquiv g * ad x := by
  ext v
  change a • g (x v) - g (x (a • v)) = g (a • x v - x (a • v))
  rw [map_sub, g.map_smul]

private theorem adjoint_right_mul (g : V ≃ₗ[E] V) (x : A) :
    ad (x * endOfEquiv g) = ad x * endOfEquiv g := by
  ext v
  change a • x (g v) - x (g (a • v)) = a • x (g v) - x (a • g v)
  rw [map_smul]

variable [ValuativeRel E] (C : LatticeChain 𝒪[E] E V)

omit [ValuativeRel F] in
private theorem left_mul_mem_latticeMaps_iff (g : V ≃ₗ[E] V) {n : ℤ} {x : A} :
    endOfEquiv g * x ∈ latticeMaps C (C.linearEquivMap g) n ↔ x ∈ latticeMaps C C n := by
  change (∀ i v, v ∈ C.lattice i → g (x v) ∈ (C.linearEquivMap g).lattice (i + n)) ↔ _
  simp only [C.mem_linearEquivMap, g.symm_apply_apply]
  rfl

omit [ValuativeRel F] in
private theorem right_mul_mem_latticeMaps_iff (g : V ≃ₗ[E] V) {n : ℤ} {x : A} :
    x * endOfEquiv g ∈ latticeMaps (C.linearEquivMap g.symm) C n ↔ x ∈ latticeMaps C C n := by
  change (∀ i v, v ∈ (C.linearEquivMap g.symm).lattice i → x (g v) ∈ C.lattice (i + n)) ↔ _
  simp only [C.mem_linearEquivMap, LinearEquiv.symm_symm]
  constructor
  · intro h i v hv
    exact g.apply_symm_apply v ▸ h i (g.symm v) (by simpa only [g.apply_symm_apply] using hv)
  · exact fun h i v hv => h i (g v) hv

variable [TopologicalSpace E] [IsNonarchimedeanLocalField E]

/-- If two relative automorphisms satisfy a linear equation with corrections
in a base lattice step, the corrections can be taken relative at the same
depth. Interpolation uses a basis splitting the base chain over `E` and its
translate by the inverse of the right multiplier. -/
theorem exists_relative_corrections
    (L : LatticeChain 𝒪[F] F V) (hC : ∀ i v, v ∈ C.lattice i ↔ v ∈ L.lattice i)
    (y z : V ≃ₗ[E] V) {m : ℤ} {a b : A}
    (ha : a ∈ L.endFiltration m) (hb : b ∈ L.endFiltration m)
    (h : (1 + a) * endOfEquiv z = endOfEquiv y * (1 + b)) :
    ∃ a' b' : Module.End E V,
      a'.restrictScalars F ∈ L.endFiltration m ∧ b'.restrictScalars F ∈ L.endFiltration m ∧
        (1 + a') * z.toLinearMap = y.toLinearMap * (1 + b') := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨r, b₀, hb₀⟩ := C.exists_basis_splits hπ
  obtain ⟨s, c, hcz, hc⟩ := (C.linearEquivMap z.symm).exists_basis_splits_of_splits hπ C b₀ hb₀
  let rel (x : A) : Module.End E V := c.constr E fun j => x (c j)
  let a' := rel (a * endOfEquiv z) * z.symm.toLinearMap
  let b' := rel b
  have hmem {x : A} : x ∈ latticeMaps C C m ↔ x ∈ L.endFiltration m :=
    ⟨fun h i v hv => (hC _ _).mp (h i v ((hC _ _).mpr hv)),
      fun h i v hv => (hC _ _).mpr (h i v ((hC _ _).mp hv))⟩
  have haRel : a'.restrictScalars F * endOfEquiv z = basisLinearPart c (a * endOfEquiv z) := by
    apply LinearMap.ext
    intro v
    change rel (a * endOfEquiv z) (z.symm (z v)) = rel (a * endOfEquiv z) v
    rw [z.symm_apply_apply]
  refine ⟨a', b', ?_, ?_, ?_⟩
  · apply hmem.mp
    apply (right_mul_mem_latticeMaps_iff C z).mp
    rw [haRel]
    exact basisLinearPart_mem_latticeMaps hπ c hcz (period_linearEquivMap C z.symm)
      ((right_mul_mem_latticeMaps_iff C z).mpr (hmem.mpr ha))
  · exact hmem.mp (basisLinearPart_mem_latticeMaps hπ c hc rfl (hmem.mpr hb))
  · apply c.ext
    intro j
    have hj := LinearMap.congr_fun h (c j)
    simpa [a', b', rel, Module.End.mul_apply] using hj

/-- Lift an adjoint in one lattice step and a sum of three translated steps.
The input and output chains have common splitting bases over `E`. -/
theorem exists_mixed_adjoint_lift (L : LatticeChain 𝒪[F] F V)
    (hC : ∀ i v, v ∈ C.lattice i ↔ v ∈ L.lattice i)
    (hker : ∀ {x : A}, ad x = 0 → ∀ (t : E) v, x (t • v) = t • x v)
    (k : ℤ) (hLift : ∀ (m : ℤ) (x : A), ad x ∈ L.endFiltration (m + k) →
      ∃ z ∈ L.endFiltration m, ad z = ad x)
    (g₁ g₂ : V ≃ₗ[E] V) {i j m n : ℤ} {y p q w : A}
    (hy : y ∈ L.endFiltration i) (hp : p ∈ L.endFiltration (j + k))
    (hq : q ∈ L.endFiltration (m + k)) (hw : w ∈ L.endFiltration (n + k))
    (hsum : ad y = g₁.toLinearMap.restrictScalars F * p +
      q * g₂.toLinearMap.restrictScalars F + w) :
    ∃ x₁ ∈ L.endFiltration j, ∃ x₂ ∈ L.endFiltration m, ∃ x₃ ∈ L.endFiltration n,
      ad x₁ ∈ L.endFiltration (j + k) ∧ ad x₂ ∈ L.endFiltration (m + k) ∧
        ad x₃ ∈ L.endFiltration (n + k) ∧
        let z := g₁.toLinearMap.restrictScalars F * x₁ + x₂ * g₂.toLinearMap.restrictScalars F + x₃
        z ∈ L.endFiltration i ∧ ad z = ad y := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
  obtain ⟨r, b₀, hb₀⟩ := C.exists_basis_splits hπ
  obtain ⟨r₁, b, hb, hb'⟩ := (C.linearEquivMap g₁).exists_basis_splits_of_splits hπ C b₀ hb₀
  obtain ⟨r₂, c, hc, hc'⟩ := (C.linearEquivMap g₂.symm).exists_basis_splits_of_splits hπ C b₀ hb₀
  let R : Fin 3 → LatticeChain 𝒪[E] E V := ![C, C.linearEquivMap g₂.symm, C]
  let T : Fin 3 → LatticeChain 𝒪[E] E V := ![C.linearEquivMap g₁, C, C]
  let step : Fin 3 → ℤ := ![j + k, m + k, n + k]
  have hR : ∀ s, (R s).period = C.period := by
    intro s
    fin_cases s
    exacts [rfl, period_linearEquivMap C g₂.symm, rfl]
  have hT : ∀ s, (T s).period = C.period := by
    intro s
    fin_cases s
    exacts [period_linearEquivMap C g₁, rfl, rfl]
  have hcR : ∀ s, (R s).Splits c := by
    intro s
    fin_cases s
    exacts [hc', hc, hc']
  have hbT : ∀ s, (T s).Splits b := by
    intro s
    fin_cases s
    exacts [hb, hb', hb']
  have hmem {n : ℤ} {x : A} : x ∈ latticeMaps C C n ↔ x ∈ L.endFiltration n :=
    ⟨fun h l v hv => (hC _ _).mp (h l v ((hC _ _).mpr hv)),
      fun h l v hv => (hC _ _).mpr (h l v ((hC _ _).mp hv))⟩
  have hstart : ad y ∈ ⨆ s, latticeMaps (R s) (T s) (step s) := by
    rw [iSup_fin_three, hsum]
    exact AddSubgroup.add_mem_sup
      (AddSubgroup.add_mem_sup ((left_mul_mem_latticeMaps_iff C g₁).mpr (hmem.mpr hp))
        ((right_mul_mem_latticeMaps_iff C g₂).mpr (hmem.mpr hq))) (hmem.mpr hw)
  have hsplit := adjoint_mem_iSup_inf_range hπ b c R T step hcR hbT C.period hR hT a y hstart
  rw [iSup_fin_three] at hsplit
  obtain ⟨z₁₂, hz₁₂, z₃, hz₃, hz⟩ := AddSubgroup.mem_sup.mp hsplit
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := AddSubgroup.mem_sup.mp hz₁₂
  obtain ⟨u₁, hu₁⟩ := hz₁.2
  obtain ⟨u₂, hu₂⟩ := hz₂.2
  obtain ⟨u₃, hu₃⟩ := hz₃.2
  change ad u₁ = z₁ at hu₁
  change ad u₂ = z₂ at hu₂
  change ad u₃ = z₃ at hu₃
  have hz₁' : ad (endOfEquiv g₁.symm * u₁) ∈ L.endFiltration (j + k) := by
    apply hmem.mp
    apply (left_mul_mem_latticeMaps_iff C g₁).mp
    rw [adjoint_left_mul, ← mul_assoc, endOfEquiv_mul_symm, one_mul, hu₁]
    exact hz₁.1
  have hz₂' : ad (u₂ * endOfEquiv g₂.symm) ∈ L.endFiltration (m + k) := by
    apply hmem.mp
    apply (right_mul_mem_latticeMaps_iff C g₂).mp
    rw [adjoint_right_mul, mul_assoc, endOfEquiv_symm_mul, mul_one, hu₂]
    exact hz₂.1
  obtain ⟨v₁, hv₁, hv₁a⟩ := hLift j (endOfEquiv g₁.symm * u₁) hz₁'
  obtain ⟨v₂, hv₂, hv₂a⟩ := hLift m (u₂ * endOfEquiv g₂.symm) hz₂'
  obtain ⟨v₃, hv₃, hv₃a⟩ := hLift n u₃ (by rw [hu₃]; exact hmem.mp hz₃.1)
  let f : A →+ A := AddMonoidHom.id A - basisLinearPart c
  have hf_adj (x : A) : ad (f x) = ad x := by
    change ad (x - basisLinearPart c x) = ad x
    rw [map_sub, adjoint_basisLinearPart, sub_zero]
  have hf_mem {R T : LatticeChain 𝒪[E] E V} (hc : R.Splits c) (hper : R.period = T.period)
      {n : ℤ} {x : A} (hx : x ∈ latticeMaps R T n) : f x ∈ latticeMaps R T n :=
    (latticeMaps R T n).sub_mem hx (basisLinearPart_mem_latticeMaps hπ c hc hper hx)
  have hzero : ad (y - (endOfEquiv g₁ * v₁ + v₂ * endOfEquiv g₂ + v₃)) = 0 := by
    rw [map_sub, map_add, map_add, adjoint_left_mul, adjoint_right_mul, hv₁a, hv₂a, hv₃a,
      adjoint_left_mul, adjoint_right_mul, ← mul_assoc (endOfEquiv g₁),
      endOfEquiv_mul_symm, one_mul, mul_assoc (ad u₂), endOfEquiv_symm_mul, mul_one,
      hu₁, hu₂, hu₃, hz, sub_self]
  have hf_zero : f (y - (endOfEquiv g₁ * v₁ + v₂ * endOfEquiv g₂ + v₃)) = 0 := by
    change _ - basisLinearPart c _ = 0
    rw [basisLinearPart_eq_self c (hker hzero), AddMonoidHom.id_apply, sub_self]
  have hfy : f y = f (endOfEquiv g₁ * v₁) + f (v₂ * endOfEquiv g₂) + f v₃ := by
    simpa only [map_sub, map_add, sub_eq_zero] using hf_zero
  let x₁ := endOfEquiv g₁.symm * f (endOfEquiv g₁ * v₁)
  let x₂ := f (v₂ * endOfEquiv g₂) * endOfEquiv g₂.symm
  have hx₁ : endOfEquiv g₁ * x₁ = f (endOfEquiv g₁ * v₁) := by
    simp only [x₁, ← mul_assoc, endOfEquiv_mul_symm, one_mul]
  have hx₂ : x₂ * endOfEquiv g₂ = f (v₂ * endOfEquiv g₂) := by
    simp only [x₂, mul_assoc, endOfEquiv_symm_mul, mul_one]
  have hx₁a : ad x₁ = ad v₁ := by
    rw [show ad x₁ = ad (endOfEquiv g₁.symm * f (endOfEquiv g₁ * v₁)) from rfl,
      adjoint_left_mul, hf_adj, adjoint_left_mul, ← mul_assoc, endOfEquiv_symm_mul, one_mul]
  have hx₂a : ad x₂ = ad v₂ := by
    rw [show ad x₂ = ad (f (v₂ * endOfEquiv g₂) * endOfEquiv g₂.symm) from rfl,
      adjoint_right_mul, hf_adj, adjoint_right_mul, mul_assoc, endOfEquiv_mul_symm, mul_one]
  refine ⟨x₁, ?_, x₂, ?_, f v₃, hmem.mp (hf_mem hc' rfl (hmem.mpr hv₃)), ?_, ?_, ?_, ?_⟩
  · apply hmem.mp
    apply (left_mul_mem_latticeMaps_iff C g₁).mp
    rw [hx₁]
    exact hf_mem hc' (period_linearEquivMap C g₁).symm
      ((left_mul_mem_latticeMaps_iff C g₁).mpr (hmem.mpr hv₁))
  · apply hmem.mp
    apply (right_mul_mem_latticeMaps_iff C g₂).mp
    rw [hx₂]
    exact hf_mem hc (period_linearEquivMap C g₂.symm)
      ((right_mul_mem_latticeMaps_iff C g₂).mpr (hmem.mpr hv₂))
  · rwa [hx₁a, hv₁a]
  · rwa [hx₂a, hv₂a]
  · rw [hf_adj, hv₃a, hu₃]
    exact hmem.mp hz₃.1
  · change (endOfEquiv g₁ * x₁ + x₂ * endOfEquiv g₂ + f v₃) ∈ L.endFiltration i ∧
      ad (endOfEquiv g₁ * x₁ + x₂ * endOfEquiv g₂ + f v₃) = ad y
    rw [hx₁, hx₂, ← hfy]
    exact ⟨hmem.mp (hf_mem hc' rfl (hmem.mpr hy)), hf_adj y⟩

end Translations

end Langlands.BushnellKutzko
