import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Transport of lattice chains and strata along semilinear equivalences

A semilinear equivalence `f : V₁ ≃ₛₗ[σ] V₂` over a field isomorphism `σ : K₁ → K₂`
conjugates `End_{K₁}(V₁)` onto `End_{K₂}(V₂)` by `x ↦ f x f⁻¹`. This file shows that
the filtrations, orders, unit groups, normalizers, valuations, adjoint lattices, critical
exponents and generated algebras of BK93 §1 correspond under this conjugation, so that
pure and simple strata correspond to pure and simple strata, and equivalent strata to
equivalent strata.
-/

noncomputable section

namespace Langlands.BushnellKutzko

section Semilinear

variable {O₁ K₁ V₁ O₂ K₂ V₂ : Type*}
  [CommRing O₁] [Field K₁] [Algebra O₁ K₁] [AddCommGroup V₁] [Module K₁ V₁] [Module O₁ V₁]
  [IsScalarTower O₁ K₁ V₁]
  [CommRing O₂] [Field K₂] [Algebra O₂ K₂] [AddCommGroup V₂] [Module K₂ V₂] [Module O₂ V₂]
  [IsScalarTower O₂ K₂ V₂]
  {σ : K₁ →+* K₂} {σ' : K₂ →+* K₁} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]

/-- Conjugation `x ↦ f ∘ x ∘ f⁻¹` of endomorphism rings by a semilinear equivalence. -/
abbrev endConj (f : V₁ ≃ₛₗ[σ] V₂) : Module.End K₁ V₁ ≃+* Module.End K₂ V₂ :=
  f.conjRingEquiv

theorem endConj_apply (f : V₁ ≃ₛₗ[σ] V₂) (x : Module.End K₁ V₁) (w : V₂) :
    endConj f x w = f (x (f.symm w)) :=
  rfl

@[simp] theorem endConj_apply_apply (f : V₁ ≃ₛₗ[σ] V₂) (x : Module.End K₁ V₁) (v : V₁) :
    endConj f x (f v) = f (x v) := by
  rw [endConj_apply, LinearEquiv.symm_apply_apply]

@[simp] theorem endConj_symm_endConj (f : V₁ ≃ₛₗ[σ] V₂) (x : Module.End K₁ V₁) :
    endConj f.symm (endConj f x) = x := by
  ext v
  simp

@[simp] theorem endConj_endConj_symm (f : V₁ ≃ₛₗ[σ] V₂) (y : Module.End K₂ V₂) :
    endConj f (endConj f.symm y) = y := by
  ext w
  simp

theorem endConj_algebraMap (f : V₁ ≃ₛₗ[σ] V₂) (c : K₁) :
    endConj f (algebraMap K₁ (Module.End K₁ V₁) c) =
      algebraMap K₂ (Module.End K₂ V₂) (σ c) := by
  ext w
  simp [Module.algebraMap_end_apply, LinearEquiv.map_smulₛₗ]

/-- Conjugation on the unit groups. -/
abbrev unitsConj (f : V₁ ≃ₛₗ[σ] V₂) : (Module.End K₁ V₁)ˣ ≃* (Module.End K₂ V₂)ˣ :=
  Units.mapEquiv (endConj f).toMulEquiv

@[simp] theorem coe_unitsConj (f : V₁ ≃ₛₗ[σ] V₂) (u : (Module.End K₁ V₁)ˣ) :
    ((unitsConj f u : (Module.End K₂ V₂)ˣ) : Module.End K₂ V₂) = endConj f u :=
  rfl

@[simp] theorem coe_unitsConj_inv (f : V₁ ≃ₛₗ[σ] V₂) (u : (Module.End K₁ V₁)ˣ) :
    (((unitsConj f u)⁻¹ : (Module.End K₂ V₂)ˣ) : Module.End K₂ V₂) =
      endConj f ((u⁻¹ : (Module.End K₁ V₁)ˣ) : Module.End K₁ V₁) :=
  rfl

/-! ### Submodules whose memberships correspond -/

section Membership

variable {R₁ R₂ A₁ A₂ : Type*} [Semiring R₁] [Semiring R₂] [AddCommMonoid A₁]
  [AddCommMonoid A₂] [Module R₁ A₁] [Module R₂ A₂]

theorem mem_sup_of_corresponds (e : A₁ ≃+ A₂) {X₁ Y₁ : Submodule R₁ A₁}
    {X₂ Y₂ : Submodule R₂ A₂} (hX : ∀ x, e x ∈ X₂ ↔ x ∈ X₁) (hY : ∀ x, e x ∈ Y₂ ↔ x ∈ Y₁)
    (x : A₁) : e x ∈ X₂ ⊔ Y₂ ↔ x ∈ X₁ ⊔ Y₁ := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨e.symm a, (hX _).1 (by simpa using ha), e.symm b, (hY _).1 (by simpa using hb), ?_⟩
    apply e.injective
    simp [hab]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨e a, (hX a).2 ha, e b, (hY b).2 hb, (map_add e a b).symm⟩

theorem le_iff_of_corresponds (e : A₁ ≃+ A₂) {X₁ Y₁ : Submodule R₁ A₁}
    {X₂ Y₂ : Submodule R₂ A₂} (hX : ∀ x, e x ∈ X₂ ↔ x ∈ X₁) (hY : ∀ x, e x ∈ Y₂ ↔ x ∈ Y₁) :
    X₂ ≤ Y₂ ↔ X₁ ≤ Y₁ := by
  constructor
  · intro hle x hx
    exact (hY x).1 (hle ((hX x).2 hx))
  · intro hle y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (hY x).2 (hle ((hX x).1 hy))

end Membership

/-! ### Lattice chains -/

namespace LatticeChain

/-- The lattice chain `L₂` is the image of `L₁` under `f`. -/
def Corresponds (f : V₁ ≃ₛₗ[σ] V₂) (L₁ : LatticeChain O₁ K₁ V₁)
    (L₂ : LatticeChain O₂ K₂ V₂) : Prop :=
  ∀ i v, v ∈ L₁.lattice i ↔ f v ∈ L₂.lattice i

variable {f : V₁ ≃ₛₗ[σ] V₂} {L₁ : LatticeChain O₁ K₁ V₁} {L₂ : LatticeChain O₂ K₂ V₂}

theorem Corresponds.symm (h : L₁.Corresponds f L₂) : L₂.Corresponds f.symm L₁ := by
  intro i w
  rw [h i (f.symm w), LinearEquiv.apply_symm_apply]

theorem Corresponds.mem_endFiltration (h : L₁.Corresponds f L₂) {n : ℤ}
    (x : Module.End K₁ V₁) : endConj f x ∈ L₂.endFiltration n ↔ x ∈ L₁.endFiltration n := by
  simp only [LatticeChain.mem_endFiltration]
  constructor
  · intro hx i v hv
    rw [h]
    simpa using hx i (f v) ((h i v).1 hv)
  · intro hx i w hw
    rw [endConj_apply]
    exact (h (i + n) _).1 (hx i _ ((h i (f.symm w)).2 (by simpa using hw)))

theorem Corresponds.mem_order (h : L₁.Corresponds f L₂) (x : Module.End K₁ V₁) :
    endConj f x ∈ L₂.order ↔ x ∈ L₁.order :=
  h.mem_endFiltration x

theorem Corresponds.valuation_eq (h : L₁.Corresponds f L₂) (x : Module.End K₁ V₁) :
    L₂.valuation (endConj f x) = L₁.valuation x := by
  have hset : {n : ℤ | endConj f x ∈ L₂.endFiltration n} = {n : ℤ | x ∈ L₁.endFiltration n} := by
    ext n
    exact h.mem_endFiltration x
  unfold LatticeChain.valuation
  rw [hset]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : endConj f x ≠ 0 := fun h0 =>
      hx ((endConj f).injective (h0.trans (map_zero (endConj f)).symm))
    simp only [hx, hx', ↓reduceIte]

theorem map_eq_lattice_iff {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (L : LatticeChain O K V) (g : (Module.End K V)ˣ) (i j : ℤ) :
    (L.lattice i).map ((g : Module.End K V).restrictScalars O) = L.lattice j ↔
      ∀ v, v ∈ L.lattice j ↔ ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ L.lattice i := by
  have hmem : ∀ v, v ∈ (L.lattice i).map ((g : Module.End K V).restrictScalars O) ↔
      ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) v ∈ L.lattice i := by
    intro v
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      change ((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) ((g : Module.End K V) u) ∈ _
      rwa [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]
    · intro hv
      refine ⟨_, hv, ?_⟩
      change (g : Module.End K V) (((g⁻¹ : (Module.End K V)ˣ) : Module.End K V) v) = v
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
  simp only [SetLike.ext_iff, hmem]
  exact forall_congr' fun v => Iff.comm

theorem Corresponds.mem_stabilizer (h : L₁.Corresponds f L₂) (u : (Module.End K₁ V₁)ˣ) :
    unitsConj f u ∈ L₂.stabilizer ↔ u ∈ L₁.stabilizer := by
  simp only [LatticeChain.mem_stabilizer, map_eq_lattice_iff, coe_unitsConj_inv]
  refine forall_congr' fun i => exists_congr fun j => ?_
  refine f.surjective.forall.trans (forall_congr' fun v => ?_)
  rw [endConj_apply_apply, ← h, ← h]

theorem Corresponds.mem_unitFiltration (h : L₁.Corresponds f L₂) {n : ℕ}
    (u : (Module.End K₁ V₁)ˣ) : unitsConj f u ∈ L₂.unitFiltration n ↔ u ∈ L₁.unitFiltration n := by
  simp only [LatticeChain.mem_unitFiltration, coe_unitsConj, coe_unitsConj_inv, h.mem_order]
  rw [← map_one (endConj f), ← map_sub, h.mem_endFiltration]

theorem Corresponds.order_eq_iff {M₁ : LatticeChain O₁ K₁ V₁} {M₂ : LatticeChain O₂ K₂ V₂}
    (h : L₁.Corresponds f L₂) (hM : M₁.Corresponds f M₂) :
    L₂.order = M₂.order ↔ L₁.order = M₁.order := by
  constructor
  · intro he
    ext x
    rw [← h.mem_order, ← hM.mem_order, he]
  · intro he
    ext y
    obtain ⟨x, rfl⟩ := (endConj f).surjective y
    rw [h.mem_order, hM.mem_order, he]

end LatticeChain

/-! ### Adjoint lattices and the critical exponent -/

theorem endConj_adjointMap (f : V₁ ≃ₛₗ[σ] V₂) (β x : Module.End K₁ V₁) :
    endConj f (adjointMap O₁ β x) = adjointMap O₂ (endConj f β) (endConj f x) := by
  simp [adjointMap, map_sub, map_mul]

namespace LatticeChain

variable {f : V₁ ≃ₛₗ[σ] V₂} {L₁ : LatticeChain O₁ K₁ V₁} {L₂ : LatticeChain O₂ K₂ V₂}

theorem Corresponds.mem_adjointLattice (h : L₁.Corresponds f L₂) {β : Module.End K₁ V₁}
    {k : ℤ} (x : Module.End K₁ V₁) :
    endConj f x ∈ adjointLattice L₂ (endConj f β) k ↔ x ∈ adjointLattice L₁ β k := by
  simp only [adjointLattice, Submodule.mem_inf, Submodule.mem_comap]
  rw [← endConj_adjointMap (O₁ := O₁) (O₂ := O₂), h.mem_endFiltration, h.mem_endFiltration]

theorem Corresponds.mem_centralizerLattice (h : L₁.Corresponds f L₂) {β : Module.End K₁ V₁}
    {k : ℤ} (x : Module.End K₁ V₁) :
    endConj f x ∈ centralizerLattice L₂ (endConj f β) k ↔ x ∈ centralizerLattice L₁ β k := by
  simp only [centralizerLattice, Submodule.mem_inf, LinearMap.mem_ker]
  rw [← endConj_adjointMap (O₁ := O₁) (O₂ := O₂), h.mem_endFiltration]
  have hz : ∀ y : Module.End K₁ V₁, endConj f y = 0 ↔ y = 0 := fun y =>
    ⟨fun h0 => (endConj f).injective (h0.trans (map_zero (endConj f)).symm),
      fun h0 => by rw [h0, map_zero]⟩
  rw [hz]

theorem Corresponds.criticalIndexSet_eq (h : L₁.Corresponds f L₂) (β : Module.End K₁ V₁) :
    criticalIndexSet L₂ (endConj f β) = criticalIndexSet L₁ β := by
  ext k
  change ¬ _ ↔ ¬ _
  rw [le_iff_of_corresponds (endConj f).toAddEquiv (fun x => h.mem_adjointLattice x)
    (mem_sup_of_corresponds (endConj f).toAddEquiv (fun x => h.mem_centralizerLattice x)
      (fun x => h.mem_endFiltration x))]

end LatticeChain

theorem endConj_mem_bot (f : V₁ ≃ₛₗ[σ] V₂) {x : Module.End K₁ V₁}
    (hx : x ∈ (⊥ : Subalgebra K₁ (Module.End K₁ V₁))) :
    endConj f x ∈ (⊥ : Subalgebra K₂ (Module.End K₂ V₂)) := by
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  rw [endConj_algebraMap]
  exact Subalgebra.algebraMap_mem _ _

theorem endConj_mem_bot_iff (f : V₁ ≃ₛₗ[σ] V₂) (x : Module.End K₁ V₁) :
    endConj f x ∈ (⊥ : Subalgebra K₂ (Module.End K₂ V₂)) ↔
      x ∈ (⊥ : Subalgebra K₁ (Module.End K₁ V₁)) := by
  refine ⟨fun hx => ?_, endConj_mem_bot f⟩
  simpa using endConj_mem_bot f.symm hx

theorem adjoin_singleton_eq_bot_iff {K A : Type*} [Field K] [Ring A] [Algebra K A] (β : A) :
    Algebra.adjoin K ({β} : Set A) = ⊥ ↔ β ∈ (⊥ : Subalgebra K A) := by
  rw [← le_bot_iff, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
  rfl

theorem elementAlgebra_endConj_eq_bot_iff (f : V₁ ≃ₛₗ[σ] V₂) (β : Module.End K₁ V₁) :
    elementAlgebra (endConj f β) = ⊥ ↔ elementAlgebra β = ⊥ := by
  rw [elementAlgebra, elementAlgebra, adjoin_singleton_eq_bot_iff, adjoin_singleton_eq_bot_iff,
    endConj_mem_bot_iff]

theorem LatticeChain.Corresponds.criticalExponent_eq {f : V₁ ≃ₛₗ[σ] V₂}
    {L₁ : LatticeChain O₁ K₁ V₁} {L₂ : LatticeChain O₂ K₂ V₂} (h : L₁.Corresponds f L₂)
    (β : Module.End K₁ V₁) :
    criticalExponent L₂ (endConj f β) = criticalExponent L₁ β := by
  have hb := elementAlgebra_endConj_eq_bot_iff f β
  simp only [elementAlgebra] at hb
  unfold criticalExponent
  rw [h.criticalIndexSet_eq β]
  by_cases h0 : Algebra.adjoin K₁ ({β} : Set (Module.End K₁ V₁)) = ⊥
  · simp only [hb, h0, ↓reduceIte]
  · simp only [hb, h0, ↓reduceIte]

/-! ### Generated algebras -/

theorem endConj_mem_elementAlgebra (f : V₁ ≃ₛₗ[σ] V₂) {β x : Module.End K₁ V₁}
    (hx : x ∈ elementAlgebra β) : endConj f x ∈ elementAlgebra (endConj f β) := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff.1 hy]
    exact Algebra.subset_adjoin rfl
  | algebraMap c =>
    rw [endConj_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact mul_mem hy hz

theorem endConj_mem_elementAlgebra_iff (f : V₁ ≃ₛₗ[σ] V₂) (β x : Module.End K₁ V₁) :
    endConj f x ∈ elementAlgebra (endConj f β) ↔ x ∈ elementAlgebra β := by
  refine ⟨fun hx => ?_, endConj_mem_elementAlgebra f⟩
  simpa using endConj_mem_elementAlgebra f.symm hx

/-- Conjugation restricts to a ring isomorphism `K₁[β] ≃ K₂[f β f⁻¹]`. -/
def elementAlgebraConj (f : V₁ ≃ₛₗ[σ] V₂) (β : Module.End K₁ V₁) :
    elementAlgebra β ≃+* elementAlgebra (endConj f β) where
  toFun a := ⟨endConj f (a : Module.End K₁ V₁), endConj_mem_elementAlgebra f a.2⟩
  invFun b := ⟨endConj f.symm (b : Module.End K₂ V₂),
    by simpa using endConj_mem_elementAlgebra f.symm b.2⟩
  left_inv a := Subtype.ext (endConj_symm_endConj f (a : Module.End K₁ V₁))
  right_inv b := Subtype.ext (endConj_endConj_symm f (b : Module.End K₂ V₂))
  map_mul' a b := Subtype.ext (map_mul (endConj f) (a : Module.End K₁ V₁) b)
  map_add' a b := Subtype.ext (map_add (endConj f) (a : Module.End K₁ V₁) b)

@[simp] theorem coe_elementAlgebraConj (f : V₁ ≃ₛₗ[σ] V₂) (β : Module.End K₁ V₁)
    (a : elementAlgebra β) :
    ((elementAlgebraConj f β a : elementAlgebra (endConj f β)) : Module.End K₂ V₂) =
      endConj f (a : Module.End K₁ V₁) :=
  rfl

theorem isField_elementAlgebra_endConj_iff (f : V₁ ≃ₛₗ[σ] V₂) (β : Module.End K₁ V₁) :
    IsField (elementAlgebra (endConj f β)) ↔ IsField (elementAlgebra β) :=
  (elementAlgebraConj f β).toMulEquiv.isField_congr.symm

/-! ### Pure and simple strata -/

namespace Stratum

/-- The normalization condition of a pure stratum, written without a field structure on
the generated algebra: units of `A` lying with their inverses in `E` normalize the chain. -/
theorem isPure_iff {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (S : Stratum O K V) :
    S.IsPure ↔ IsField (elementAlgebra S.b) ∧
      (∀ u : (Module.End K V)ˣ, (u : Module.End K V) ∈ elementAlgebra S.b →
        ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) ∈ elementAlgebra S.b →
          u ∈ S.chain.stabilizer) ∧
      S.chain.valuation S.b = (-S.n : WithTop ℤ) := by
  unfold IsPure
  constructor
  · rintro ⟨⟨hF, hU⟩, hv⟩
    refine ⟨hF, fun u hu hu' => ?_, hv⟩
    let := hF.toField
    let a : (elementAlgebra S.b)ˣ :=
      ⟨⟨u, hu⟩, ⟨_, hu'⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
    have h := hU a
    convert h using 1
    exact Units.ext (LinearMap.ext fun _ => rfl)
  · rintro ⟨hF, hU, hv⟩
    refine ⟨⟨hF, fun a => ?_⟩, hv⟩
    let := hF.toField
    exact hU _ (a : elementAlgebra S.b).2 ((a⁻¹ : (elementAlgebra S.b)ˣ) : elementAlgebra S.b).2

/-- The stratum `S₂` is the image of `S₁` under `f`. -/
structure Corresponds (f : V₁ ≃ₛₗ[σ] V₂) (S₁ : Stratum O₁ K₁ V₁) (S₂ : Stratum O₂ K₂ V₂) :
    Prop where
  chain : S₁.chain.Corresponds f S₂.chain
  n : S₂.n = S₁.n
  r : S₂.r = S₁.r
  b : S₂.b = endConj f S₁.b

variable {f : V₁ ≃ₛₗ[σ] V₂} {S₁ : Stratum O₁ K₁ V₁} {S₂ : Stratum O₂ K₂ V₂}

theorem Corresponds.symm (h : S₁.Corresponds f S₂) : S₂.Corresponds f.symm S₁ :=
  ⟨h.chain.symm, h.n.symm, h.r.symm, by rw [h.b, endConj_symm_endConj]⟩

theorem Corresponds.isPure_iff (h : S₁.Corresponds f S₂) : S₂.IsPure ↔ S₁.IsPure := by
  rw [Stratum.isPure_iff, Stratum.isPure_iff, h.b, h.n, h.chain.valuation_eq,
    isField_elementAlgebra_endConj_iff]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  refine (unitsConj f).surjective.forall.trans (forall_congr' fun u => ?_)
  rw [coe_unitsConj, coe_unitsConj_inv, endConj_mem_elementAlgebra_iff,
    endConj_mem_elementAlgebra_iff, h.chain.mem_stabilizer]

theorem Corresponds.criticalExponent_eq (h : S₁.Corresponds f S₂) :
    criticalExponent S₂.chain S₂.b = criticalExponent S₁.chain S₁.b := by
  rw [h.b, h.chain.criticalExponent_eq]

theorem Corresponds.isSimple_iff (h : S₁.Corresponds f S₂) : S₂.IsSimple ↔ S₁.IsSimple := by
  unfold IsSimple
  rw [h.isPure_iff, h.criticalExponent_eq, h.r]

theorem Corresponds.mem_coset (h : S₁.Corresponds f S₂) (x : Module.End K₁ V₁) :
    endConj f x ∈ S₂.coset ↔ x ∈ S₁.coset := by
  change endConj f x - S₂.b ∈ S₂.chain.endFiltration (-S₂.r) ↔
    x - S₁.b ∈ S₁.chain.endFiltration (-S₁.r)
  rw [h.b, h.r, ← map_sub, h.chain.mem_endFiltration]

theorem Corresponds.equivalent_iff {T₁ : Stratum O₁ K₁ V₁} {T₂ : Stratum O₂ K₂ V₂}
    (h : S₁.Corresponds f S₂) (hT : T₁.Corresponds f T₂) :
    S₂.Equivalent T₂ ↔ S₁.Equivalent T₁ := by
  unfold Equivalent
  constructor
  · intro he
    ext x
    rw [← h.mem_coset, ← hT.mem_coset, he]
  · intro he
    ext y
    obtain ⟨x, rfl⟩ := (endConj f).surjective y
    rw [h.mem_coset, hT.mem_coset, he]

/-- The image of a stratum, on a given image of its lattice chain. -/
def transport (S : Stratum O₁ K₁ V₁) (f : V₁ ≃ₛₗ[σ] V₂) (L : LatticeChain O₂ K₂ V₂)
    (hL : S.chain.Corresponds f L) : Stratum O₂ K₂ V₂ where
  chain := L
  n := S.n
  r := S.r
  b := endConj f S.b
  r_lt_n := S.r_lt_n
  valuation_ge := by
    rw [hL.valuation_eq]
    exact S.valuation_ge

theorem corresponds_transport (S : Stratum O₁ K₁ V₁) (f : V₁ ≃ₛₗ[σ] V₂)
    (L : LatticeChain O₂ K₂ V₂) (hL : S.chain.Corresponds f L) :
    S.Corresponds f (S.transport f L hL) :=
  ⟨hL, rfl, rfl, rfl⟩

end Stratum

/-! ### Construction of the image of a lattice chain -/

section Construction

variable {σO : O₁ →+* O₂} {σO' : O₂ →+* O₁} [RingHomInvPair σO σO'] [RingHomInvPair σO' σO]

/-- `f` viewed as semilinear over the rings of integers. -/
def integerSemilinear (f : V₁ ≃ₛₗ[σ] V₂)
    (hσ : ∀ o, σ (algebraMap O₁ K₁ o) = algebraMap O₂ K₂ (σO o)) : V₁ ≃ₛₗ[σO] V₂ where
  toFun := f
  invFun := f.symm
  map_add' := map_add f
  map_smul' o v := by
    rw [← algebraMap_smul K₁ o v, LinearEquiv.map_smulₛₗ, hσ, algebraMap_smul]
  left_inv := f.left_inv
  right_inv := f.right_inv

theorem map_ideal_ringJacobson (σO : O₁ →+* O₂) (hσO : Function.Bijective σO) :
    Ideal.map σO (Ring.jacobson O₁) = Ring.jacobson O₂ := by
  rw [← Ideal.jacobson_bot, ← Ideal.jacobson_bot, Ideal.map_jacobson_of_bijective hσO,
    Ideal.map_bot]

theorem map_smul_semilinear {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂]
    [Module O₁ M₁] [Module O₂ M₂] (e : M₁ ≃ₛₗ[σO] M₂) (I : Ideal O₁) (N : Submodule O₁ M₁) :
    (I • N).map (e : M₁ →ₛₗ[σO] M₂) = I.map σO • N.map (e : M₁ →ₛₗ[σO] M₂) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine Submodule.smul_le.2 fun r hr n hn => ?_
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.map_smulₛₗ]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem σO hr) (Submodule.mem_map_of_mem hn)
  · refine Submodule.smul_le.2 fun r hr m hm => ?_
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective σO
      (RingHomSurjective.is_surjective)).1 hr
    obtain ⟨n, hn, rfl⟩ := Submodule.mem_map.1 hm
    rw [← LinearMap.map_smulₛₗ]
    exact Submodule.mem_map_of_mem (Submodule.smul_mem_smul hx hn)

/-- The image of a lattice chain under a semilinear equivalence compatible with
semilinear isomorphisms of the rings of integers. -/
def LatticeChain.transport (L : LatticeChain O₁ K₁ V₁) (f : V₁ ≃ₛₗ[σ] V₂)
    (hσ : ∀ o, σ (algebraMap O₁ K₁ o) = algebraMap O₂ K₂ (σO o)) :
    LatticeChain O₂ K₂ V₂ where
  lattice i := (L.lattice i).map (integerSemilinear f hσ : V₁ →ₛₗ[σO] V₂)
  isLattice i :=
    { fg := (L.isLattice i).fg.map _
      span_eq_top := by
        rw [Submodule.map_coe]
        change Submodule.span K₂ ((f : V₁ →ₛₗ[σ] V₂) '' (L.lattice i : Set V₁)) = ⊤
        rw [← Submodule.map_span, (L.isLattice i).span_eq_top, Submodule.map_top,
          LinearMap.range_eq_top]
        exact f.surjective }
  lattice_succ_lt i :=
    Submodule.map_strictMono_of_injective (integerSemilinear f hσ).injective
      (L.lattice_succ_lt i)
  exists_period := by
    obtain ⟨e, he, hper⟩ := L.exists_period
    refine ⟨e, he, fun i => ?_⟩
    have hbij : Function.Bijective σO :=
      ⟨fun a b hab => by
        simpa [RingHomInvPair.comp_apply_eq (σ := σO) (σ' := σO')] using congrArg σO' hab,
        fun b => ⟨σO' b, RingHomInvPair.comp_apply_eq₂⟩⟩
    rw [hper, map_smul_semilinear, map_ideal_ringJacobson σO hbij]

theorem LatticeChain.corresponds_transport (L : LatticeChain O₁ K₁ V₁) (f : V₁ ≃ₛₗ[σ] V₂)
    (hσ : ∀ o, σ (algebraMap O₁ K₁ o) = algebraMap O₂ K₂ (σO o)) :
    L.Corresponds f (L.transport f hσ) := by
  intro i v
  change v ∈ L.lattice i ↔ f v ∈ (L.lattice i).map (integerSemilinear f hσ : V₁ →ₛₗ[σO] V₂)
  rw [Submodule.mem_map_equiv]
  change _ ↔ f.symm (f v) ∈ _
  rw [LinearEquiv.symm_apply_apply]

end Construction

end Semilinear

end Langlands.BushnellKutzko
