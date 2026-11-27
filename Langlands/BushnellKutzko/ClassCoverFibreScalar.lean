import Langlands.BushnellKutzko.ClassCoverDet
import Langlands.BushnellKutzko.CentralizerCharacterDual
import Langlands.BushnellKutzko.SimpleCharacterTransferComparison
import Langlands.BushnellKutzko.SimpleCharacterTransferIntersection
import Langlands.BushnellKutzko.SimpleStratumAdjointLayers
import Langlands.BushnellKutzko.SplitObstructionLattice
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof

/-! # Covering simple-character classes: the fibre characters (BK94 p. 120) -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

section Corestriction

variable {E : Type uV} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

/-- For finite-dimensional `V` and an intermediate field `E` whose units normalize `L`, a tame
corestriction relative to `E/F` is surjective. -/
theorem tameCorestriction_surjective [FiniteDimensional F V] (L : LatticeChain 𝒪[F] F V)
    (hnorm : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) (s : TameCorestriction 𝒪[F] F E V) :
    Function.Surjective s := by
  intro w
  obtain ⟨j, hj⟩ := SplitObstruction.exists_mem_endFiltration L (w.restrictScalars F)
  have h := (tameCorestriction F V E).2.2 s L hnorm j
  have hw : w ∈ s '' (L.endFiltration j : Set A) := by
    rw [h]
    exact hj
  obtain ⟨a, -, ha⟩ := hw
  exact ⟨a, ha⟩

/-- For finite-dimensional `V` and an intermediate field `E` whose units normalize `L`, a tame
corestriction relative to `E/F` carries `𝔓^j(𝔄)` into the `E`-linear endomorphisms lying in
`𝔓^j(𝔄)`. -/
theorem tameCorestriction_mem [FiniteDimensional F V] (L : LatticeChain 𝒪[F] F V)
    (hnorm : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) (s : TameCorestriction 𝒪[F] F E V)
    (j : ℤ) {y : A} (hy : y ∈ L.endFiltration j) :
    (s y).restrictScalars F ∈ L.endFiltration j := by
  have h := (tameCorestriction F V E).2.2 s L hnorm j
  have h' : s y ∈ s '' (L.endFiltration j : Set A) := ⟨y, hy, rfl⟩
  rw [h] at h'
  exact h'

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem TameCorestriction.apply_mul_left {O : Type*} [CommRing O] [Algebra O F] [Module O V]
    [IsScalarTower O F V] (s : TameCorestriction O F E V) (b : Module.End E V) (x : A) :
    s (b.restrictScalars F * x) = b * s x :=
  s.map_mul_left b x

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem TameCorestriction.apply_mul_right {O : Type*} [CommRing O] [Algebra O F] [Module O V]
    [IsScalarTower O F V] (s : TameCorestriction O F E V) (x : A) (b : Module.End E V) :
    s (x * b.restrictScalars F) = s x * b :=
  s.map_mul_right x b

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem TameCorestriction.apply_add {O : Type*} [CommRing O] [Algebra O F] [Module O V]
    [IsScalarTower O F V] (s : TameCorestriction O F E V) (x y : A) : s (x + y) = s x + s y :=
  map_add s.toAddMonoidHom x y

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem TameCorestriction.apply_sub {O : Type*} [CommRing O] [Algebra O F] [Module O V]
    [IsScalarTower O F V] (s : TameCorestriction O F E V) (x y : A) : s (x - y) = s x - s y :=
  map_sub s.toAddMonoidHom x y

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem TameCorestriction.apply_zero {O : Type*} [CommRing O] [Algebra O F] [Module O V]
    [IsScalarTower O F V] (s : TameCorestriction O F E V) : s 0 = 0 :=
  map_zero s.toAddMonoidHom

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A tame corestriction commutes with the scalars of `F`. -/
theorem tameCorestriction_smul (s : TameCorestriction 𝒪[F] F E V) (c : F) (y : A) :
    s (c • y) = scalarEnd (algebraMap F E c) * s y := by
  have h := s.map_mul_left (scalarEnd (algebraMap F E c)) y
  have e : (scalarEnd (algebraMap F E c) : Module.End E V).restrictScalars F * y = c • y := by
    ext v
    simp [scalarEnd, algebraMap_smul]
  rw [e] at h
  exact h

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A tame corestriction kills the commutators with elements of `E`. -/
theorem tameCorestriction_adjoint (s : TameCorestriction 𝒪[F] F E V) (c : E) (x : A) :
    s (subfieldEmbedding F E V c * x - x * subfieldEmbedding F E V c) = 0 := by
  have h1 : s (subfieldEmbedding F E V c * x) = scalarEnd c * s x := by
    have h := s.map_mul_left (scalarEnd c) x
    rw [restrictScalars_scalarEnd] at h
    exact h
  have h2 : s (x * subfieldEmbedding F E V c) = s x * scalarEnd c := by
    have h := s.map_mul_right x (scalarEnd c)
    rw [restrictScalars_scalarEnd] at h
    exact h
  have h3 : scalarEnd c * s x = s x * scalarEnd c := by
    ext v
    simp [scalarEnd]
  change s.toAddMonoidHom (_ - _) = 0
  rw [map_sub]
  change s (subfieldEmbedding F E V c * x) - s (x * subfieldEmbedding F E V c) = 0
  rw [h1, h2, h3, sub_self]

end Corestriction

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The trace form `ψ_A` is invariant under `ab ↦ ba`. -/
theorem traceCharacter_mul_comm [FiniteDimensional F V] (ψF : AddChar F ℂ) (x y : A) :
    traceCharacter ψF (x * y) = traceCharacter ψF (y * x) := by
  rw [traceCharacter_apply, traceCharacter_apply, LinearMap.trace_mul_comm]

/-- Let `V` be finite-dimensional and `F[γ]` a field whose units normalize `L`. The kernel of a
tame corestriction relative to `F[γ]/F` consists of trace-zero elements. -/
theorem trace_eq_zero_of_tameCorestriction [FiniteDimensional F V] (L : LatticeChain 𝒪[F] F V)
    (γ : A) (hE : IsField (elementAlgebra γ)) :
    letI := hE.toField
    (∀ a : (elementAlgebra γ)ˣ, subfieldUnits F (elementAlgebra γ) V a ∈ L.stabilizer) →
    ∀ (s : TameCorestriction 𝒪[F] F (elementAlgebra γ) V) (y : A), s y = 0 →
      LinearMap.trace F V y = 0 := by
  let := hE.toField
  intro hnorm s y hy
  by_cases hbot : elementAlgebra γ = ⊥
  · have hy0 : y = 0 := by
      apply SplitObstruction.eq_zero_of_forall_mem L
      intro j
      refine mem_endFiltration_of_tameCorestriction_scalar (E := elementAlgebra γ)
        (fun c => ?_) L hnorm s j ?_
      · have hc : (c : A) ∈ (⊥ : Subalgebra F A) := hbot ▸ c.2
        obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hc
        exact ⟨a, Subtype.ext ha⟩
      · rw [hy]
        exact zero_mem _
    rw [hy0, map_zero]
  · have : FiniteDimensional F (elementAlgebra γ) :=
      Module.Finite.of_injective (elementAlgebra γ).val.toLinearMap Subtype.val_injective
    obtain ⟨-, -, -, ⟨k₀, -, hk₀⟩, hex⟩ := adjointExactness F V (elementAlgebra γ) L
      (elementGenerator γ) (adjoin_elementGenerator γ)
      (not_exists_algebraMap_elementGenerator γ hbot) hnorm
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    obtain ⟨t, ht⟩ := L.exists_uniformizer_pow_mem_endFiltration hϖ y k₀
    obtain ⟨-, h2, -, -⟩ := hex s k₀ k₀ 1 (le_of_eq hk₀) le_rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, hmid⟩ := h2
    have hs : (s (((ϖ : F) ^ t) • y)).restrictScalars F ∈ (⊥ : AddSubgroup A) := by
      rw [tameCorestriction_smul, hy, mul_zero]
      rfl
    obtain ⟨x, -, hx⟩ := (hmid _ ht).mp hs
    have hx' : ((ϖ : F) ^ t) • y = subfieldEmbedding F (elementAlgebra γ) V (elementGenerator γ) * x -
        x * subfieldEmbedding F (elementAlgebra γ) V (elementGenerator γ) := by
      have := (AddSubgroup.mem_bot).mp hx
      rw [sub_eq_zero] at this
      rw [this]
      rfl
    have htr := congrArg (LinearMap.trace F V) hx'
    rw [map_sub, LinearMap.trace_mul_comm F (subfieldEmbedding F _ V _), sub_self, map_smul,
      smul_eq_mul] at htr
    have hϖ0 : ((ϖ : F) ^ t) ≠ 0 := pow_ne_zero _ (by
      intro h
      exact hϖ.ne_zero (Subtype.ext h))
    exact (mul_eq_zero.mp htr).resolve_left hϖ0

section Pushforward

variable {E : Type uV} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]

open Classical in
/-- The character `ψ_A` transported along a tame corestriction `s : A → B`: its value at `w ∈ B`
is `ψ_A(a)` for a preimage `a` of `w` (and `1` if there is none). -/
def corestrictedTrace (ψF : AddChar F ℂ) (s : TameCorestriction 𝒪[F] F E V)
    (w : Module.End E V) : ℂ :=
  if h : ∃ a, s a = w then traceCharacter ψF h.choose else 1

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- If the kernel of `s` consists of trace-zero elements, `corestrictedTrace` is the
pushforward of `ψ_A`. -/
theorem corestrictedTrace_apply (ψF : AddChar F ℂ) (s : TameCorestriction 𝒪[F] F E V)
    (hker : ∀ y, s y = 0 → LinearMap.trace F V y = 0) (a : A) :
    corestrictedTrace ψF s (s a) = traceCharacter ψF a := by
  have h : ∃ a', s a' = s a := ⟨a, rfl⟩
  rw [corestrictedTrace, dite_eq_left h]
  have hs : s (h.choose - a) = 0 := by
    rw [s.apply_sub]
    exact sub_eq_zero.mpr h.choose_spec
  have htr := hker _ hs
  calc traceCharacter ψF h.choose = traceCharacter ψF (a + (h.choose - a)) := by
        congr 1
        abel
    _ = traceCharacter ψF a := by
        rw [AddChar.map_add_eq_mul, traceCharacter_apply ψF (h.choose - a), htr,
          AddChar.map_zero_eq_one, mul_one]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Let `C` be a lattice chain over an intermediate field `E` whose lattices have the same
underlying sets as those of `L` at every index. A unit of `End_E(V)` in `U^m` of `C` lies, as a
unit of `End_F(V)`, in `U^m(𝔄)`. -/
theorem relativeEndUnits_mem_unitFiltration [ValuativeRel F] {O : Type*} [CommRing O]
    [Algebra O E] [Module O V] [IsScalarTower O E V] {L : LatticeChain 𝒪[F] F V}
    {C : LatticeChain O E V} (hlat : ∀ i, (C.lattice i : Set V) = L.lattice i) {m : ℕ}
    {x : (Module.End E V)ˣ} (hx : x ∈ C.unitFiltration m) :
    relativeEndUnits E x ∈ L.unitFiltration m := by
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · exact (mem_endFiltration_restrictScalars hlat (k := 0)).mp h1
  · exact (mem_endFiltration_restrictScalars hlat (k := 0)).mp h2
  · exact (mem_endFiltration_restrictScalars hlat).mp h3

end Pushforward

set_option maxHeartbeats 1000000 in
/-- **The scalar step used in the proof of BK94 (2.7)** (printed p. 121), derived here by the
elementary-matrix argument of `exists_scalar_of_det_invariant` instead of BK93 (2.4.11). Let
`ψ_F` be trivial on `𝔭_F` and nontrivial on `𝔬_F`, and assume that, whenever `E = F[γ]` is a
field, its units normalize `L`. If `x ↦ ψ_A(e(x - 1))` on the relative units in `U^{k+1}(𝔄)`
depends only on the determinant over `E`, then every tame corestriction relative to `E/F` carries
`e` to a scalar of `E` modulo `𝔓^{-k}`. -/
theorem corestrictionScalarMod_of_det [FiniteDimensional F V] (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) (γ e : A) (k : ℕ)
    (hEn : ∀ hE : IsField (elementAlgebra γ), letI := hE.toField
      ∀ a : (elementAlgebra γ)ˣ, subfieldUnits F (elementAlgebra γ) V a ∈ L.stabilizer)
    (hdet : ∀ hE : IsField (elementAlgebra γ), letI := hE.toField
      ∀ x x' : (Module.End (elementAlgebra γ) V)ˣ,
        relativeEndUnits (elementAlgebra γ) x ∈ L.unitFiltration (k + 1) →
        relativeEndUnits (elementAlgebra γ) x' ∈ L.unitFiltration (k + 1) →
        LinearMap.det (x : Module.End (elementAlgebra γ) V) =
          LinearMap.det (x' : Module.End (elementAlgebra γ) V) →
        elementCharacter (traceCharacter ψF) e (relativeEndUnits (elementAlgebra γ) x) =
          elementCharacter (traceCharacter ψF) e (relativeEndUnits (elementAlgebra γ) x')) :
    CorestrictionScalarMod L γ e k := by
  intro hE
  let := hE.toField
  intro s
  have hnorm := hEn hE
  have : FiniteDimensional F (elementAlgebra γ) :=
    Module.Finite.of_injective (elementAlgebra γ).val.toLinearMap Subtype.val_injective
  have hsurj := tameCorestriction_surjective L hnorm s
  have hker := trace_eq_zero_of_tameCorestriction L γ hE hnorm s
  let ℓ := corestrictedTrace ψF s
  have hℓ : ∀ a, ℓ (s a) = traceCharacter ψF a := corestrictedTrace_apply ψF s hker
  have hzero : ℓ 0 = 1 := by
    have h := hℓ 0
    rw [s.apply_zero, AddChar.map_zero_eq_one] at h
    exact h
  have hadd : ∀ w w', ℓ (w + w') = ℓ w * ℓ w' := by
    intro w w'
    obtain ⟨a, rfl⟩ := hsurj w
    obtain ⟨a', rfl⟩ := hsurj w'
    rw [← s.apply_add, hℓ, hℓ, hℓ, AddChar.map_add_eq_mul]
  have hcyc : ∀ w w', ℓ (w * w') = ℓ (w' * w) := by
    intro w w'
    obtain ⟨a, rfl⟩ := hsurj w
    rw [← s.apply_mul_right, ← s.apply_mul_left, hℓ, hℓ, traceCharacter_mul_comm]
  let B : LatticeChain (subfieldIntegers F (elementAlgebra γ)) (elementAlgebra γ) V :=
    L.extensionChain hnorm
  let := LocalField.FiniteExtension.normedField F (elementAlgebra γ)
  let := LocalField.FiniteExtension.valuativeRel F (elementAlgebra γ)
  have := LocalField.FiniteExtension.isLocalField F (elementAlgebra γ)
  have : IsScalarTower 𝒪[elementAlgebra γ] (elementAlgebra γ) V :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let φ := subfieldIntegerEquiv F (elementAlgebra γ)
  let C := B.transfer φ (fun _ => rfl)
  have hlat (i : ℤ) : (C.lattice i : Set V) = L.lattice i := rfl
  have hdetC : ∀ x x' : (Module.End (elementAlgebra γ) V)ˣ, x ∈ C.unitFiltration (k + 1) →
      x' ∈ C.unitFiltration (k + 1) →
      LinearMap.det (x : Module.End (elementAlgebra γ) V) =
        LinearMap.det (x' : Module.End (elementAlgebra γ) V) →
      ℓ (s e * ((x : Module.End (elementAlgebra γ) V) - 1)) =
        ℓ (s e * ((x' : Module.End (elementAlgebra γ) V) - 1)) := by
    intro x x' hx hx' hxx'
    rw [← s.apply_mul_right, ← s.apply_mul_right, hℓ, hℓ]
    exact hdet hE x x' (relativeEndUnits_mem_unitFiltration hlat hx)
      (relativeEndUnits_mem_unitFiltration hlat hx') hxx'
  obtain ⟨δ, hδ⟩ := exists_scalar_of_det_invariant C k ℓ hzero hadd hcyc (s e) hdetC
  obtain ⟨a, ha⟩ := hsurj (s e - scalarEnd δ)
  have hdual : a ∈ additiveDual (traceCharacter ψF)
      (centralizerLattice L γ ((k : ℤ) + 1) : Set A) := by
    intro y hy
    obtain ⟨hyP, hyc⟩ := hy
    have hcomm : Commute γ y := by
      have h := LinearMap.mem_ker.mp hyc
      rw [StratumEquivalence.adjointMap_apply, sub_eq_zero] at h
      exact h
    let Y : Module.End (elementAlgebra γ) V :=
      { toFun := y, map_add' := y.map_add, map_smul' := map_smul_elementAlgebra_of_commute hcomm }
    have hY : Y.restrictScalars F = y := rfl
    have hYC : Y ∈ C.endFiltration ((k : ℤ) + 1) := (mem_endFiltration_restrictScalars hlat).mpr hyP
    have h1 := hδ Y hYC
    rw [← ha, ← s.apply_mul_right, hℓ, hY] at h1
    exact h1
  have hmem := (mem_dual_centralizerLattice_iff L ψF hψ γ a ((k : ℤ) + 1)).mp hdual
  obtain ⟨p, hp, r, hr, hpr⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨x, hx⟩ := hr
  have hsr : s r = 0 := by
    rw [← hx]
    have h := tameCorestriction_adjoint s (elementGenerator γ) x
    rw [subfieldEmbedding_elementGenerator γ hE] at h
    exact h
  have hsa : s a = s p := by
    rw [← hpr, s.apply_add, hsr, add_zero]
  have hpk := tameCorestriction_mem L hnorm s _ hp
  have heq : (s e).restrictScalars F - subfieldEmbedding F (elementAlgebra γ) V δ =
      (s p).restrictScalars F := by
    rw [← hsa, ha, ← restrictScalars_scalarEnd]
    rfl
  refine ⟨δ, ?_⟩
  rw [heq]
  convert hpk using 2
  ring

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- **BK93 (3.2.1)(b), (3.2.3)(a).** For any additive character, any list `tail` and any index
`m` below the critical depth of `β`, every element of `simpleCharacters` at index `m` factors
through the determinant of the centralizer `B_β` on its intersection with `B_β^×`; this is a
clause of the definition. -/
theorem simpleCharacters_factorsThroughCentralizerDet (ψF : AddChar F ℂ)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (β : A) (tail : List A) (m : ℕ)
    (hm : (m : ℤ) < finiteCriticalDepth L n β)
    {θ : simpleHGroup L n β tail (m + 1) →* ℂˣ} (hθ : θ ∈ simpleCharacters ψF L n β tail m) :
    factorsThroughCentralizerDet β θ := by
  cases tail with
  | nil =>
    rw [simpleCharacters] at hθ
    exact hθ.2
  | cons γ tail =>
    rw [simpleCharacters] at hθ
    simp only at hθ
    rw [ite_eq_left hm] at hθ
    exact hθ.1

/-- Equal pairs have equal values. -/
theorem CharacterPair.apply_eq_of_eq {G' : Type*} [Group G'] {P Q : CharacterPair G'} (h : P = Q)
    (g : G') (hP : g ∈ P.1) (hQ : g ∈ Q.1) : P.2 ⟨g, hP⟩ = Q.2 ⟨g, hQ⟩ := by
  subst h
  rfl

variable (ψF : AddChar F ℂ)

set_option maxHeartbeats 1000000 in
/-- `FibreCharacterAt`, for `ψ_F` trivial on `𝔭_F` and nontrivial on `𝔬_F`: the quotient of two
extensions, an auxiliary step of the proof of BK94 (2.7). -/
theorem fibreCharacterAt [FiniteDimensional F V]
    (hChoice : SimpleCharacterChoiceStatement.{uF, uV}) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (n : ℤ) (k : ℕ) : FibreCharacterAt ψF L n k := by
  intro T ϑ ϑ' hϑ hϑ' hres
  obtain ⟨hTL, hTn, hTr, hTs⟩ := T.2
  have hϑ₀ := hϑ
  simp only [simpleCharacterPairs, Set.mem_iUnion, Set.mem_image] at hϑ₀
  obtain ⟨q, θ, hθ, rfl⟩ := hϑ₀
  rw [simpleCharacterPairs_eq_choiceImage_of_le ψF hChoice hψ T.1 k
    (by rw [hTr]; push_cast; omega) hTs q] at hϑ'
  obtain ⟨θ', hθ', rfl⟩ := hϑ'
  refine ⟨rfl, ?_⟩
  let H := simpleHGroup T.1.chain T.1.n T.1.b q.tail (k + 1)
  have hH : H ≤ L.unitFiltration (k + 1) :=
    (simpleHGroup_le_unitFiltration T.1.chain T.1.n T.1.b q.tail (k + 1)).trans
      (le_of_eq (congrArg (fun M : LatticeChain 𝒪[F] F V => M.unitFiltration (k + 1)) hTL))
  let χ : H →* ℂˣ := θ' * θ⁻¹
  have hχ : ∀ h : H, (h : G) ∈ L.unitFiltration (k + 2) → χ h = 1 := by
    intro h hh
    have h1 := CharacterPair.apply_eq_of_eq hres h ⟨h.2, hh⟩ ⟨h.2, hh⟩
    change θ h = θ' h at h1
    change θ' h * (θ h)⁻¹ = 1
    rw [h1, mul_inv_cancel]
  obtain ⟨e, he, hev⟩ := exists_elementCharacter_of_trivial_succ ψF hψ L k H hH χ hχ
  have hχθ : ∀ h : H, θ' h = χ h * θ h := by
    intro h
    change θ' h = θ' h * (θ h)⁻¹ * θ h
    rw [inv_mul_cancel_right]
  have hk : (k : ℤ) < finiteCriticalDepth T.1.chain T.1.n T.1.b := by
    have h := lt_finiteCriticalDepth_of_criticalExponent_lt T.1.r_lt_n hTs.2
    rw [hTr] at h
    push_cast at h
    omega
  have hθdet := simpleCharacters_factorsThroughCentralizerDet ψF T.1.chain T.1.n T.1.b q.tail k
    hk hθ
  have hθ'det := simpleCharacters_factorsThroughCentralizerDet ψF T.1.chain T.1.n T.1.b q.tail k
    hk hθ'
  refine ⟨e, he, ?_, fun g => ⟨g.2, g.2, ?_⟩⟩
  · apply corestrictionScalarMod_of_det ψF hψ L T.1.b e k
    · intro hE
      obtain ⟨hEf, hEn⟩ := hTs.1.1
      rw [hTL] at hEn
      exact hEn
    · intro hE x x' hx hx' hxx'
      let := hE.toField
      have hcomm (y : (Module.End (elementAlgebra T.1.b) V)ˣ) :
          relativeEndUnits (elementAlgebra T.1.b) y ∈ centralizerUnitGroup T.1.b := by
        have h := commute_subfieldEmbedding (F := F) (y : Module.End (elementAlgebra T.1.b) V)
          (elementGenerator T.1.b)
        rw [subfieldEmbedding_elementGenerator T.1.b hE] at h
        exact h
      have hxH : relativeEndUnits (elementAlgebra T.1.b) x ∈ H :=
        relativeUnitFiltration_le_simpleHGroup T.1.chain T.1.n T.1.b q.tail (k + 1)
          ⟨hcomm x, by rw [hTL]; exact hx⟩
      have hx'H : relativeEndUnits (elementAlgebra T.1.b) x' ∈ H :=
        relativeUnitFiltration_le_simpleHGroup T.1.chain T.1.n T.1.b q.tail (k + 1)
          ⟨hcomm x', by rw [hTL]; exact hx'⟩
      rw [← hev ⟨_, hxH⟩, ← hev ⟨_, hx'H⟩]
      congr 1
      change θ' ⟨_, hxH⟩ * (θ ⟨_, hxH⟩)⁻¹ = θ' ⟨_, hx'H⟩ * (θ ⟨_, hx'H⟩)⁻¹
      rw [factorsThroughCentralizerDet_apply_eq hθ'det hE x x' hxH hx'H hxx',
        factorsThroughCentralizerDet_apply_eq hθdet hE x x' hxH hx'H hxx']
  · change (θ' g : ℂ) = (θ g : ℂ) * elementCharacter (traceCharacter ψF) e g
    rw [hχθ g, Units.val_mul, hev g, mul_comm]

end Langlands.BushnellKutzko
