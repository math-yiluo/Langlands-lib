import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceProof
import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.AdditiveDualityProof
import Langlands.BushnellKutzko.PureStratumApproximationChainImprovement
import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.SimpleCharacters
import Langlands.BushnellKutzko.SimpleStratumGroups
import Langlands.BushnellKutzko.StratumApproximationReduction

/-! # The refinement step in the proof of BK93 (3.5.9)

`SimpleStratumIntertwinedRefinementStatement` is the step of the proof of BK93 (3.5.9), printed
p. 122, that passes from a character `ψ_b` of `U^m(𝔅_β)` intertwined by `B_β^×` to a simple
stratum: by (2.4.11) applied over `E = F[β]`, the derived coset `s(b) + 𝔔^{1−m}` contains a
scalar of `E`, and the refinement theorem (2.2.8) (or, for the zero coset, the conjugation of
(2.2.1)) gives the new simple element. `simpleStratumIntertwinedRefinement` proves it. -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uE

/-- **The refinement step of BK93 (3.5.9)**, printed p. 122. Let `[𝔄,n,m,β]` be a simple
stratum with `m ≥ 1` and let `b ∈ 𝔓^{−m}`. Suppose the function `ψ_b(y) = ψ_F(tr(b(y − 1)))` on
`U^m(𝔅_β)` is intertwined by every element of `B_β^×`: `ψ_b(tyt⁻¹) = ψ_b(y)` whenever `t`
commutes with `β` and both `y` and `tyt⁻¹` lie in `U^m(𝔅_β)`. Then on the same chain there is a
simple stratum `[𝔄,n,m,β']` with `β' ≡ β + b (mod 𝔓^{1−m})`. The case `b = 0`, with zero derived
coset, is included (take `β' = β`). -/
def SimpleStratumIntertwinedRefinementStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V) (m : ℕ), S.r = m → 1 ≤ m → S.IsSimple →
    ∀ b ∈ S.chain.endFiltration (-(m : ℤ)),
      (∀ t ∈ centralizerUnitGroup S.b, ∀ y ∈ relativeUnitFiltration S.chain S.b m,
        t * y * t⁻¹ ∈ relativeUnitFiltration S.chain S.b m →
          elementCharacter (traceCharacter ψF) b (t * y * t⁻¹) =
            elementCharacter (traceCharacter ψF) b y) →
      ∃ T : Stratum 𝒪[F] F V, T.chain = S.chain ∧ T.n = S.n ∧ T.r = m ∧ T.IsSimple ∧
        T.b - (S.b + b) ∈ S.chain.endFiltration (1 - (m : ℤ))

section TraceDuality

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

/-- The trace pairing on `End_F(V)` is nondegenerate: `tr(aX) = 0` for all `a` forces `X = 0`. -/
theorem eq_zero_of_forall_trace_mul_eq_zero [FiniteDimensional F V] {X : A}
    (h : ∀ a : A, LinearMap.trace F V (a * X) = 0) : X = 0 := by
  ext v
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff F (X v)).mp fun f => ?_
  have h1 := h (f.smulRight v)
  have he : f.smulRight v * X = (f ∘ₗ X).smulRight v := by
    ext w
    simp [Module.End.mul_apply]
  rw [he, LinearMap.trace_smulRight] at h1
  simpa using h1

/-- Every linear form on `End_F(V)` is a trace form `a ↦ tr(az)`. -/
theorem exists_trace_mul_eq [FiniteDimensional F V] (φ : A →ₗ[F] F) :
    ∃ z : A, ∀ a : A, φ a = LinearMap.trace F V (a * z) := by
  let Φ : A →ₗ[F] Module.Dual F A := ((LinearMap.mul F A).flip).compr₂ (LinearMap.trace F V)
  have hΦ (z a : A) : Φ z a = LinearMap.trace F V (a * z) := rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    apply eq_zero_of_forall_trace_mul_eq_zero
    intro a
    rw [← hΦ, hz]
    rfl
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).mp hinj
  obtain ⟨z, hz⟩ := hsurj φ
  exact ⟨z, fun a => by rw [← hz, hΦ]⟩

end TraceDuality

section Decomposition

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

open StratumEquivalence

/-- **Dual form of an intertwining condition.** Let `t` be a unit and `D ∈ A`. Suppose
`tr(Dz) ∈ 𝔭_F` for every `z` commuting with `β` with `z ∈ 𝔓^{1−k}` and `tzt⁻¹ ∈ 𝔓^{1−k}`.
Then `D ∈ 𝔓^k + t⁻¹𝔓^k t + [β, A]`. -/
theorem exists_decomposition_of_trace_test (L : LatticeChain 𝒪[F] F V) (β : A) (k : ℤ) (t : G)
    (D : A)
    (h : ∀ z : A, β * z = z * β → z ∈ L.endFiltration (1 - k) →
      (t : A) * z * (↑t⁻¹ : A) ∈ L.endFiltration (1 - k) →
        LinearMap.trace F V (D * z) ∈ maximalIdealInField 𝒪[F] F) :
    ∃ p₁ ∈ L.endFiltration k, ∃ p₂ ∈ L.endFiltration k, ∃ y : A,
      D = p₁ + (↑t⁻¹ : A) * p₂ * (t : A) + (β * y - y * β) := by
  have := L.finiteDimensional
  by_contra hD
  let W : Submodule F A := LinearMap.range (adjointMap F β)
  let c : A →ₗ[F] A := LinearMap.mulLeft F (↑t⁻¹ : A) ∘ₗ LinearMap.mulRight F (t : A)
  have hc (a : A) : c a = (↑t⁻¹ : A) * a * (t : A) := by
    simp [c, mul_assoc]
  let P := L.endFiltration k
  let L' : Submodule 𝒪[F] A := P ⊔ P.map (c.restrictScalars 𝒪[F])
  let M : Submodule 𝒪[F] (A ⧸ W) := L'.map (W.mkQ.restrictScalars 𝒪[F])
  have hM : M.FG := ((L.fg_endFiltration k).sup ((L.fg_endFiltration k).map _)).map _
  have hL'M {a : A} (ha : a ∈ L') : W.mkQ a ∈ M := ⟨a, ha, rfl⟩
  have hv : W.mkQ D ∉ M := by
    rintro ⟨l, hl, hle⟩
    apply hD
    obtain ⟨p₁, hp₁, q, hq, rfl⟩ := Submodule.mem_sup.mp hl
    obtain ⟨p₂, hp₂, rfl⟩ := hq
    have hw : D - (p₁ + c p₂) ∈ W := by
      rw [← Submodule.Quotient.eq]
      exact hle.symm
    obtain ⟨y, hy⟩ := hw
    refine ⟨p₁, hp₁, p₂, hp₂, y, ?_⟩
    change adjointMap F β y = D - (p₁ + c p₂) at hy
    rw [adjointMap_apply] at hy
    rw [hy, ← hc]
    abel
  obtain ⟨f, hf, hfD⟩ := separates_fg_submodule (O := 𝒪[F]) (K := F) M hM hv
  obtain ⟨z, hz⟩ := exists_trace_mul_eq (f ∘ₗ W.mkQ)
  have hzv (a : A) : f (W.mkQ a) = LinearMap.trace F V (a * z) := hz a
  -- `z` commutes with `β`
  have hzβ : β * z = z * β := by
    have h0 : z * β - β * z = 0 := by
      apply eq_zero_of_forall_trace_mul_eq_zero
      intro y
      have h1 : f (W.mkQ (adjointMap F β y)) = 0 := by
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero W).mpr
          (LinearMap.mem_range_self _ y), map_zero]
      rw [hzv, adjointMap_apply] at h1
      rw [← h1, mul_sub, sub_mul, map_sub, map_sub, ← mul_assoc, ← mul_assoc,
        mul_assoc β y z, LinearMap.trace_mul_comm F β (y * z)]
    exact (sub_eq_zero.mp h0).symm
  -- `z ∈ 𝔓^{1−k}` and `tzt⁻¹ ∈ 𝔓^{1−k}`
  have hz1 : z ∈ L.endFiltration (1 - k) := by
    refine (L.mem_endFiltration_iff_trace_mul k z).mpr fun y hy => ?_
    rw [LinearMap.trace_mul_comm, ← hzv]
    exact hf _ (hL'M (Submodule.mem_sup_left hy))
  have hz2 : (t : A) * z * (↑t⁻¹ : A) ∈ L.endFiltration (1 - k) := by
    refine (L.mem_endFiltration_iff_trace_mul k _).mpr fun y hy => ?_
    have hcy : c y ∈ L' := Submodule.mem_sup_right ⟨y, hy, rfl⟩
    have h1 := hf _ (hL'M hcy)
    rw [hzv, hc] at h1
    have he : LinearMap.trace F V ((t : A) * z * (↑t⁻¹ : A) * y) =
        LinearMap.trace F V ((↑t⁻¹ : A) * y * (t : A) * z) := by
      rw [LinearMap.trace_mul_comm F ((t : A) * z * (↑t⁻¹ : A)) y,
        show y * ((t : A) * z * (↑t⁻¹ : A)) = (y * (t : A) * z) * (↑t⁻¹ : A) by
          simp only [mul_assoc],
        LinearMap.trace_mul_comm F (y * (t : A) * z) (↑t⁻¹ : A)]
      simp only [mul_assoc]
    rw [he]
    exact h1
  exact hfD (by rw [hzv]; exact h z hzβ hz1 hz2)

end Decomposition

section Linearization

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- A unit `g` with `g − 1 ∈ 𝔓^n`, `n ≥ 1`, lies in `U^n(𝔄)`. -/
theorem mem_unitFiltration_of_sub_one_mem (L : LatticeChain 𝒪[F] F V) {n : ℕ} (hn : 1 ≤ n)
    {g : G} (hg : (g : A) - 1 ∈ L.endFiltration n) : g ∈ L.unitFiltration n := by
  have h : (g : A) ∈ ((↑) : G → A) '' (L.unitFiltration n : Set G) := by
    rw [L.coe_image_unitFiltration hn]
    exact hg
  obtain ⟨g', hg', e⟩ := h
  rwa [Units.ext e] at hg'

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **Linearization of the intertwining condition.** If `ψ_b` on `U^m(𝔅_β)` is intertwined by
`t ∈ B_β^×`, then `tr((t⁻¹bt − b)z) ∈ 𝔭_F` for every `z ∈ 𝔓^m` commuting with `β` with
`tzt⁻¹ ∈ 𝔓^m`. -/
theorem trace_mem_of_intertwined (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (β b : A) {m : ℕ} (hm : 1 ≤ m)
    (hint : ∀ t ∈ centralizerUnitGroup β, ∀ y ∈ relativeUnitFiltration L β m,
      t * y * t⁻¹ ∈ relativeUnitFiltration L β m →
        elementCharacter (traceCharacter ψF) b (t * y * t⁻¹) =
          elementCharacter (traceCharacter ψF) b y)
    {t : G} (ht : t ∈ centralizerUnitGroup β) {z : A} (hzβ : β * z = z * β)
    (hz : z ∈ L.endFiltration m) (htz : (t : A) * z * (↑t⁻¹ : A) ∈ L.endFiltration m) :
    LinearMap.trace F V (((↑t⁻¹ : A) * b * t - b) * z) ∈ maximalIdealInField 𝒪[F] F := by
  rw [mem_maximalIdealInField_iff_annihilates_integers ψF hψ.1 hψ.2]
  intro a
  have hsmul {x : A} (hx : x ∈ L.endFiltration m) : (a : F) • x ∈ L.endFiltration m :=
    (L.endFiltration m).smul_mem a hx
  obtain ⟨y, hy, hyz⟩ := L.exists_mem_unitFiltration hm (hsmul hz)
  have hyβ : y ∈ centralizerUnitGroup β := by
    change β * (y : A) = (y : A) * β
    rw [hyz, mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, hzβ]
  have hyR : y ∈ relativeUnitFiltration L β m := ⟨hyβ, hy⟩
  have htyt : ((t * y * t⁻¹ : G) : A) = 1 + (a : F) • ((t : A) * z * (↑t⁻¹ : A)) := by
    rw [Units.val_mul, Units.val_mul, hyz, mul_add, add_mul, mul_one, Units.mul_inv,
      mul_smul_comm, smul_mul_assoc]
  have htytR : t * y * t⁻¹ ∈ relativeUnitFiltration L β m := by
    refine ⟨(centralizerUnitGroup β).mul_mem ((centralizerUnitGroup β).mul_mem ht hyβ)
      ((centralizerUnitGroup β).inv_mem ht), mem_unitFiltration_of_sub_one_mem L hm ?_⟩
    rw [htyt, add_sub_cancel_left]
    exact hsmul htz
  have h := hint t ht y hyR htytR
  rw [elementCharacter_apply, elementCharacter_apply, htyt, hyz, add_sub_cancel_left,
    add_sub_cancel_left, traceCharacter_apply, traceCharacter_apply] at h
  have he : (a : F) * LinearMap.trace F V (((↑t⁻¹ : A) * b * t - b) * z) =
      LinearMap.trace F V (b * ((a : F) • ((t : A) * z * (↑t⁻¹ : A)))) -
        LinearMap.trace F V (b * ((a : F) • z)) := by
    rw [mul_smul_comm, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub,
      sub_mul, map_sub]
    congr 2
    rw [show b * ((t : A) * z * (↑t⁻¹ : A)) = (b * (t : A) * z) * (↑t⁻¹ : A) by
        simp only [mul_assoc],
      LinearMap.trace_mul_comm F (b * (t : A) * z) (↑t⁻¹ : A)]
    simp only [mul_assoc]
  rw [he, sub_eq_add_neg, AddChar.map_add_eq_mul, h, ← AddChar.map_add_eq_mul, add_neg_cancel,
    AddChar.map_zero_eq_one]

/-- **The additive form of the intertwining condition.** Under the hypothesis of
`trace_mem_of_intertwined`, `t⁻¹bt − b ∈ 𝔓^{1−m} + t⁻¹𝔓^{1−m}t + [β, A]`. -/
theorem exists_decomposition_of_intertwined (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (L : LatticeChain 𝒪[F] F V) (β b : A) {m : ℕ} (hm : 1 ≤ m)
    (hint : ∀ t ∈ centralizerUnitGroup β, ∀ y ∈ relativeUnitFiltration L β m,
      t * y * t⁻¹ ∈ relativeUnitFiltration L β m →
        elementCharacter (traceCharacter ψF) b (t * y * t⁻¹) =
          elementCharacter (traceCharacter ψF) b y)
    {t : G} (ht : t ∈ centralizerUnitGroup β) :
    ∃ p₁ ∈ L.endFiltration (1 - (m : ℤ)), ∃ p₂ ∈ L.endFiltration (1 - (m : ℤ)), ∃ y : A,
      (↑t⁻¹ : A) * b * t - b = p₁ + (↑t⁻¹ : A) * p₂ * (t : A) + (β * y - y * β) := by
  apply exists_decomposition_of_trace_test L β (1 - (m : ℤ)) t
  intro z hzβ hz htz
  rw [sub_sub_cancel] at hz htz
  exact trace_mem_of_intertwined ψF hψ L β b hm hint ht hzβ hz htz

end Linearization

section RelativeCoset

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

/-- **The coset part of BK93 (2.4.11) over a normalizing field.** Let `E` act on `V` with `E^×`
normalizing the chain, and let `y ∈ B = End_E(V)`. If `xy − yx ∈ x𝔔^k + 𝔔^k x` for every
`x ∈ B^×`, where `𝔔^k = 𝔓^k ∩ B`, then `y ≡ δ (mod 𝔔^k)` for some `δ ∈ E`. The chain is read
over `𝔬_E` through `relativeLatticeChain`. -/
theorem exists_scalar_sub_mem_of_coset_intertwined (L : LatticeChain 𝒪[F] F V)
    (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer) (k : ℤ) (y : Module.End E V)
    (h : ∀ x : (Module.End E V)ˣ, ∃ p : Module.End E V, p.restrictScalars F ∈ L.endFiltration k ∧
      ∃ q : Module.End E V, q.restrictScalars F ∈ L.endFiltration k ∧
        (x : Module.End E V) * y - y * x = (x : Module.End E V) * p + q * x) :
    ∃ δ : E, y.restrictScalars F - subfieldEmbedding F E V δ ∈ L.endFiltration k := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  have hInt : ∀ a : E, IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[E] := isIntegral_iff_mem_spectralInteger F E
  let C := L.relativeLatticeChain hE hInt
  obtain ⟨c, hc⟩ := exists_algebraMap_sub_mem_of_coset_intertwined C k y fun x => by
    obtain ⟨p, hp, q, hq, e⟩ := h x
    exact ⟨p, (L.mem_relativeLatticeChain_endFiltration hE hInt k p).mpr hp, q,
      (L.mem_relativeLatticeChain_endFiltration hE hInt k q).mpr hq, e⟩
  exact ⟨c, (L.mem_relativeLatticeChain_endFiltration hE hInt k _).mp hc⟩

end RelativeCoset

/-- Two lattice chains with the same lattices are equal. -/
theorem LatticeChain.eq_of_lattice_coe_eq {O : Type*} {K : Type*} {V : Type*} [CommRing O]
    [Field K] [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    {L₁ L₂ : LatticeChain O K V} (h : ∀ i, (L₁.lattice i : Set V) = L₂.lattice i) : L₁ = L₂ := by
  obtain ⟨l₁, _, _, _⟩ := L₁
  obtain ⟨l₂, _, _, _⟩ := L₂
  have e : l₁ = l₂ := funext fun i => SetLike.coe_injective (h i)
  subst e
  rfl

section Steps

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

local notation "A" => Module.End F V
local notation "B" => Module.End E V

/-- **The derived commutator identity.** Let `β` be the image of `βE ∈ E` and let `s` be a tame
corestriction mapping each `𝔓^k` into `𝔔^k`. If `ψ_b` on `U^m(𝔅_β)` is intertwined by `B_β^×`,
then for every `x ∈ B^×` the commutator `x s(b) − s(b) x` lies in `x𝔔^{1−m} + 𝔔^{1−m}x`. -/
theorem corestriction_commutator_mem_of_intertwined (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (L : LatticeChain 𝒪[F] F V) {βE : E} {β b : A}
    (hβ : subfieldEmbedding F E V βE = β) {m : ℕ} (hm : 1 ≤ m)
    (hint : ∀ t ∈ centralizerUnitGroup β, ∀ y ∈ relativeUnitFiltration L β m,
      t * y * t⁻¹ ∈ relativeUnitFiltration L β m →
        elementCharacter (traceCharacter ψF) b (t * y * t⁻¹) =
          elementCharacter (traceCharacter ψF) b y)
    (s : TameCorestriction 𝒪[F] F E V)
    (hsmap : ∀ (k : ℤ) (z : A), z ∈ L.endFiltration k → (s z).restrictScalars F ∈ L.endFiltration k)
    (x : Bˣ) : ∃ p : B, p.restrictScalars F ∈ L.endFiltration (1 - (m : ℤ)) ∧
      ∃ q : B, q.restrictScalars F ∈ L.endFiltration (1 - (m : ℤ)) ∧
        (x : B) * s b - s b * x = (x : B) * p + q * x := by
  let restrict : B →* A :=
    { toFun := fun z => z.restrictScalars F
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let t := Units.map restrict x
  have ht : (t : A) = (x : B).restrictScalars F := rfl
  have hti : ((t⁻¹ : Aˣ) : A) = ((x⁻¹ : Bˣ) : B).restrictScalars F := rfl
  have htβ : t ∈ centralizerUnitGroup β := by
    change β * (t : A) = (t : A) * β
    rw [← hβ, subfieldEmbedding_eq_restrictScalars, ht]
    apply LinearMap.ext
    intro v
    exact ((x : B).map_smul βE v).symm
  obtain ⟨p₁, hp₁, p₂, hp₂, y, hy⟩ := exists_decomposition_of_intertwined ψF hψ L β b hm hint htβ
  refine ⟨s.toLinearMap (-p₁), hsmap _ _ (neg_mem hp₁), s.toLinearMap (-p₂),
    hsmap _ _ (neg_mem hp₂), ?_⟩
  have hs := congrArg s.toLinearMap hy
  have hconj (z : A) : s.toLinearMap ((↑t⁻¹ : A) * z * t) = (↑x⁻¹ : B) * s z * x := by
    rw [TameCorestriction.toLinearMap_apply, ht, hti]
    have h₁ : s (((x⁻¹ : Bˣ) : B).restrictScalars F * z * (x : B).restrictScalars F) =
        s (((x⁻¹ : Bˣ) : B).restrictScalars F * z) * x := s.map_mul_right _ _
    have h₂ : s (((x⁻¹ : Bˣ) : B).restrictScalars F * z) = (↑x⁻¹ : B) * s z :=
      s.map_mul_left _ _
    rw [h₁, h₂]
  have had : s.toLinearMap (β * y - y * β) = 0 := by
    rw [← hβ]
    exact s.adjointMap_eq_zero βE y
  rw [map_sub, map_add, map_add, hconj, hconj, had, add_zero] at hs
  simp only [TameCorestriction.toLinearMap_apply] at hs
  have e₂ := congrArg (fun w => (x : B) * w) hs
  simp only [mul_sub, mul_add, ← mul_assoc, Units.mul_inv, one_mul] at e₂
  rw [map_neg, map_neg, mul_neg, neg_mul, ← neg_add]
  simp only [TameCorestriction.toLinearMap_apply]
  rw [← e₂, neg_sub]

open PureApproximation in
/-- **Zero derived coset.** Let `[𝔄,n,r,β]` be simple, `b ∈ 𝔓^{−r}` and `s(b) ∈ 𝔓^{1−r}`. Then a
conjugate `g⁻¹βg` by some `g ∈ U¹(𝔄)` is the element of a simple stratum `[𝔄,n,r,g⁻¹βg]` with
`g⁻¹βg ≡ β + b (mod 𝔓^{1−r})`. The conjugating element comes from `exists_conj_sub_mem`
(BK93 (2.4.5), built on the exact sequence (1.4.10)). -/
theorem exists_simple_of_corestriction_mem (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {b : A} (hb : b ∈ S.chain.endFiltration (-S.r))
    (hsb : (s b).restrictScalars F ∈ S.chain.endFiltration (1 - S.r)) :
    ∃ T : Stratum 𝒪[F] F V, T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ T.IsSimple ∧
      T.b - (S.b + b) ∈ S.chain.endFiltration (1 - S.r) := by
  have hE := normalized_of_generated S hS.1 hβES hβE
  have hsb' : (s b).restrictScalars F ∈ S.chain.endFiltration (-(S.r - 1)) := by
    rw [neg_sub]
    exact hsb
  obtain ⟨g, p, hg1, hgi1, -, hp', -, hconj⟩ :=
    exists_conj_sub_mem S hS hβES hβE s S.chain hE hb hsb'
  have hone : (1 : A) ∈ S.chain.endFiltration 0 := S.chain.order.one_mem
  have hg0 : (g : A) ∈ S.chain.endFiltration 0 := by
    have h := add_mem hone (S.chain.endFiltration_antitone (by omega : (0 : ℤ) ≤ 1) hg1)
    rwa [add_sub_cancel] at h
  have hgi0 : ((g⁻¹ : Aˣ) : A) ∈ S.chain.endFiltration 0 := by
    have h := add_mem hone (S.chain.endFiltration_antitone (by omega : (0 : ℤ) ≤ 1) hgi1)
    rwa [add_sub_cancel] at h
  refine ⟨conjStratum S g hg0 hgi0, rfl, rfl, rfl, isSimple_conjStratum S g hg0 hgi0 hS, ?_⟩
  have hp'' : p ∈ S.chain.endFiltration (1 - S.r) := by
    rwa [neg_sub] at hp'
  set X := (g : A) * (S.b + b) * ((g⁻¹ : Aˣ) : A) with hX
  have hw : X - S.b ∈ S.chain.endFiltration (1 - S.r) := by
    have h := add_mem hconj hp''
    rwa [show X - (S.b + p) + p = X - S.b by abel] at h
  have h := S.chain.mul_mem_endFiltration (S.chain.mul_mem_endFiltration hgi0 hw) hg0
  simp only [zero_add, add_zero] at h
  have h₁ : ((g⁻¹ : Aˣ) : A) * X * (g : A) = S.b + b := by
    rw [hX]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
    rw [mul_assoc, Units.inv_mul, mul_one]
  have he : (conjStratum S g hg0 hgi0).b - (S.b + b) =
      -(((g⁻¹ : Aˣ) : A) * (X - S.b) * (g : A)) := by
    change ((g⁻¹ : Aˣ) : A) * S.b * g - (S.b + b) = _
    rw [mul_sub, sub_mul, h₁, neg_sub]
  rw [he]
  exact neg_mem h

open PureApproximation in
/-- **Nonzero derived coset: the refinement theorem.** Let `[𝔄,n,r,β]` be simple with `E = F[β]`,
let `b ∈ 𝔓^{−r}` and suppose `s(b) ≡ δ (mod 𝔓^{1−r})` for a scalar `δ ∈ E` with
`δ ∉ 𝔓^{1−r}`. Then `v_𝔄(b) = v_𝔄(δ) = −r`, the derived stratum `[𝔅,r,r−1,s(b)]` is
equivalent to the simple scalar stratum `[𝔅,r,r−1,δ]`, and BK93 (2.2.8) gives a simple stratum
`[𝔄,n,r−1,β']` with `β' ≡ β + b (mod 𝔓^{1−r})` and `k₀(β',𝔄) = max(k₀(β,𝔄), −∞) = k₀(β,𝔄)`.
Hence `[𝔄,n,r,β']` is simple as well. -/
theorem exists_simple_of_corestriction_sub_scalar_mem [FiniteDimensional F V]
    [FiniteDimensional F E] (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {b : A} (hb : b ∈ S.chain.endFiltration (-S.r))
    {δ : E} (hδ : (s b).restrictScalars F - subfieldEmbedding F E V δ ∈
      S.chain.endFiltration (1 - S.r))
    (hA : subfieldEmbedding F E V δ ∉ S.chain.endFiltration (1 - S.r)) :
    ∃ T : Stratum 𝒪[F] F V, T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r ∧ T.IsSimple ∧
      T.b - (S.b + b) ∈ S.chain.endFiltration (1 - S.r) := by
  have hE := normalized_of_generated S hS.1 hβES hβE
  have hsmap (k : ℤ) {z : A} (hz : z ∈ S.chain.endFiltration k) :
      (s z).restrictScalars F ∈ S.chain.endFiltration k := by
    have h := (tameCorestriction F V E).2.2 s S.chain hE k
    have hmem : s z ∈ s '' (S.chain.endFiltration k : Set A) := ⟨z, hz, rfl⟩
    rw [h] at hmem
    exact hmem
  have hsb : (s b).restrictScalars F ∈ S.chain.endFiltration (-S.r) := hsmap _ hb
  have hδm : subfieldEmbedding F E V δ ∈ S.chain.endFiltration (-S.r) := by
    have h := sub_mem hsb (S.chain.endFiltration_antitone (by omega : -S.r ≤ 1 - S.r) hδ)
    rwa [sub_sub_cancel] at h
  have hval_eq {z : A} (h1 : z ∈ S.chain.endFiltration (-S.r))
      (h2 : z ∉ S.chain.endFiltration (1 - S.r)) :
      S.chain.valuation z = ((-S.r : ℤ) : WithTop ℤ) := by
    have hv1 := le_valuation_of_mem S.chain h1
    have hv2 : ¬ ((1 - S.r : ℤ) : WithTop ℤ) ≤ S.chain.valuation z :=
      fun h => h2 (mem_endFiltration_of_le_valuation S.chain h)
    generalize S.chain.valuation z = v at hv1 hv2 ⊢
    induction v using WithTop.recTopCoe with
    | top => exact absurd le_top hv2
    | coe k =>
      have h1' : -S.r ≤ k := by exact_mod_cast hv1
      have h2' : ¬ 1 - S.r ≤ k := fun h => hv2 (by exact_mod_cast h)
      congr 1
      omega
  have hvδ := hval_eq hδm hA
  have hb1 : b ∉ S.chain.endFiltration (1 - S.r) := by
    intro hb1
    apply hA
    have h := sub_mem (hsmap _ hb1) hδ
    rwa [sub_sub_cancel] at h
  have hvb : S.chain.valuation b = (-S.r : WithTop ℤ) := by
    rw [hval_eq hb hb1]
    rfl
  have hrn := S.r_lt_n
  let D : Stratum (subfieldIntegers F E) E V :=
    ⟨S.chain.subfieldChain E hE, S.r, S.r - 1, s b, by omega, by
      rw [valuation_subfieldChain]
      exact_mod_cast le_valuation_of_mem S.chain hsb⟩
  have hD : S.IsDerivedStratum E b s D :=
    ⟨hS, ⟨βE, hβES, hβE⟩, hb, fun i => Set.ext fun v => Iff.rfl, rfl, rfl, rfl⟩
  obtain ⟨C, hClat, hCn, hCr, hCb, hCs⟩ := exists_scalar_simple S.chain hE (x := δ) hvδ
  have hCD : C.chain = D.chain := LatticeChain.eq_of_lattice_coe_eq fun i => hClat i
  have hDC : D.Equivalent C := by
    refine Stratum.equivalent_of_sub_mem hCD hCr ?_
    change s b - C.b ∈ D.chain.endFiltration (-(S.r - 1))
    rw [hCb, neg_sub]
    exact (mem_subfieldChain_endFiltration_iff S.chain hE).mpr hδ
  obtain ⟨T, hTc, hTn, -, hTs, hTcoset, -, -, hTk⟩ :=
    refinement F V E S b s D C hD hvb hCD hCn hCr hDC hCs
  have hCk : criticalExponent C.chain C.b = ⊥ := by
    rw [hCb]
    have hbot : Algebra.adjoin E ({algebraMap E B δ} : Set B) = ⊥ :=
      le_antisymm (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
        (Subalgebra.algebraMap_mem ⊥ δ))) bot_le
    unfold criticalExponent
    rw [ite_eq_left hbot]
  have hTk' : criticalExponent T.chain T.b < ((-S.r : ℤ) : WithBot ℤ) := by
    rw [hTk, hCk, max_bot_right]
    exact hS.2
  let T' : Stratum 𝒪[F] F V :=
    ⟨T.chain, T.n, S.r, T.b, by rw [hTn]; exact S.r_lt_n, T.valuation_ge⟩
  refine ⟨T', hTc, hTn, rfl, ⟨hTs.1, hTk'⟩, ?_⟩
  have hself : T.b ∈ T.coset := by
    change T.b - T.b ∈ T.chain.endFiltration (-T.r)
    rw [sub_self]
    exact zero_mem _
  rw [hTcoset] at hself
  exact hself

end Steps

/-- **The refinement step of BK93 (3.5.9)**, proved: see `SimpleStratumIntertwinedRefinement.md`. -/
theorem simpleStratumIntertwinedRefinement :
    SimpleStratumIntertwinedRefinementStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ ψF hψ S m hr hm hS b hb hint
  have := S.chain.finiteDimensional
  obtain ⟨hEf, hEn⟩ := hS.1.1
  let : Field (elementAlgebra S.b) := hEf.toField
  let : FiniteDimensional F (elementAlgebra S.b) :=
    inferInstanceAs (FiniteDimensional F (elementAlgebra S.b))
  obtain ⟨s⟩ := (tameCorestriction F V (elementAlgebra S.b)).1
  have hsmap (k : ℤ) (z : Module.End F V) (hz : z ∈ S.chain.endFiltration k) :
      (s z).restrictScalars F ∈ S.chain.endFiltration k := by
    have h := (tameCorestriction F V (elementAlgebra S.b)).2.2 s S.chain hEn k
    have hmem : s z ∈ s '' (S.chain.endFiltration k : Set (Module.End F V)) := ⟨z, hz, rfl⟩
    rw [h] at hmem
    exact hmem
  have hβES := subfieldEmbedding_elementGenerator S.b hEf
  have hβE := adjoin_elementGenerator (E := F) S.b
  have hbr : b ∈ S.chain.endFiltration (-S.r) := by rw [hr]; exact hb
  obtain ⟨δ, hδ⟩ := exists_scalar_sub_mem_of_coset_intertwined S.chain hEn (1 - (m : ℤ)) (s b)
    (corestriction_commutator_mem_of_intertwined ψF hψ S.chain hβES hm hint s hsmap)
  rw [← hr] at hδ ⊢
  by_cases hA : subfieldEmbedding F (elementAlgebra S.b) V δ ∈ S.chain.endFiltration (1 - S.r)
  · refine exists_simple_of_corestriction_mem S hS hβES hβE s hbr ?_
    have h := add_mem hδ hA
    rwa [sub_add_cancel] at h
  · exact exists_simple_of_corestriction_sub_scalar_mem S hS hβES hβE s hbr hδ hA

end Langlands.BushnellKutzko
