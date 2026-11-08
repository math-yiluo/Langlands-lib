import Mathlib.Algebra.Colimit.Module
import Langlands.Topology.GroupAction.CompactLocallyConstantStabilizer
import Langlands.Shimura.DefiniteFormsFunctions
import Langlands.Shimura.DefiniteFormsTower

/-!
# Harris's `D_m(K_ℓ)` and the forms of level `K(n)` along the tower `K_ℓ(n)`

Harris (1999, p.308) introduces the module `D_m(K_ℓ) = C(K_ℓ, 𝒪/ℓ^m𝒪)` of continuous functions
on `K_ℓ` with right translation, the forms `𝒜_ℓ(GJ, D_m(K_ℓ), K)` "defined by analogy with
(3.7)", a tower `K_ℓ(n)` with levels `K(n) = K_ℓ(n) × K^ℓ`, and the restriction (3.10) of the
forms of level `K(n)` to the double cosets, with values in `[D_m(K_ℓ)^N]^{K_ℓ(n)}`, a sum of
copies of `D_m(K_{ℓ,n})`. This module lets `n` vary: it relates `D_m(K_ℓ)` to the
`D_m(K_{ℓ,n})` and the forms with coefficients in `D_m(K_ℓ)` to the forms of all levels `K(n)`.
The coefficient ring `𝒪/ℓ^m𝒪` is an arbitrary commutative ring `R`, and continuous functions
with discrete values are locally constant functions.

## Main definitions and results

* `FunctionModule.rightStabilizer f`, `FunctionModule.isSmooth_rightRegular`: on a compact group,
  the right translations fixing a locally constant function form an open subgroup, so the right
  regular representation (Harris's `D_m(K_ℓ)`) is smooth.
* `CongruenceTower.exists_lower_apply_mul`, `CongruenceTower.iSup_fixedVectors_rightRegular`: for
  a tower `K_ℓ(n)` of a compact group, every locally constant function is fixed by some `K_ℓ(n)`.
* `CongruenceTower.directLimitEquiv`: the locally constant functions on a compact group are the
  direct limit of the functions on the quotients `G ⧸ K_ℓ(n)`, `D_m(K_ℓ) = lim→ D_m(K_{ℓ,n})`.
* In `Langlands.Shimura.DefiniteForms`: `congruenceForms σ ℓ R M H` (Harris's
  `𝒜_ℓ(GJ, M, K(n))`), `towerForms σ ℓ T R M` (the union over `n` of the forms of level `K(n)`)
  and `towerAction` (right translation by `K` on it).
* `towerFunctionEquiv`: Harris's (3.10) along the tower, under (3.6), for compact `K`: the union
  over `n` of the forms of level `K(n)` is `D(K_ℓ)` with values in the functions on the double
  cosets, as representations of `K`.
* `functionFormsEquiv`: for compact `K` with finitely many double cosets, `f ↦ (g ↦ f g 1)`
  identifies `𝒜_ℓ(GJ, D(K_ℓ), K)` (with values in `M`) with the union over `n` of the forms of
  level `K(n)` with values in `M`.
-/

noncomputable section

namespace Langlands.Shimura.FunctionModule

universe uG uR uM

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {M : Type uM}

/-- On a compact group `G`, the elements `h` with `f (x * h) = f x` for all `x` form an open
subgroup, for a locally constant `f`: the published `functionStabilizer` of `f` for the action
of `Gᵐᵒᵖ` on `G` by right multiplication, transported to `G`. -/
def rightStabilizer (f : LocallyConstant G M) : OpenSubgroup G :=
  ⟨(Langlands.CompactAction.functionStabilizer Gᵐᵒᵖ f).unop,
    (Langlands.CompactAction.functionStabilizer_isOpen Gᵐᵒᵖ f).preimage
      MulOpposite.continuous_op⟩

@[simp]
lemma mem_rightStabilizer {f : LocallyConstant G M} {h : G} :
    h ∈ rightStabilizer f ↔ ∀ x, f (x * h) = f x :=
  Iff.rfl

variable (R : Type uR) [CommRing R] [AddCommGroup M] [Module R M]

/-- On a compact group, the right regular representation on the locally constant functions
(Harris's `D_m(K_ℓ)`) is smooth: `rightStabilizer f` fixes `f`. -/
theorem isSmooth_rightRegular : IsSmooth (rightRegular R G M) := fun f =>
  ⟨rightStabilizer f, (Representation.mem_invariants _ f).2 fun h =>
    LocallyConstant.ext fun x => mem_rightStabilizer.1 h.2 x⟩

end Langlands.Shimura.FunctionModule

namespace Langlands.CongruenceTower

open Langlands.Shimura.FunctionModule

universe uG uR uM

variable {G : Type uG} [Group G] [TopologicalSpace G] (T : CongruenceTower G) {M : Type uM}

section Compact

variable [IsTopologicalGroup G] [CompactSpace G]

/-- On a compact group, a locally constant function is invariant under right translation by
some `K_ℓ(n)`. -/
theorem exists_lower_apply_mul (f : LocallyConstant G M) :
    ∃ n, ∀ x : G, ∀ h ∈ T.lower n, f (x * h) = f x := by
  obtain ⟨n, hn⟩ := T.exists_lower_le (rightStabilizer f)
  exact ⟨n, fun x h hh => mem_rightStabilizer.1 (hn hh) x⟩

variable (R : Type uR) [CommRing R] [AddCommGroup M] [Module R M]

/-- On a compact group, every locally constant function is fixed by some `K_ℓ(n)` under right
translation. -/
theorem exists_mem_fixedVectors_rightRegular (f : LocallyConstant G M) :
    ∃ n, f ∈ fixedVectors (rightRegular R G M) (T.lower n) := by
  obtain ⟨n, hn⟩ := T.exists_lower_apply_mul f
  exact ⟨n, (Representation.mem_invariants _ f).2 fun h =>
    LocallyConstant.ext fun x => hn x h.1 h.2⟩

/-- On a compact group, the locally constant functions are the union of the functions fixed by
the `K_ℓ(n)`. -/
theorem iSup_fixedVectors_rightRegular :
    ⨆ n, fixedVectors (rightRegular R G M) (T.lower n) = ⊤ :=
  (T.isSmooth_iff_iSup _).1 (isSmooth_rightRegular R)

end Compact

section DirectLimit

variable (R : Type uR) [CommRing R] [AddCommGroup M] [Module R M]

/-- For `m ≤ n`, the pullback of functions along `G ⧸ K_ℓ(n) → G ⧸ K_ℓ(m)`. -/
def quotientFunctionsMap {m n : ℕ} (h : m ≤ n) :
    (G ⧸ T.lower m → M) →ₗ[R] (G ⧸ T.lower n → M) :=
  LinearMap.funLeft R M (Subgroup.quotientMapOfLE (T.antitone h))

/-- `quotientFunctionsMap` evaluated at a coset `[y]` of `K_ℓ(n)`. -/
@[simp]
lemma quotientFunctionsMap_apply_mk {m n : ℕ} (h : m ≤ n) (φ : G ⧸ T.lower m → M) (y : G) :
    T.quotientFunctionsMap R h φ (y : G ⧸ T.lower n) = φ (y : G ⧸ T.lower m) :=
  rfl

/-- The pullbacks `quotientFunctionsMap` form a directed system. -/
instance directedSystem_quotientFunctions :
    DirectedSystem (fun n => G ⧸ T.lower n → M) fun _ _ h => T.quotientFunctionsMap R h where
  map_self _ φ := funext fun q => by
    induction q using QuotientGroup.induction_on with
    | H y => rfl
  map_map _ _ _ _ _ φ := funext fun q => by
    induction q using QuotientGroup.induction_on with
    | H y => rfl

variable [IsTopologicalGroup G]

/-- A function on `G ⧸ K_ℓ(n)` as a locally constant function on `G`. -/
def quotientFunctionsPullback (n : ℕ) : (G ⧸ T.lower n → M) →ₗ[R] LocallyConstant G M where
  toFun φ := (invariantsPullback (R := R) (T.isOpen_lower n) φ).1
  map_add' _ _ := LocallyConstant.ext fun _ => rfl
  map_smul' _ _ := LocallyConstant.ext fun _ => rfl

/-- `quotientFunctionsPullback n φ` is `y ↦ φ [y]`. -/
@[simp]
lemma quotientFunctionsPullback_apply (n : ℕ) (φ : G ⧸ T.lower n → M) (y : G) :
    T.quotientFunctionsPullback R n φ y = φ (y : G ⧸ T.lower n) :=
  rfl

/-- The pullbacks are compatible with the transition maps `quotientFunctionsMap`. -/
lemma quotientFunctionsPullback_map (m n : ℕ) (h : m ≤ n) (φ : G ⧸ T.lower m → M) :
    T.quotientFunctionsPullback R n (T.quotientFunctionsMap R h φ) =
      T.quotientFunctionsPullback R m φ :=
  LocallyConstant.ext fun _ => rfl

/-- Pulling back along the surjection `G → G ⧸ K_ℓ(n)` is injective. -/
lemma quotientFunctionsPullback_injective (n : ℕ) :
    Function.Injective (T.quotientFunctionsPullback R (M := M) n) := fun φ ψ h =>
  funext fun q => by
    induction q using QuotientGroup.induction_on with
    | H y => exact DFunLike.congr_fun h y

/-- The pullback intertwines right translation on the functions on `G ⧸ K_ℓ(n)` with right
translation on the locally constant functions on `G`. -/
lemma quotientFunctionsPullback_comm (n : ℕ) (g : G) (φ : G ⧸ T.lower n → M) :
    T.quotientFunctionsPullback R n
        (functionRightRegular R (G ⧸ T.lower n) M (g : G ⧸ T.lower n) φ) =
      rightRegular R G M g (T.quotientFunctionsPullback R n φ) :=
  LocallyConstant.ext fun _ => rfl

variable [CompactSpace G]

/-- For a compact group `G`, the locally constant functions on `G` (Harris's `D_m(K_ℓ)`) are
the direct limit of the functions on the quotients `G ⧸ K_ℓ(n)` (Harris's
`D_m(K_{ℓ,n})`), along the pullbacks `quotientFunctionsMap`. -/
def directLimitEquiv :
    Module.DirectLimit (fun n => G ⧸ T.lower n → M) (fun _ _ h => T.quotientFunctionsMap R h)
      ≃ₗ[R] LocallyConstant G M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift R ℕ _ _ (T.quotientFunctionsPullback R)
      (T.quotientFunctionsPullback_map R))
    (show Function.Bijective _ from
      ⟨Module.DirectLimit.lift_injective _ _ (T.quotientFunctionsPullback_injective R),
      fun f => by
        obtain ⟨n, hn⟩ := T.exists_mem_fixedVectors_rightRegular R f
        refine ⟨Module.DirectLimit.of R ℕ _ _ n (invariantsDescend (T.lower n) ⟨f, hn⟩), ?_⟩
        rw [Module.DirectLimit.lift_of]
        exact LocallyConstant.ext fun _ => rfl⟩)

/-- `directLimitEquiv` on the image of the functions on `G ⧸ K_ℓ(n)` is
`quotientFunctionsPullback`. -/
@[simp]
lemma directLimitEquiv_of (n : ℕ) (φ : G ⧸ T.lower n → M) :
    T.directLimitEquiv R
        (Module.DirectLimit.of R ℕ _ (fun _ _ h => T.quotientFunctionsMap R h) n φ) =
      T.quotientFunctionsPullback R n φ := by
  change Module.DirectLimit.lift R ℕ _ _ (T.quotientFunctionsPullback R)
    (T.quotientFunctionsPullback_map R) (Module.DirectLimit.of R ℕ _ _ n φ) = _
  exact Module.DirectLimit.lift_of _ _ _

end DirectLimit

end Langlands.CongruenceTower

namespace Langlands.Shimura.DefiniteForms

open Langlands.Global Langlands.Shimura.EquivariantForms

universe v t uR

variable {A : Type v} [Ring A] [Algebra ℚ A] (σ : AlgebraInvolution ℚ A) [Module.Finite ℚ A]
  (ℓ : FinitePlace ℚ) {K : Subgroup σ.FiniteAdelicPoints}

section Level

variable (K) in
/-- A chosen element `k_y ∈ K` with `ℓ`-component `y`, for each `y ∈ K_ℓ`. -/
def localLevelSection (y : localLevel σ ℓ K) : K :=
  Function.surjInv (localLevelMap_surjective σ ℓ K) y

@[simp]
lemma localLevelMap_localLevelSection (y : localLevel σ ℓ K) :
    localLevelMap σ ℓ K (localLevelSection σ ℓ K y) = y :=
  Function.surjInv_eq (localLevelMap_surjective σ ℓ K) y

variable (R : Type uR) [CommRing R] (M : Type t) [AddCommGroup M] [Module R M]

/-- Harris's `𝒜_ℓ(GJ, M, K(n))` for trivial coefficients `M` and a subgroup `H` of `K_ℓ`
(Harris's `K_ℓ(n)`): the forms of level `K(n) = congruenceLevel σ ℓ K H` on which
`levelAction` acts. -/
abbrev congruenceForms (H : Subgroup (localLevel σ ℓ K)) :
    Submodule R (σ.FiniteAdelicPoints → M) :=
  forms σ.finiteAdelicDiagonal (congruenceLevel σ ℓ K H)
    ((Representation.trivial R K M).comp (Subgroup.inclusion (congruenceLevel_le σ ℓ K H)))

variable {σ ℓ R M} in
/-- The forms of level `K(n)` with trivial coefficients are the functions invariant under
`GJ(ℚ)` on the left and under `K(n)` on the right. -/
lemma mem_congruenceForms {H : Subgroup (localLevel σ ℓ K)} {f : σ.FiniteAdelicPoints → M} :
    f ∈ congruenceForms σ ℓ R M H ↔
      (∀ (γ : σ.similitudes) (g : σ.FiniteAdelicPoints),
          f (σ.finiteAdelicDiagonal γ * g) = f g) ∧
        ∀ (g : σ.FiniteAdelicPoints), ∀ k ∈ congruenceLevel σ ℓ K H, f (g * k) = f g :=
  and_congr Iff.rfl ⟨fun h g k hk => h g ⟨k, hk⟩, fun h g k => h g k k.2⟩

variable {σ ℓ R M} in
/-- A form of level `K(n)` takes the same value at `g * k` and `g * k'` when
`k_ℓ⁻¹ * k'_ℓ ∈ K_ℓ(n)`. -/
lemma congruenceForms_apply_mul_eq {H : Subgroup (localLevel σ ℓ K)}
    {f : σ.FiniteAdelicPoints → M} (hf : f ∈ congruenceForms σ ℓ R M H)
    (g : σ.FiniteAdelicPoints) {k k' : K}
    (hk : (localLevelMap σ ℓ K k)⁻¹ * localLevelMap σ ℓ K k' ∈ H) :
    f (g * k') = f (g * k) := by
  have hm : k⁻¹ * k' ∈ (congruenceLevel σ ℓ K H).subgroupOf K := by
    rw [congruenceLevel_subgroupOf, Subgroup.mem_comap, map_mul, map_inv]
    exact hk
  have := (mem_congruenceForms.1 hf).2 (g * k) _ (Subgroup.mem_subgroupOf.1 hm)
  rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc g, mul_inv_cancel_left] at this

variable {σ ℓ R M} in
/-- Right translation by `k ∈ K` preserves the forms of level `K(n)` for normal `K_ℓ(n)`. -/
lemma translate_mem_congruenceForms {H : Subgroup (localLevel σ ℓ K)} [H.Normal]
    {f : σ.FiniteAdelicPoints → M} (hf : f ∈ congruenceForms σ ℓ R M H) (k : K) :
    (fun g => f (g * k)) ∈ congruenceForms σ ℓ R M H := by
  refine mem_congruenceForms.2 ⟨fun γ g => ?_, fun g j hj => ?_⟩
  · rw [mul_assoc]
    exact (mem_congruenceForms.1 hf).1 γ (g * k)
  · have hm : (k : σ.FiniteAdelicPoints)⁻¹ * j * k ∈ congruenceLevel σ ℓ K H := by
      have h1 : (⟨j, congruenceLevel_le σ ℓ K H hj⟩ : K) ∈
          (congruenceLevel σ ℓ K H).subgroupOf K := hj
      have h2 := (inferInstance : ((congruenceLevel σ ℓ K H).subgroupOf K).Normal).conj_mem _
        h1 k⁻¹
      simpa [Subgroup.mem_subgroupOf] using h2
    have e : g * j * k = g * k * ((k : σ.FiniteAdelicPoints)⁻¹ * j * k) := by group
    rw [e]
    exact (mem_congruenceForms.1 hf).2 (g * k) _ hm

/-- The forms of level `K(n)` grow as `K_ℓ(n)` shrinks. -/
lemma congruenceForms_anti {H H' : Subgroup (localLevel σ ℓ K)} (h : H' ≤ H) :
    congruenceForms σ ℓ R M H ≤ congruenceForms σ ℓ R M H' := fun _ hf =>
  mem_congruenceForms.2 ⟨(mem_congruenceForms.1 hf).1, fun g k hk =>
    (mem_congruenceForms.1 hf).2 g k (congruenceLevel_mono σ ℓ h hk)⟩

end Level

section Tower

variable (T : CongruenceTower (localLevel σ ℓ K)) (R : Type uR) [CommRing R] (M : Type t)
  [AddCommGroup M] [Module R M]

/-- The forms of level `K(n)` increase with `n`. -/
lemma monotone_congruenceForms : Monotone fun n => congruenceForms σ ℓ R M (T.lower n) :=
  fun _ _ h => congruenceForms_anti σ ℓ R M (T.antitone h)

/-- Harris's forms of level `K(n)` for all `n` at once: the union `⋃_n 𝒜_ℓ(GJ, M, K(n))`, the
direct limit of the forms of level `K(n)` along the inclusions. -/
def towerForms : Submodule R (σ.FiniteAdelicPoints → M) :=
  ⨆ n, congruenceForms σ ℓ R M (T.lower n)

variable {σ ℓ T R M} in
/-- A function lies in `towerForms` exactly when it is a form of level some `K(n)`. -/
lemma mem_towerForms {f : σ.FiniteAdelicPoints → M} :
    f ∈ towerForms σ ℓ T R M ↔ ∃ n, f ∈ congruenceForms σ ℓ R M (T.lower n) :=
  Submodule.mem_iSup_of_directed _ (monotone_congruenceForms σ ℓ T R M).directed_le

/-- The forms of level `K(n)` lie in `towerForms`. -/
lemma congruenceForms_le_towerForms (n : ℕ) :
    congruenceForms σ ℓ R M (T.lower n) ≤ towerForms σ ℓ T R M :=
  le_iSup (fun n => congruenceForms σ ℓ R M (T.lower n)) n

/-- The action of `K` on `⋃_n 𝒜_ℓ(GJ, M, K(n))` by right translation, `(k • f)(g) = f (g * k)`;
on each `𝒜_ℓ(GJ, M, K(n))` it is `levelAction`. -/
def towerAction : Representation R K (towerForms σ ℓ T R M) where
  toFun k := (LinearMap.funLeft R M (· * (k : σ.FiniteAdelicPoints))).restrict fun f hf => by
    obtain ⟨n, hn⟩ := mem_towerForms.1 hf
    exact mem_towerForms.2 ⟨n, translate_mem_congruenceForms hn k⟩
  map_one' := LinearMap.ext fun f => Subtype.ext <| funext fun g => by
    change f.1 (g * ((1 : K) : σ.FiniteAdelicPoints)) = f.1 g
    rw [OneMemClass.coe_one, mul_one]
  map_mul' k k' := LinearMap.ext fun f => Subtype.ext <| funext fun g => by
    change f.1 (g * ((k * k' : K) : σ.FiniteAdelicPoints)) = f.1 (g * k * k')
    rw [Subgroup.coe_mul, mul_assoc]

@[simp]
lemma towerAction_apply_coe (k : K) (f : towerForms σ ℓ T R M) (g : σ.FiniteAdelicPoints) :
    (towerAction σ ℓ T R M k f).1 g = f.1 (g * k) :=
  rfl

end Tower

section Functions

variable (R : Type uR) [CommRing R]

/-- The restriction to double cosets `f ↦ (y ↦ (x ↦ f (x.out * k_y)))`, where `k_y ∈ K` is a
chosen element with `ℓ`-component `y`. -/
def towerFunctionMap :
    (σ.FiniteAdelicPoints → R) →ₗ[R]
      (localLevel σ ℓ K → DoubleCosets σ.finiteAdelicDiagonal K → R) :=
  LinearMap.pi fun y => LinearMap.pi fun x => LinearMap.proj
    (x.out * (localLevelSection σ ℓ K y : σ.FiniteAdelicPoints))

variable {σ ℓ R} in
/-- On the forms of level `K(n)`, `towerFunctionMap` is Harris's (3.10)
(`congruenceFunctionEquiv`). -/
lemma towerFunctionMap_eq (h : LocalLevelFree σ ℓ K) {H : Subgroup (localLevel σ ℓ K)}
    [H.Normal] (hH : IsOpen (H : Set (localLevel σ ℓ K))) {f : σ.FiniteAdelicPoints → R}
    (hf : f ∈ congruenceForms σ ℓ R R H) :
    towerFunctionMap σ ℓ R f = ⇑(congruenceFunctionEquiv σ ℓ R H h hH ⟨f, hf⟩).1 := by
  funext y x
  have := congruenceFunctionEquiv_apply σ ℓ R H h hH ⟨f, hf⟩ (localLevelSection σ ℓ K y) x
  rw [localLevelMap_localLevelSection] at this
  exact this.symm

variable (T : CongruenceTower (localLevel σ ℓ K))

/-- `towerFunctionMap` on `⋃_n 𝒜_ℓ(GJ, R, K(n))`, with values in the locally constant
functions. -/
def towerFunctionLinearMap (h : LocalLevelFree σ ℓ K) :
    towerForms σ ℓ T R R →ₗ[R]
      LocallyConstant (localLevel σ ℓ K) (DoubleCosets σ.finiteAdelicDiagonal K → R) where
  toFun f := ⟨towerFunctionMap σ ℓ R f.1, by
    obtain ⟨n, hn⟩ := mem_towerForms.1 f.2
    rw [towerFunctionMap_eq h (T.isOpen_lower n) hn]
    exact LocallyConstant.isLocallyConstant _⟩
  map_add' f f' := LocallyConstant.ext fun y =>
    congrFun (map_add (towerFunctionMap σ ℓ R) f.1 f'.1) y
  map_smul' r f := LocallyConstant.ext fun y =>
    congrFun (map_smul (towerFunctionMap σ ℓ R) r f.1) y

variable {σ ℓ R T} in
/-- `towerFunctionLinearMap` is injective, since (3.10) is injective at each level. -/
lemma towerFunctionLinearMap_injective (h : LocalLevelFree σ ℓ K) :
    Function.Injective (towerFunctionLinearMap σ ℓ R T h) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
  obtain ⟨n, hn⟩ := mem_towerForms.1 f.2
  have h0 : congruenceFunctionEquiv σ ℓ R (T.lower n) h (T.isOpen_lower n) ⟨f.1, hn⟩ = 0 :=
    Subtype.ext (LocallyConstant.ext fun y => by
      rw [← congrFun (towerFunctionMap_eq h (T.isOpen_lower n) hn) y]
      exact DFunLike.congr_fun hf y)
  have h1 := (map_eq_zero_iff _ (EquivLike.injective _)).1 h0
  exact Subtype.ext (congrArg
    (fun x : congruenceForms σ ℓ R R (T.lower n) => (x : σ.FiniteAdelicPoints → R)) h1)

variable {σ ℓ R T} in
/-- For compact `K`, `towerFunctionLinearMap` is surjective: a locally constant function on the
compact `K_ℓ` is fixed by some `K_ℓ(n)`, hence comes from a form of level `K(n)` by (3.10). -/
lemma towerFunctionLinearMap_surjective (h : LocalLevelFree σ ℓ K)
    (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) :
    Function.Surjective (towerFunctionLinearMap σ ℓ R T h) := by
  intro φ
  have := compactSpace_localLevel σ ℓ K hK
  obtain ⟨n, hn⟩ := T.exists_mem_fixedVectors_rightRegular R φ
  obtain ⟨f, hf⟩ := (congruenceFunctionEquiv σ ℓ R (T.lower n) h
    (T.isOpen_lower n)).toLinearEquiv.surjective ⟨φ, hn⟩
  refine ⟨⟨f.1, congruenceForms_le_towerForms σ ℓ T R R n f.2⟩, LocallyConstant.ext fun y => ?_⟩
  change towerFunctionMap σ ℓ R f.1 y = φ y
  rw [towerFunctionMap_eq h (T.isOpen_lower n) f.2]
  exact DFunLike.congr_fun (congrArg Subtype.val hf) y

variable {σ ℓ R T} in
/-- `towerFunctionLinearMap` intertwines right translation by `k` with right translation by
`k_ℓ`. -/
lemma towerFunctionLinearMap_comm (h : LocalLevelFree σ ℓ K) (k : K)
    (f : towerForms σ ℓ T R R) :
    towerFunctionLinearMap σ ℓ R T h (towerAction σ ℓ T R R k f) =
      functionModuleRep σ ℓ K R (DoubleCosets σ.finiteAdelicDiagonal K → R)
        (localLevelMap σ ℓ K k) (towerFunctionLinearMap σ ℓ R T h f) :=
  LocallyConstant.ext fun y => funext fun x => by
    obtain ⟨n, hn⟩ := mem_towerForms.1 f.2
    change f.1 (x.out * ↑(localLevelSection σ ℓ K y) * ↑k) =
      f.1 (x.out * ↑(localLevelSection σ ℓ K (y * localLevelMap σ ℓ K k)))
    rw [mul_assoc, ← Subgroup.coe_mul]
    refine congruenceForms_apply_mul_eq hn _ ?_
    rw [map_mul, localLevelMap_localLevelSection, localLevelMap_localLevelSection,
      inv_mul_cancel]
    exact one_mem _

/-- Harris's (3.10) along the tower (1999, p.308), under (3.6), for compact `K`: restriction to
double cosets identifies `⋃_n 𝒜_ℓ(GJ, R, K(n))`, with `K` acting by right translation, with
`D(K_ℓ)` with values in the functions on the double cosets `GJ(ℚ)\GJ(𝔸^f)/K`, with `K` acting
through `k ↦ k_ℓ` by right translation. A form `f` goes to `k_ℓ ↦ (x ↦ f (x.out * k))`
(`towerFunctionEquiv_apply`). -/
def towerFunctionEquiv (h : LocalLevelFree σ ℓ K)
    (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) :
    Representation.Equiv (towerAction σ ℓ T R R)
      ((functionModuleRep σ ℓ K R (DoubleCosets σ.finiteAdelicDiagonal K → R)).comp
        (localLevelMap σ ℓ K)) :=
  .mk (LinearEquiv.ofBijective (towerFunctionLinearMap σ ℓ R T h)
      ⟨towerFunctionLinearMap_injective h, towerFunctionLinearMap_surjective h hK⟩)
    fun k => LinearMap.ext fun f => towerFunctionLinearMap_comm h k f

/-- `towerFunctionEquiv` sends a form `f` to `k_ℓ ↦ (x ↦ f (x.out * k))`. -/
lemma towerFunctionEquiv_apply (h : LocalLevelFree σ ℓ K)
    (hK : IsCompact (K : Set σ.FiniteAdelicPoints)) (f : towerForms σ ℓ T R R) (k : K)
    (x : DoubleCosets σ.finiteAdelicDiagonal K) :
    towerFunctionEquiv σ ℓ R T h hK f (localLevelMap σ ℓ K k) x =
      f.1 (x.out * (k : σ.FiniteAdelicPoints)) := by
  obtain ⟨n, hn⟩ := mem_towerForms.1 f.2
  change towerFunctionMap σ ℓ R f.1 (localLevelMap σ ℓ K k) x = _
  rw [towerFunctionMap_eq h (T.isOpen_lower n) hn]
  exact congruenceFunctionEquiv_apply σ ℓ R (T.lower n) h (T.isOpen_lower n) ⟨f.1, hn⟩ k x

end Functions

section Frobenius

variable (R : Type uR) [CommRing R] (M : Type t) [AddCommGroup M] [Module R M]

variable {σ ℓ R M} in
/-- The functional equation of `𝒜_ℓ(GJ, D(K_ℓ), K)`: `f (g * k) y = f g (y * k_ℓ⁻¹)`. -/
lemma functionModuleForms_apply_mul (f : functionModuleForms σ ℓ K R M)
    (g : σ.FiniteAdelicPoints) (k : K) (y : localLevel σ ℓ K) :
    f.1 (g * k) y = f.1 g (y * (localLevelMap σ ℓ K k)⁻¹) := by
  rw [f.2.2 g k]
  change f.1 g (y * localLevelMap σ ℓ K k⁻¹) = _
  rw [map_inv]

variable {σ ℓ R M} in
/-- A form with coefficients in `D(K_ℓ)` is determined by its values at `1`:
`f g y = f (g * k) 1` whenever `k_ℓ = y⁻¹`. -/
lemma functionModuleForms_apply_eq (f : functionModuleForms σ ℓ K R M)
    (g : σ.FiniteAdelicPoints) {k : K} {y : localLevel σ ℓ K}
    (hk : localLevelMap σ ℓ K k = y⁻¹) : f.1 g y = f.1 (g * k) 1 := by
  rw [functionModuleForms_apply_mul, hk, inv_inv, one_mul]

/-- Evaluation at `1`, `f ↦ (g ↦ f g 1)`, on the functions with values in `D(K_ℓ)`. -/
def evalOne :
    (σ.FiniteAdelicPoints → LocallyConstant (localLevel σ ℓ K) M) →ₗ[R]
      (σ.FiniteAdelicPoints → M) where
  toFun f g := f g 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (T : CongruenceTower (localLevel σ ℓ K))

variable {σ ℓ R M} in
/-- For compact `K` and finitely many double cosets `GJ(ℚ)\GJ(𝔸^f)/K` (Harris's (3.9)), all
values of a form with coefficients in `D(K_ℓ)` are fixed by one `K_ℓ(n)` under right
translation. -/
theorem exists_lower_functionModuleForms (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] (f : functionModuleForms σ ℓ K R M) :
    ∃ n, ∀ (g : σ.FiniteAdelicPoints) (y : localLevel σ ℓ K), ∀ h ∈ T.lower n,
      f.1 g (y * h) = f.1 g y := by
  have := compactSpace_localLevel σ ℓ K hK
  choose N hN using fun x : DoubleCosets σ.finiteAdelicDiagonal K =>
    T.exists_lower_apply_mul (f.1 x.out)
  obtain ⟨n, hn⟩ := Finite.exists_le N
  refine ⟨n, fun g y h hh => ?_⟩
  obtain ⟨γ, k, hg⟩ := exists_eq_mul_out_mul (ι := σ.finiteAdelicDiagonal) (K := K) g
  rw [hg, forms_apply_mul_mul f γ _ k]
  have hm : (localLevelMap σ ℓ K k⁻¹)⁻¹ * h * localLevelMap σ ℓ K k⁻¹ ∈
      T.lower (N (DoubleCoset.mk σ.finiteAdelicDiagonal.range K g)) :=
    T.antitone (hn _) (by
      simpa using (T.lower_normal n).conj_mem h hh (localLevelMap σ ℓ K k⁻¹)⁻¹)
  have e : y * h * localLevelMap σ ℓ K k⁻¹ = y * localLevelMap σ ℓ K k⁻¹ *
      ((localLevelMap σ ℓ K k⁻¹)⁻¹ * h * localLevelMap σ ℓ K k⁻¹) := by group
  change f.1 _ (y * h * localLevelMap σ ℓ K k⁻¹) = f.1 _ (y * localLevelMap σ ℓ K k⁻¹)
  rw [e]
  exact hN _ _ _ hm

variable {σ ℓ R M T} in
/-- If all values of `f` are fixed by `K_ℓ(n)`, then `g ↦ f g 1` is a form of level `K(n)`. -/
lemma evalOne_mem_congruenceForms {n : ℕ} (f : functionModuleForms σ ℓ K R M)
    (hn : ∀ (g : σ.FiniteAdelicPoints) (y : localLevel σ ℓ K), ∀ h ∈ T.lower n,
      f.1 g (y * h) = f.1 g y) :
    evalOne σ ℓ R M f.1 ∈ congruenceForms σ ℓ R M (T.lower n) := by
  refine mem_congruenceForms.2 ⟨fun γ g => ?_, fun g k hk => ?_⟩
  · exact congrArg (fun φ : LocallyConstant (localLevel σ ℓ K) M => φ 1) (f.2.1 γ g)
  · have hkK : k ∈ K := congruenceLevel_le σ ℓ K _ hk
    have hk' : localLevelMap σ ℓ K ⟨k, hkK⟩ ∈ T.lower n := by
      have : (⟨k, hkK⟩ : K) ∈ (congruenceLevel σ ℓ K (T.lower n)).subgroupOf K := hk
      rwa [congruenceLevel_subgroupOf] at this
    exact (functionModuleForms_apply_mul f g ⟨k, hkK⟩ 1).trans (hn g 1 _ (inv_mem hk'))

variable {σ ℓ R M T} in
/-- The form with coefficients in `D(K_ℓ)` attached to a form `F` of level `K(n)`:
`g ↦ (y ↦ F (g * k_y⁻¹))`. -/
def functionModuleFormsLift {n : ℕ} {F : σ.FiniteAdelicPoints → M}
    (hF : F ∈ congruenceForms σ ℓ R M (T.lower n)) : functionModuleForms σ ℓ K R M :=
  ⟨fun g => ⟨fun y => F (g * ((localLevelSection σ ℓ K y)⁻¹ : K)), by
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
      have hy : y ∈ (fun z => y⁻¹ * z) ⁻¹' (T.lower n : Set (localLevel σ ℓ K)) := by
        change y⁻¹ * y ∈ T.lower n
        rw [inv_mul_cancel]
        exact one_mem _
      refine Filter.eventually_of_mem (((T.isOpen_lower n).preimage
        (continuous_const_mul y⁻¹)).mem_nhds hy) fun y' hy' => ?_
      refine congruenceForms_apply_mul_eq hF g ?_
      rw [map_inv, map_inv, localLevelMap_localLevelSection, localLevelMap_localLevelSection,
        inv_inv]
      have e : y * y'⁻¹ = y * (y⁻¹ * y')⁻¹ * y⁻¹ := by group
      rw [e]
      exact (T.lower_normal n).conj_mem _ (inv_mem hy') y⟩,
    fun γ g => LocallyConstant.ext fun y => by
      change F (σ.finiteAdelicDiagonal γ * g * _) = F (g * _)
      rw [mul_assoc]
      exact (mem_congruenceForms.1 hF).1 γ _,
    fun g k => LocallyConstant.ext fun y => by
      change F (g * k * ((localLevelSection σ ℓ K y)⁻¹ : K)) =
        F (g * ((localLevelSection σ ℓ K (y * localLevelMap σ ℓ K k⁻¹))⁻¹ : K))
      rw [mul_assoc, ← Subgroup.coe_mul]
      refine congruenceForms_apply_mul_eq hF g ?_
      have e : (localLevelMap σ ℓ K (localLevelSection σ ℓ K (y * localLevelMap σ ℓ K k⁻¹))⁻¹)⁻¹ *
          localLevelMap σ ℓ K (k * (localLevelSection σ ℓ K y)⁻¹) = 1 := by
        simp only [map_inv, map_mul, inv_inv, localLevelMap_localLevelSection]
        group
      rw [e]
      exact one_mem _⟩

variable {σ ℓ R M T} in
/-- `functionModuleFormsLift` is a right inverse of evaluation at `1`. -/
lemma evalOne_functionModuleFormsLift {n : ℕ} {F : σ.FiniteAdelicPoints → M}
    (hF : F ∈ congruenceForms σ ℓ R M (T.lower n)) :
    evalOne σ ℓ R M (functionModuleFormsLift hF).1 = F := funext fun g => by
  change F (g * ((localLevelSection σ ℓ K 1)⁻¹ : K)) = F g
  have := congruenceForms_apply_mul_eq hF g (k := 1) (k' := (localLevelSection σ ℓ K 1)⁻¹)
    (by simp)
  rwa [OneMemClass.coe_one, mul_one] at this

variable {σ ℓ R M} in
/-- Evaluation at `1` as a linear map from `𝒜_ℓ(GJ, D(K_ℓ), K)` to `⋃_n 𝒜_ℓ(GJ, M, K(n))`. -/
def functionFormsMap (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] :
    functionModuleForms σ ℓ K R M →ₗ[R] towerForms σ ℓ T R M :=
  ((evalOne σ ℓ R M).comp (functionModuleForms σ ℓ K R M).subtype).codRestrict _ fun f => by
    obtain ⟨n, hn⟩ := exists_lower_functionModuleForms T hK f
    exact congruenceForms_le_towerForms σ ℓ T R M n (evalOne_mem_congruenceForms f hn)

variable {σ ℓ R M} in
/-- A form with coefficients in `D(K_ℓ)` vanishing at `1` everywhere is zero. -/
lemma functionFormsMap_injective (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] :
    Function.Injective (functionFormsMap (R := R) (M := M) T hK) := by
  refine (injective_iff_map_eq_zero _).2 fun f hf =>
    Subtype.ext (funext fun g => LocallyConstant.ext fun y => ?_)
  rw [functionModuleForms_apply_eq f g (localLevelMap_localLevelSection σ ℓ y⁻¹)]
  exact congrFun (congrArg Subtype.val hf) (g * localLevelSection σ ℓ K y⁻¹)

variable {σ ℓ R M} in
/-- Every form of level some `K(n)` is `g ↦ f g 1` for its `functionModuleFormsLift` `f`. -/
lemma functionFormsMap_surjective (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] :
    Function.Surjective (functionFormsMap (R := R) (M := M) T hK) := fun F => by
  obtain ⟨n, hn⟩ := mem_towerForms.1 F.2
  exact ⟨functionModuleFormsLift hn, Subtype.ext (evalOne_functionModuleFormsLift hn)⟩

/-- For compact `K` with finitely many double cosets `GJ(ℚ)\GJ(𝔸^f)/K` (Harris's (3.9)), the
forms `𝒜_ℓ(GJ, D(K_ℓ), K)` with coefficients in the locally constant functions `K_ℓ → M` are
the forms of level some `K(n)` with trivial coefficients `M`: `f ↦ (g ↦ f g 1)`
(`functionFormsEquiv_apply_coe`), with inverse `F ↦ (g ↦ (y ↦ F (g * k)))` for any `k ∈ K` with
`k_ℓ = y⁻¹` (`functionFormsEquiv_symm_apply`). Hypothesis (3.6) is not used. -/
def functionFormsEquiv (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] :
    functionModuleForms σ ℓ K R M ≃ₗ[R] towerForms σ ℓ T R M :=
  LinearEquiv.ofBijective (functionFormsMap T hK)
    ⟨functionFormsMap_injective T hK, functionFormsMap_surjective T hK⟩

/-- `functionFormsEquiv f` is `g ↦ f g 1`. -/
@[simp]
lemma functionFormsEquiv_apply_coe (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] (f : functionModuleForms σ ℓ K R M)
    (g : σ.FiniteAdelicPoints) :
    (functionFormsEquiv σ ℓ R M T hK f).1 g = f.1 g 1 :=
  rfl

/-- The inverse of `functionFormsEquiv` sends `F` to `g ↦ (y ↦ F (g * k))` for any `k ∈ K` with
`k_ℓ = y⁻¹`. -/
lemma functionFormsEquiv_symm_apply (hK : IsCompact (K : Set σ.FiniteAdelicPoints))
    [Finite (DoubleCosets σ.finiteAdelicDiagonal K)] (F : towerForms σ ℓ T R M)
    (g : σ.FiniteAdelicPoints) {k : K} {y : localLevel σ ℓ K}
    (hk : localLevelMap σ ℓ K k = y⁻¹) :
    ((functionFormsEquiv σ ℓ R M T hK).symm F).1 g y = F.1 (g * k) := by
  rw [functionModuleForms_apply_eq _ g hk]
  exact congrFun (congrArg Subtype.val ((functionFormsEquiv σ ℓ R M T hK).apply_symm_apply F))
    (g * k)

end Frobenius

end Langlands.Shimura.DefiniteForms
