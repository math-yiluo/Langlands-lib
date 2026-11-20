import Langlands.GroupScheme.Rational.RelativeRealCorootProof
import Langlands.GroupScheme.Rational.LanglandsSimpleRootBasis
import Langlands.GroupScheme.Rational.DominantWeylDisplacementRoots
import Langlands.GroupScheme.Rational.RootReflectionExistenceProof
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof
import Langlands.LinearAlgebra.ArthurCombinatorics
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-! # Arthur's parabolic combinatorics for an actual reductive group

Arthur 1978, §1 and §6; Arthur 2005, §5 and §8. For a connected reductive group `G` over a field
`k`, a maximal split torus `i : T → G` (Arthur's `A_0`) and a generic cocharacter `ν` (fixing the
minimal parabolic `P_0`), with integral reflection data `D`:

* `rootPairing hG hi D` is the reduced real root system of the indivisible relative roots, on
  `(𝔞_0^G)^* = relativeRootSpanReal i` and `𝔞_0^G = D.realCorootSpan`;
* `base hG hi hν D` is its Mathlib base whose simple roots are the simple relative roots `Δ_0`;
* `standardIndex hG hi ν J` is the subset of the base attached to the standard parabolic
  subgroup with `Δ_0^P = J`;
* `toCorootSpan hG hi D` is the projection `𝔞_0 → 𝔞_0^G` along `𝔞_G`, and `toRootSpan hG hi` the
  projection `𝔞_0^* → (𝔞_0^G)^*` along `𝔞_G^*`;
* `tau`, `tauHat`, `sigma`, `epsilon`, `phi`, `weight` and `levelProjection` are the functions of
  `Langlands.ArthurCombinatorics` pulled back to `𝔞_0 = V T` and `𝔞_0^* = Vstar T`; the theorems
  `tau_eq`, `tauHat_eq`, `weight_coroot`, `epsilon_eq`, `phi_eq` and
  `levelProjection_eq_projectionOnto` identify them with Arthur's definitions;
* `aSpace T J`, `corootSubspace D J` and `relativeSpace D J K` are `𝔞_P`, `𝔞_0^P` and `𝔞_P^Q`,
  with the decompositions `𝔞_0 = 𝔞_0^P ⊕ 𝔞_P` and `𝔞_P = 𝔞_P^Q ⊕ 𝔞_Q`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped Classical

namespace Langlands.GroupScheme.ArthurRelative

open RealTorusSpace RelativeRootSystem

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

section RootSystem

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include hG hi in
/-- The published relative root system of `i`. -/
theorem hasRelativeRootSystem : HasRelativeRootSystem i :=
  relativeRootSystem k G hG T i hi

include hG hi in
/-- The relative Weyl group is finite. -/
theorem finite_relativeWeylGroup : Finite (relativeWeylGroup i) :=
  (hasRelativeRootSystem hG hi).finite_relativeWeylGroup i

include hG hi in
/-- There are finitely many relative roots. -/
theorem finite_relativeRoots : (relativeRoots i).Finite :=
  (hasRelativeRootSystem hG hi).finite_relativeRoots i hi.isSplitSubtorus.1

omit [Mono i.hom.hom.left] in
include hG hi in
/-- `𝔞_0^* = (𝔞_0^G)^* ⊕ 𝔞_G^*`: the real root span and the restricted rational characters of
`G` are complementary. -/
theorem isCompl_relativeRootSpanReal :
    IsCompl (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range :=
  (relativeCharacterRootComplement k G hG T i hi).2

include hG hi in
/-- A `W`-invariant inner product on `𝔞_0^*` exists. -/
theorem exists_isWeylInvariantInnerProduct :
    ∃ B : LinearMap.BilinForm ℝ (Vstar T), IsWeylInvariantInnerProduct i B :=
  haveI := finite_relativeWeylGroup hG hi
  (exists_relativeWeyl_realInnerProducts (i := i) hi.isSplitSubtorus.1).1

variable (D : RelativeRootReflectionData i)

/-- Arthur's root system of `G`: the indivisible relative roots `Σ(A_0)` with their coroots, a
reduced crystallographic real root system on `(𝔞_0^G)^* = relativeRootSpanReal i` and
`𝔞_0^G = D.realCorootSpan`. It is the published `indivisibleRealRootPairing`. -/
def rootPairing :
    RootPairing (RelativeRoot.indivisibleRoots i) ℝ (relativeRootSpanReal i) D.realCorootSpan :=
  D.indivisibleRealRootPairing hi.isSplitSubtorus.1
    (finite_relativeRoots hG hi) (isCompl_relativeRootSpanReal hG hi)
    (exists_isWeylInvariantInnerProduct hG hi).choose
    (exists_isWeylInvariantInnerProduct hG hi).choose_spec (hasRelativeRootSystem hG hi)

@[simp] theorem rootPairing_root (α : RelativeRoot.indivisibleRoots i) :
    ((rootPairing hG hi D).root α : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] (α : characterLattice T) :=
  rfl

@[simp] theorem rootPairing_coroot (α : RelativeRoot.indivisibleRoots i) :
    ((rootPairing hG hi D).coroot α : V T) = D.realCoroot ⟨α.1, α.2.1⟩ :=
  rfl

@[simp] theorem rootPairing_toLinearMap (x : relativeRootSpanReal i) (y : D.realCorootSpan) :
    (rootPairing hG hi D).toLinearMap x y = pair T (x : Vstar T) (y : V T) :=
  rfl

include hG hi in
/-- There are finitely many indivisible relative roots. -/
theorem finite_indivisibleRoots : Finite (RelativeRoot.indivisibleRoots i) :=
  ((finite_relativeRoots hG hi).subset fun _ h => h.1).to_subtype

instance rootPairing_isRootSystem : (rootPairing hG hi D).IsRootSystem :=
  D.indivisibleRealRootPairing_isRootSystem _ _ _ _ _ _

instance rootPairing_isCrystallographic : (rootPairing hG hi D).IsCrystallographic :=
  D.indivisibleRealRootPairing_isCrystallographic _ _ _ _ _ _

instance rootPairing_isReduced : (rootPairing hG hi D).IsReduced :=
  haveI := finite_indivisibleRoots hG hi
  RootPairing.isReduced_of_no_double (rootPairing hG hi D)
    (RelativeRootSystem.indivisibleRealRoot_ne_two_smul hi.isSplitSubtorus.1)

end RootSystem

section Base

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include hG hi in
/-- The simple relative roots are indivisible. -/
theorem simpleRelativeRoots_subset_indivisibleRoots (ν : cocharacterLattice T) :
    simpleRelativeRoots i ν ⊆ RelativeRoot.indivisibleRoots i := by
  intro α hα
  refine ⟨hα.1.1, ?_⟩
  intro b hb m hm hmb
  rcases (hasRelativeRootSystem hG hi).eq_one_or_two_of_nsmul_mem hb (hmb ▸ hα.1.1) with h | h
  · omega
  · subst h
    have hpos : 0 < latticePairing T α ν := hα.1.2
    rw [← hmb, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hpos
    have hb' : b ∈ positiveRelativeRoots i ν := ⟨hb, by push_cast at hpos; omega⟩
    exact hα.2 ⟨b, hb', b, hb', by rw [← hmb, two_smul]⟩

/-- Arthur's `Δ_0`: the simple relative roots, as indices of `rootPairing`. -/
def simpleIndex (ν : cocharacterLattice T) : Set (RelativeRoot.indivisibleRoots i) :=
  {α | (α : characterLattice T) ∈ simpleRelativeRoots i ν}

variable {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
  (D : RelativeRootReflectionData i)

include hν in
/-- The roots of `Δ_0` are linearly independent. -/
theorem linearIndepOn_simpleIndex :
    LinearIndepOn ℝ (rootPairing hG hi D).root (simpleIndex ν) := by
  have h := D.linearIndependent_realSimpleRoots i ν hi.isSplitSubtorus.1
    (finite_relativeRoots hG hi) hν
  let e : simpleIndex (i := i) ν ≃ simpleRelativeRoots i ν :=
    { toFun := fun α => ⟨α.1.1, α.2⟩
      invFun := fun α => ⟨⟨α.1, simpleRelativeRoots_subset_indivisibleRoots hG hi ν α.2⟩, α.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact LinearIndependent.of_comp (relativeRootSpanReal i).subtype (h.comp e e.injective)

include hν in
/-- Every indivisible root is a nonnegative or a nonpositive integral combination of `Δ_0`. -/
theorem root_mem_closure_simpleIndex (α : RelativeRoot.indivisibleRoots i) :
    (rootPairing hG hi D).root α ∈
        AddSubmonoid.closure ((rootPairing hG hi D).root '' simpleIndex ν) ∨
      -(rootPairing hG hi D).root α ∈
        AddSubmonoid.closure ((rootPairing hG hi D).root '' simpleIndex ν) := by
  let φ : characterLattice T →+ Vstar T :=
    (TensorProduct.mk ℤ ℝ (characterLattice T) 1).toAddMonoidHom
  let ι : relativeRootSpanReal i →+ Vstar T := (relativeRootSpanReal i).subtype.toAddMonoidHom
  have himage : ι '' ((rootPairing hG hi D).root '' simpleIndex ν) =
      φ '' simpleRelativeRoots i ν := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a.1, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, ⟨⟨a, simpleRelativeRoots_subset_indivisibleRoots hG hi ν ha⟩, ha, rfl⟩, rfl⟩
  have key : ∀ (χ : characterLattice T) (y : relativeRootSpanReal i),
      χ ∈ positiveRelativeRoots i ν → (y : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] χ →
        y ∈ AddSubmonoid.closure ((rootPairing hG hi D).root '' simpleIndex ν) := by
    intro χ y hχ hy
    have h1 : φ χ ∈ (AddSubmonoid.closure (simpleRelativeRoots i ν)).map φ :=
      AddSubmonoid.mem_map_of_mem φ (DominantDisplacement.positive_mem_closure hχ)
    rw [AddMonoidHom.map_mclosure, ← himage, ← AddMonoidHom.map_mclosure] at h1
    obtain ⟨z, hz, hzy⟩ := AddSubmonoid.mem_map.mp h1
    have : z = y := Subtype.ext (hzy.trans hy.symm)
    exact this ▸ hz
  have hne := hν α.1 α.2.1
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    refine key (-α.1) _ ⟨D.neg_mem_relativeRoots i α.2.1, ?_⟩ ?_
    · rw [map_neg, LinearMap.neg_apply]
      omega
    · simp [TensorProduct.tmul_neg]
  · left
    exact key α.1 _ ⟨α.2.1, hpos⟩ rfl

/-- **Arthur's base.** The Mathlib base of `rootPairing hG hi D` whose simple roots are the
simple relative roots `Δ_0` for `ν`. -/
def base : (rootPairing hG hi D).Base :=
  haveI := finite_indivisibleRoots hG hi
  RootPairing.Base.mk' (rootPairing hG hi D) (simpleIndex ν)
    (linearIndepOn_simpleIndex hG hi hν D) (root_mem_closure_simpleIndex hG hi hν D)

@[simp] theorem mem_support_base {α : RelativeRoot.indivisibleRoots i} :
    α ∈ (base hG hi hν D).support ↔ (α : characterLattice T) ∈ simpleRelativeRoots i ν := by
  simp [base, RootPairing.Base.mk', simpleIndex]

end Base

section Projections

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)

/-- The subset `Θ = Δ_0^P` of indices recording the standard parabolic subgroup `P` whose Levi
component has simple roots `J ∩ Δ_0`. -/
def standardIndex (J : Set (characterLattice T)) : Finset (RelativeRoot.indivisibleRoots i) :=
  haveI := finite_indivisibleRoots hG hi
  (Set.toFinite {α : RelativeRoot.indivisibleRoots i |
    (α : characterLattice T) ∈ simpleRelativeRoots i ν ∧ (α : characterLattice T) ∈ J}).toFinset

@[simp] theorem mem_standardIndex {J : Set (characterLattice T)}
    {α : RelativeRoot.indivisibleRoots i} :
    α ∈ standardIndex hG hi ν J ↔
      (α : characterLattice T) ∈ simpleRelativeRoots i ν ∧ (α : characterLattice T) ∈ J := by
  simp [standardIndex]

theorem standardIndex_mono {J K : Set (characterLattice T)} (h : J ⊆ K) :
    standardIndex hG hi ν J ⊆ standardIndex hG hi ν K := by
  intro α hα
  rw [mem_standardIndex] at hα ⊢
  exact ⟨hα.1, h hα.2⟩

variable {ν} in
theorem standardIndex_subset_support (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) :
    standardIndex hG hi ν J ⊆ (base hG hi hν D).support := by
  intro α hα
  rw [mem_standardIndex] at hα
  rw [mem_support_base]
  exact hα.1

variable {ν} in
theorem standardIndex_simpleRelativeRoots (hν : IsGenericCocharacter i ν) :
    standardIndex hG hi ν (simpleRelativeRoots i ν) = (base hG hi hν D).support := by
  ext α
  rw [mem_standardIndex, mem_support_base, and_self]

/-- Every subset of `Δ_0` comes from a set of simple roots. -/
theorem standardIndex_image (Θ : Finset (RelativeRoot.indivisibleRoots i))
    (hΘ : ∀ α ∈ Θ, (α : characterLattice T) ∈ simpleRelativeRoots i ν) :
    standardIndex hG hi ν ((↑) '' (Θ : Set (RelativeRoot.indivisibleRoots i))) = Θ := by
  ext α
  rw [mem_standardIndex]
  constructor
  · rintro ⟨_, β, hβ, hβα⟩
    exact (Subtype.ext hβα : β = α) ▸ hβ
  · intro hα
    exact ⟨hΘ α hα, α, hα, rfl⟩

/-- Distinct sets of simple roots give distinct index sets. -/
theorem standardIndex_injOn :
    Set.InjOn (standardIndex hG hi ν) {J | J ⊆ simpleRelativeRoots i ν} := by
  intro J hJ K hK h
  ext χ
  constructor
  · intro hχ
    have hα : (⟨χ, simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hJ hχ)⟩ :
        RelativeRoot.indivisibleRoots i) ∈ standardIndex hG hi ν J :=
      (mem_standardIndex hG hi ν).mpr ⟨hJ hχ, hχ⟩
    rw [h, mem_standardIndex] at hα
    exact hα.2
  · intro hχ
    have hα : (⟨χ, simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hK hχ)⟩ :
        RelativeRoot.indivisibleRoots i) ∈ standardIndex hG hi ν K :=
      (mem_standardIndex hG hi ν).mpr ⟨hK hχ, hχ⟩
    rw [← h, mem_standardIndex] at hα
    exact hα.2

include hG hi in
/-- `𝔞_0 = 𝔞_G ⊕ 𝔞_0^G`: the common root annihilator and the real coroot span are
complementary. -/
theorem isCompl_relativeCentralDirections :
    IsCompl (relativeCentralDirections i) D.realCorootSpan :=
  D.central_isCompl_realCorootSpan hi.isSplitSubtorus.1 (isCompl_relativeRootSpanReal hG hi)
    (exists_isWeylInvariantInnerProduct hG hi).choose
    (exists_isWeylInvariantInnerProduct hG hi).choose_spec

/-- The projection `𝔞_0 → 𝔞_0^G` along `𝔞_G`. -/
def toCorootSpan : V T →ₗ[ℝ] D.realCorootSpan :=
  Submodule.projectionOnto D.realCorootSpan (relativeCentralDirections i)
    (isCompl_relativeCentralDirections hG hi D).symm

theorem toCorootSpan_apply_coe (y : D.realCorootSpan) : toCorootSpan hG hi D y = y :=
  Submodule.projectionOnto_apply_left _ y

theorem toCorootSpan_apply_eq_zero_iff {H : V T} :
    toCorootSpan hG hi D H = 0 ↔ H ∈ relativeCentralDirections i :=
  Submodule.projectionOnto_apply_eq_zero_iff _

theorem sub_toCorootSpan_mem (H : V T) :
    H - (toCorootSpan hG hi D H : V T) ∈ relativeCentralDirections i := by
  rw [← toCorootSpan_apply_eq_zero_iff hG hi D, map_sub, toCorootSpan_apply_coe, sub_self]

omit [Mono i.hom.hom.left] in
/-- The projection `𝔞_0^* → (𝔞_0^G)^*` along `𝔞_G^*`, the restricted rational characters of
`G`. -/
def toRootSpan : Vstar T →ₗ[ℝ] relativeRootSpanReal i :=
  Submodule.projectionOnto (relativeRootSpanReal i) (rationalCharacterRestrictReal i).range
    (isCompl_relativeRootSpanReal hG hi)

omit [Mono i.hom.hom.left] in
theorem toRootSpan_apply_coe (x : relativeRootSpanReal i) : toRootSpan hG hi x = x :=
  Submodule.projectionOnto_apply_left _ x

omit [Mono i.hom.hom.left] in
theorem sub_toRootSpan_mem (Λ : Vstar T) :
    Λ - (toRootSpan hG hi Λ : Vstar T) ∈ (rationalCharacterRestrictReal i).range := by
  rw [← Submodule.projectionOnto_apply_eq_zero_iff (isCompl_relativeRootSpanReal hG hi)]
  change toRootSpan hG hi (Λ - (toRootSpan hG hi Λ : Vstar T)) = 0
  rw [map_sub, toRootSpan_apply_coe, sub_self]

/-- On `𝔞_0^G`, a vector of `𝔞_0^*` pairs as its projection to `(𝔞_0^G)^*`: the restricted
rational characters of `G` vanish on the coroots. -/
theorem pair_toRootSpan (Λ : Vstar T) {y : V T} (hy : y ∈ D.realCorootSpan) :
    pair T (toRootSpan hG hi Λ : Vstar T) y = pair T Λ y := by
  have hy' := D.realCorootSpan_le_annihilator (exists_isWeylInvariantInnerProduct hG hi).choose
    (exists_isWeylInvariantInnerProduct hG hi).choose_spec hy
  rw [mem_cocharacterAnnihilator] at hy'
  have h := hy' _ (sub_toRootSpan_mem hG hi Λ)
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h
  exact h.symm

end Projections

section Functions

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (ν : cocharacterLattice T) (D : RelativeRootReflectionData i)

/-- Arthur's weight `ϖ_β` on `𝔞_0`, for the standard parabolic subgroup `P` with `Δ_0^P = J` and
`β ∈ J`: the abstract `weightCoordinate`, evaluated through `𝔞_0 → 𝔞_0^G`. It is the
coefficient of `β^∨` in the `𝔞_0^P`-component of a vector (`weight_coroot`,
`weight_eq_zero_of_mem_rootAnnihilator`). It is `0` if `β` is not an indivisible root. -/
def weight (J : Set (characterLattice T)) (β : characterLattice T) : V T →ₗ[ℝ] ℝ :=
  if h : β ∈ RelativeRoot.indivisibleRoots i then
    ArthurCombinatorics.weightCoordinate (rootPairing hG hi D) (standardIndex hG hi ν J) ⟨β, h⟩ ∘ₗ
      toCorootSpan hG hi D
  else 0

theorem weight_of_mem (J : Set (characterLattice T)) {β : characterLattice T}
    (h : β ∈ RelativeRoot.indivisibleRoots i) :
    weight hG hi ν D J β =
      ArthurCombinatorics.weightCoordinate (rootPairing hG hi D) (standardIndex hG hi ν J)
        ⟨β, h⟩ ∘ₗ toCorootSpan hG hi D := by
  simp only [weight, h, ↓reduceDIte]

/-- The projection `H ↦ H_P` of `𝔞_0 = 𝔞_0^P ⊕ 𝔞_P` onto `𝔞_P`, for the standard parabolic
subgroup `P` with `Δ_0^P = J`: `H_P = H - ∑_{β ∈ Δ_0^P} ϖ_β(H) β^∨`
(`levelProjection_mem_rootAnnihilator`, `sub_levelProjection_mem_span`). -/
def levelProjection (J : Set (characterLattice T)) : V T →ₗ[ℝ] V T :=
  LinearMap.id - ∑ j : standardIndex hG hi ν J,
    (ArthurCombinatorics.weightCoordinate (rootPairing hG hi D) (standardIndex hG hi ν J) j ∘ₗ
      toCorootSpan hG hi D).smulRight (D.realCoroot ⟨j.1.1, j.1.2.1⟩)

/-- Arthur's `τ_{P_1}^{P_2}(H)` for `H ∈ 𝔞_0`, with `Δ_0^{P_1} = J₁` and `Δ_0^{P_2} = J₂`
(`tau_eq`). -/
def tau (J₁ J₂ : Set (characterLattice T)) (H : V T) : ℤ :=
  ArthurCombinatorics.tau (rootPairing hG hi D) (standardIndex hG hi ν J₁)
    (standardIndex hG hi ν J₂) (toCorootSpan hG hi D H)

/-- Arthur's `τ̂_{P_1}^{P_2}(H)` for `H ∈ 𝔞_0` (`tauHat_eq`). With `J₂ = Δ_0` it is
`τ̂_{P_1} = τ̂_{P_1}^G`. -/
def tauHat (J₁ J₂ : Set (characterLattice T)) (H : V T) : ℤ :=
  ArthurCombinatorics.tauHat (rootPairing hG hi D) (standardIndex hG hi ν J₁)
    (standardIndex hG hi ν J₂) (toCorootSpan hG hi D H)

/-- Arthur's `σ_{P_1}^{P_2}(H) = ∑_{P_3 ⊇ P_2} (−1)^{dim(A_2/A_3)} τ_{P_1}^{P_3}(H) τ̂_{P_3}(H)`
for `H ∈ 𝔞_0`. -/
def sigma (J₁ J₂ : Set (characterLattice T)) (H : V T) : ℤ :=
  ArthurCombinatorics.sigma (rootPairing hG hi D)
    (standardIndex hG hi ν (simpleRelativeRoots i ν)) (standardIndex hG hi ν J₁)
    (standardIndex hG hi ν J₂) (toCorootSpan hG hi D H)

/-- Langlands' sign `ε_Q^P(Λ)` for `Λ ∈ 𝔞_0^*` (`epsilon_eq`). -/
def epsilon (JQ JP : Set (characterLattice T)) (Λ : Vstar T) : ℤ :=
  ArthurCombinatorics.epsilon (rootPairing hG hi D) (standardIndex hG hi ν JQ)
    (standardIndex hG hi ν JP) (toRootSpan hG hi Λ)

/-- Langlands' function `φ_Q^P(Λ, H)` for `Λ ∈ 𝔞_0^*` and `H ∈ 𝔞_0` (`phi_eq`). -/
def phi (JQ JP : Set (characterLattice T)) (Λ : Vstar T) (H : V T) : ℤ :=
  ArthurCombinatorics.phi (rootPairing hG hi D) (standardIndex hG hi ν JQ)
    (standardIndex hG hi ν JP) (toRootSpan hG hi Λ) (toCorootSpan hG hi D H)

/-- `H_P` is the central part of `H` plus the abstract level projection of its `𝔞_0^G` part. -/
theorem levelProjection_eq (J : Set (characterLattice T)) (H : V T) :
    levelProjection hG hi ν D J H = (H - (toCorootSpan hG hi D H : V T)) +
      (ArthurCombinatorics.levelProjection (rootPairing hG hi D) (standardIndex hG hi ν J)
        (toCorootSpan hG hi D H) : V T) := by
  simp only [levelProjection, ArthurCombinatorics.levelProjection, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul,
    rootPairing_coroot]
  abel

/-- A relative root vanishes on `H - H^G`. -/
theorem eval_sub_toCorootSpan {β : characterLattice T} (hβ : β ∈ relativeRoots i) (H : V T) :
    eval T β (H - (toCorootSpan hG hi D H : V T)) = 0 :=
  (mem_relativeCentralDirections i _).mp (sub_toCorootSpan_mem hG hi D H) β hβ

/-- A relative root evaluated on `H_P` is the abstract root evaluated on the abstract level
projection. -/
theorem eval_levelProjection (J : Set (characterLattice T)) (β : RelativeRoot.indivisibleRoots i)
    (H : V T) :
    eval T β (levelProjection hG hi ν D J H) =
      (rootPairing hG hi D).root' β
        (ArthurCombinatorics.levelProjection (rootPairing hG hi D) (standardIndex hG hi ν J)
          (toCorootSpan hG hi D H)) := by
  rw [levelProjection_eq, map_add, eval_sub_toCorootSpan hG hi D β.2.1, zero_add, eval_eq_pair]
  rfl

variable {ν}

/-- `H_P ∈ 𝔞_P`: the roots of `J = Δ_0^P` vanish on the level projection. -/
theorem levelProjection_mem_rootAnnihilator (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν) (H : V T) :
    levelProjection hG hi ν D J H ∈ rootAnnihilator T J := by
  have := finite_indivisibleRoots hG hi
  rw [mem_rootAnnihilator]
  intro β hβ
  have hβi := simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hJ hβ)
  have hmem := ArthurCombinatorics.levelProjection_mem_rootAnnihilator (base hG hi hν D)
    (standardIndex_subset_support hG hi D hν J) (toCorootSpan hG hi D H)
  have hk : (⟨β, hβi⟩ : RelativeRoot.indivisibleRoots i) ∈ standardIndex hG hi ν J :=
    (mem_standardIndex hG hi ν).mpr ⟨hJ hβ, hβ⟩
  have h0 := (Submodule.mem_iInf _).mp hmem ⟨β, hβi⟩
  have h1 := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp h0 hk)
  rw [eval_levelProjection hG hi ν D J ⟨β, hβi⟩ H]
  exact h1

/-- `H - H_P ∈ 𝔞_0^P`, the span of the coroots of `J = Δ_0^P`. -/
theorem sub_levelProjection_mem_span (J : Set (characterLattice T)) (H : V T) :
    H - levelProjection hG hi ν D J H ∈ Submodule.span ℝ (D.realCorootsOf J) := by
  simp only [levelProjection, LinearMap.sub_apply, LinearMap.id_apply, sub_sub_cancel,
    LinearMap.sum_apply, LinearMap.smulRight_apply]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨⟨j.1.1, j.1.2.1⟩, ((mem_standardIndex hG hi ν).mp j.2).2, rfl⟩

variable (ν)

/-- The weight of an indexed root is the abstract `weightCoordinate` on `𝔞_0^G`. -/
theorem weight_coe (J : Set (characterLattice T)) (α : RelativeRoot.indivisibleRoots i)
    (H : V T) :
    weight hG hi ν D J α H =
      ArthurCombinatorics.weightCoordinate (rootPairing hG hi D) (standardIndex hG hi ν J) α
        (toCorootSpan hG hi D H) := by
  rw [weight_of_mem hG hi ν D J α.2]
  rfl

/-- The weights vanish on `𝔞_P = rootAnnihilator T J`. -/
theorem weight_eq_zero_of_mem_rootAnnihilator (J : Set (characterLattice T))
    (β : characterLattice T) {v : V T} (hv : v ∈ rootAnnihilator T J) :
    weight hG hi ν D J β v = 0 := by
  by_cases hβ : β ∈ RelativeRoot.indivisibleRoots i
  · rw [weight_of_mem hG hi ν D J hβ, LinearMap.comp_apply]
    apply ArthurCombinatorics.weightCoordinate_eq_zero_of_mem_rootAnnihilator
    simp only [ArthurCombinatorics.rootAnnihilator, Submodule.mem_iInf, LinearMap.mem_ker]
    intro α hα
    have hαJ := ((mem_standardIndex hG hi ν).mp hα).2
    have h1 : eval T α.1 v = 0 := (mem_rootAnnihilator _ _).mp hv α.1 hαJ
    have h2 := eval_sub_toCorootSpan hG hi D α.2.1 v
    rw [map_sub, h1, zero_sub, neg_eq_zero, eval_eq_pair] at h2
    exact h2
  · simp [weight, hβ]

variable {ν}

/-- `ϖ_β(α^∨) = δ_{βα}` for `α, β ∈ J = Δ_0^P`: the weights are dual to the coroots of `J`. -/
theorem weight_coroot (hν : IsGenericCocharacter i ν) {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {β : characterLattice T} (hβ : β ∈ J)
    (α : relativeRoots i) (hα : (α : characterLattice T) ∈ J) :
    weight hG hi ν D J β (D.realCoroot α) = if β = α then 1 else 0 := by
  have := finite_indivisibleRoots hG hi
  have hβi := simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hJ hβ)
  have hαi := simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hJ hα)
  have hproj : toCorootSpan hG hi D (D.realCoroot α) =
      (rootPairing hG hi D).coroot ⟨α.1, hαi⟩ :=
    toCorootSpan_apply_coe hG hi D ((rootPairing hG hi D).coroot ⟨α.1, hαi⟩)
  rw [weight_of_mem hG hi ν D J hβi, LinearMap.comp_apply, hproj,
    ArthurCombinatorics.weightCoordinate_coroot (base hG hi hν D)
      (standardIndex_subset_support hG hi D hν J) ((mem_standardIndex hG hi ν).mpr ⟨hJ hβ, hβ⟩)
      ((mem_standardIndex hG hi ν).mpr ⟨hJ hα, hα⟩)]
  by_cases h : β = α.1
  · simp [h]
  · simp [h]

/-- On `𝔞_0^P` (`Δ_0^P = J ⊆ K = Δ_0^Q`) the weights of `Q` and of `P` attached to `β ∈ J`
agree. With `K = Δ_0` this identifies the weight of `P` on `𝔞_0^P` with the restriction of the
weight `ϖ_β ∈ Δ̂_0` of `G`, as in Arthur 2005, §5, p.26. -/
theorem weight_eq_of_mem_corootSubspace (hν : IsGenericCocharacter i ν)
    {J K : Set (characterLattice T)} (hJK : J ⊆ K) (hK : K ⊆ simpleRelativeRoots i ν)
    {β : characterLattice T} (hβ : β ∈ J) {v : V T}
    (hv : v ∈ Submodule.span ℝ (D.realCorootsOf J)) :
    weight hG hi ν D J β v = weight hG hi ν D K β v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    rw [weight_coroot hG hi D hν (hJK.trans hK) hβ α hα,
      weight_coroot hG hi D hν hK (hJK hβ) α (hJK hα)]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, map_smul, hx]

/-- **Arthur's `τ`.** For `Δ_0^{P_2} = J₂ ⊆ Δ_0`, `τ_{P_1}^{P_2}(H) = 1` exactly when
`β(H_{P_1}) > 0` for every `β ∈ Δ_0^{P_2} ∖ Δ_0^{P_1}`, that is, when every root of
`Δ_{P_1}^{P_2}` is positive on the projection of `H` to `𝔞_{P_1}`. -/
theorem tau_eq (J₁ : Set (characterLattice T)) {J₂ : Set (characterLattice T)}
    (hJ₂ : J₂ ⊆ simpleRelativeRoots i ν) (H : V T) :
    tau hG hi ν D J₁ J₂ H =
      if ∀ β ∈ J₂ \ J₁, 0 < eval T β (levelProjection hG hi ν D J₁ H) then 1 else 0 := by
  have hiff : (∀ α ∈ standardIndex hG hi ν J₂ \ standardIndex hG hi ν J₁,
      0 < (rootPairing hG hi D).root' α (ArthurCombinatorics.levelProjection (rootPairing hG hi D)
        (standardIndex hG hi ν J₁) (toCorootSpan hG hi D H))) ↔
      ∀ β ∈ J₂ \ J₁, 0 < eval T β (levelProjection hG hi ν D J₁ H) := by
    constructor
    · intro h β hβ
      have hβi := simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hJ₂ hβ.1)
      have hmem : (⟨β, hβi⟩ : RelativeRoot.indivisibleRoots i) ∈
          standardIndex hG hi ν J₂ \ standardIndex hG hi ν J₁ := by
        rw [Finset.mem_sdiff, mem_standardIndex, mem_standardIndex]
        exact ⟨⟨hJ₂ hβ.1, hβ.1⟩, fun h' => hβ.2 h'.2⟩
      rw [eval_levelProjection hG hi ν D J₁ ⟨β, hβi⟩ H]
      exact h _ hmem
    · intro h α hα
      rw [Finset.mem_sdiff, mem_standardIndex, mem_standardIndex] at hα
      have h' := h α.1 ⟨hα.1.2, fun h'' => hα.2 ⟨hα.1.1, h''⟩⟩
      rw [eval_levelProjection hG hi ν D J₁ α H] at h'
      exact h'
  unfold tau ArthurCombinatorics.tau
  by_cases hc : ∀ β ∈ J₂ \ J₁, 0 < eval T β (levelProjection hG hi ν D J₁ H)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hc)), ite_eq_left_of_eq_true _ _ (eq_true hc)]
  · simp only [mt hiff.mp hc, hc, ↓reduceIte]

/-- **Arthur's `τ̂`.** For `Δ_0^{P_2} = J₂ ⊆ Δ_0`, `τ̂_{P_1}^{P_2}(H) = 1` exactly when
`ϖ_β(H) > 0` for every `β ∈ Δ_0^{P_2} ∖ Δ_0^{P_1}`, with `ϖ_β = weight … J₂ β` the weight of
`Δ̂_{P_1}^{P_2}` attached to `β`. -/
theorem tauHat_eq (J₁ : Set (characterLattice T)) {J₂ : Set (characterLattice T)}
    (hJ₂ : J₂ ⊆ simpleRelativeRoots i ν) (H : V T) :
    tauHat hG hi ν D J₁ J₂ H =
      if ∀ β ∈ J₂ \ J₁, 0 < weight hG hi ν D J₂ β H then 1 else 0 := by
  have hiff : (∀ α ∈ standardIndex hG hi ν J₂ \ standardIndex hG hi ν J₁,
      0 < ArthurCombinatorics.weightCoordinate (rootPairing hG hi D) (standardIndex hG hi ν J₂) α
        (toCorootSpan hG hi D H)) ↔
      ∀ β ∈ J₂ \ J₁, 0 < weight hG hi ν D J₂ β H := by
    constructor
    · intro h β hβ
      have hβi := simpleRelativeRoots_subset_indivisibleRoots hG hi ν (hJ₂ hβ.1)
      have hmem : (⟨β, hβi⟩ : RelativeRoot.indivisibleRoots i) ∈
          standardIndex hG hi ν J₂ \ standardIndex hG hi ν J₁ := by
        rw [Finset.mem_sdiff, mem_standardIndex, mem_standardIndex]
        exact ⟨⟨hJ₂ hβ.1, hβ.1⟩, fun h' => hβ.2 h'.2⟩
      rw [weight_of_mem hG hi ν D J₂ hβi]
      exact h _ hmem
    · intro h α hα
      rw [Finset.mem_sdiff, mem_standardIndex, mem_standardIndex] at hα
      have h' := h α.1 ⟨hα.1.2, fun h'' => hα.2 ⟨hα.1.1, h''⟩⟩
      rw [weight_coe] at h'
      exact h'
  unfold tauHat ArthurCombinatorics.tauHat
  by_cases hc : ∀ β ∈ J₂ \ J₁, 0 < weight hG hi ν D J₂ β H
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr hc)), ite_eq_left_of_eq_true _ _ (eq_true hc)]
  · simp only [mt hiff.mp hc, hc, ↓reduceIte]

variable (ν)

/-- **Arthur's `Λ(α^∨)`.** For `Λ ∈ 𝔞_0^*`, the abstract coroot value attached to `β` and
`Q` (with `Δ_0^Q = JQ`) is `Λ(α^∨)`, where `α^∨ = (β^∨)_Q` is the projection to `𝔞_Q` of the
coroot `β^∨`. -/
theorem corootValue_eq (JQ : Set (characterLattice T)) (Λ : Vstar T)
    (α : RelativeRoot.indivisibleRoots i) :
    ArthurCombinatorics.corootValue (rootPairing hG hi D) (standardIndex hG hi ν JQ)
        (toRootSpan hG hi Λ) α =
      pair T Λ (levelProjection hG hi ν D JQ (D.realCoroot ⟨α.1, α.2.1⟩)) := by
  have hproj : toCorootSpan hG hi D (D.realCoroot ⟨α.1, α.2.1⟩) = (rootPairing hG hi D).coroot α :=
    toCorootSpan_apply_coe hG hi D ((rootPairing hG hi D).coroot α)
  rw [levelProjection_eq, hproj]
  have h0 : D.realCoroot ⟨α.1, α.2.1⟩ - ((rootPairing hG hi D).coroot α : V T) = 0 := sub_self _
  rw [h0, zero_add]
  unfold ArthurCombinatorics.corootValue
  rw [rootPairing_toLinearMap]
  exact pair_toRootSpan hG hi D Λ (Submodule.coe_mem _)

/-- **Langlands' sign.** `ε_Q^P(Λ) = (−1)^{#{α ∈ Δ_Q^P : Λ(α^∨) ≤ 0}}`, with `α^∨` the projection
to `𝔞_Q` of the coroot of the simple root `β ∈ Δ_0^P ∖ Δ_0^Q` restricting to `α`. -/
theorem epsilon_eq (JQ JP : Set (characterLattice T)) (Λ : Vstar T) :
    epsilon hG hi ν D JQ JP Λ =
      (-1) ^ ((standardIndex hG hi ν JP \ standardIndex hG hi ν JQ).filter fun α =>
        pair T Λ (levelProjection hG hi ν D JQ (D.realCoroot ⟨α.1, α.2.1⟩)) ≤ 0).card := by
  unfold epsilon ArthurCombinatorics.epsilon
  simp_rw [corootValue_eq]

/-- **Langlands' function.** `φ_Q^P(Λ, H) = 1` exactly when, for every `β ∈ Δ_0^P ∖ Δ_0^Q`,
`ϖ_β(H) > 0` if `Λ(α^∨) ≤ 0` and `ϖ_β(H) ≤ 0` if `Λ(α^∨) > 0`, where `α^∨` is as in
`epsilon_eq` and `ϖ_β = weight … JP β`. -/
theorem phi_eq (JQ JP : Set (characterLattice T)) (Λ : Vstar T) (H : V T) :
    phi hG hi ν D JQ JP Λ H =
      if ∀ α ∈ standardIndex hG hi ν JP \ standardIndex hG hi ν JQ,
          (pair T Λ (levelProjection hG hi ν D JQ (D.realCoroot ⟨α.1, α.2.1⟩)) ≤ 0 →
            0 < weight hG hi ν D JP α H) ∧
          (0 < pair T Λ (levelProjection hG hi ν D JQ (D.realCoroot ⟨α.1, α.2.1⟩)) →
            weight hG hi ν D JP α H ≤ 0) then 1 else 0 := by
  unfold phi ArthurCombinatorics.phi
  simp_rw [corootValue_eq, weight_coe]

end Functions

section Spaces

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

/-- `𝔞_P ⊂ 𝔞_0` for the standard parabolic subgroup `P` with `Δ_0^P = J`: the common kernel of
the roots of `J` (Arthur 2005, §5, p.26). For `J = Δ_0` it is `𝔞_G`
(`aSpace_simpleRelativeRoots`). -/
abbrev aSpace (T : CommGroupScheme (Spec (CommRingCat.of k))) (J : Set (characterLattice T)) :
    Submodule ℝ (V T) :=
  rootAnnihilator T J

/-- `𝔞_0^P ⊂ 𝔞_0`: the span of the coroots of `J = Δ_0^P`. -/
abbrev corootSubspace (J : Set (characterLattice T)) : Submodule ℝ (V T) :=
  Submodule.span ℝ (D.realCorootsOf J)

/-- `𝔞_P^Q ⊂ 𝔞_P` for `Δ_0^P = J ⊆ Δ_0^Q = K`: the published `leviCorootSpace`, the part of
`𝔞_P` in the span of the coroots of `K`. -/
abbrev relativeSpace (J K : Set (characterLattice T)) : Submodule ℝ (V T) :=
  D.leviCorootSpace J K

omit [Mono i.hom.hom.left] in
include hG hi hν in
/-- `𝔞_G = 𝔞_{P}` for `P = G` (`J = Δ_0`) is the common kernel of all relative roots. -/
theorem aSpace_simpleRelativeRoots :
    aSpace T (simpleRelativeRoots i ν) = relativeCentralDirections i :=
  (standardLeviRealDecomposition k G hG T i hi ν hν
    (relativeRootReflectionExistence k G hG T i hi).choose).2.1

include hG hi hν in
/-- `𝔞_0 = 𝔞_0^P ⊕ 𝔞_P` for `Δ_0^P = J ⊆ Δ_0`. -/
theorem isCompl_corootSubspace_aSpace {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    IsCompl (corootSubspace D J) (aSpace T J) :=
  ((standardLeviRealDecomposition k G hG T i hi ν hν D).2.2.2 J J subset_rfl hJ).2.1.symm

include hG hi hν in
/-- `𝔞_P = 𝔞_P^Q ⊕ 𝔞_Q` for `Δ_0^P = J ⊆ Δ_0^Q = K ⊆ Δ_0`: the two summands are disjoint. -/
theorem disjoint_aSpace_relativeSpace {J K : Set (characterLattice T)} (hJK : J ⊆ K)
    (hK : K ⊆ simpleRelativeRoots i ν) :
    Disjoint (aSpace T K) (relativeSpace D J K) :=
  ((standardLeviRealDecomposition k G hG T i hi ν hν D).2.2.2 J K hJK hK).2.2.2.2.2.2.1

include hG hi hν in
/-- `𝔞_P = 𝔞_P^Q ⊕ 𝔞_Q`: the two summands span `𝔞_P`. -/
theorem aSpace_sup_relativeSpace {J K : Set (characterLattice T)} (hJK : J ⊆ K)
    (hK : K ⊆ simpleRelativeRoots i ν) :
    aSpace T K ⊔ relativeSpace D J K = aSpace T J :=
  ((standardLeviRealDecomposition k G hG T i hi ν hν D).2.2.2 J K hJK hK).2.2.2.2.2.2.2.1

/-- **`H ↦ H_P` is the projection of `𝔞_0 = 𝔞_0^P ⊕ 𝔞_P` onto `𝔞_P`.** -/
theorem levelProjection_eq_projectionOnto {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (H : V T) :
    (Submodule.projectionOnto (aSpace T J) (corootSubspace D J)
        (isCompl_corootSubspace_aSpace hG hi hν D hJ).symm H : V T) =
      levelProjection hG hi ν D J H := by
  have h1 := levelProjection_mem_rootAnnihilator hG hi D hν hJ H
  have h2 := sub_levelProjection_mem_span hG hi (ν := ν) D J H
  have hH : H = levelProjection hG hi ν D J H + (H - levelProjection hG hi ν D J H) := by abel
  conv_lhs => rw [hH]
  rw [map_add, Submodule.projectionOnto_apply_of_mem_left _ h1,
    Submodule.projectionOnto_apply_of_mem_right _ h2, add_zero]

end Spaces

end Langlands.GroupScheme.ArthurRelative
