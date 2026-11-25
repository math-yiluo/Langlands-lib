import Langlands.Theta.Heisenberg.SelfDual
import Langlands.HarmonicAnalysis.AdditiveCharacterExists
import Langlands.Representation.Smooth.Definitions
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The induced model of the Heisenberg representation over a nonarchimedean local field

GKT §1.2.1 (Definition 1.6, p. 20; Corollary 1.4, p. 19; Proposition 1.12, p. 23). Let `B` be an
alternating form on a finite-dimensional vector space `W` over a nonarchimedean local field `F`
with `2` invertible, and `ψ` a continuous additive character of `F`.

* A `SelfDualDatum B ψ` is a subgroup `A` of `W` equal to its orthogonal for the pairing `ψ ∘ B`
  (it contains `charOrthogonal B ψ A`, and the cocycle vanishes on it), a function `ψ_A`
  (`character`) splitting the cocycle `ψ (⅟2 * B a b)` on `A`, with `A` open and `ψ_A = 1` near
  `0`, and the finiteness of `A` modulo the orthogonals of suitable sets. For non-degenerate `B`
  and non-trivial `ψ` such a datum exists (`nonempty_selfDualDatum`): `A` is a maximal
  self-orthogonal subgroup containing a small lattice, found by Zorn's lemma, and `ψ_A` is
  obtained from the injectivity of `ℂˣ` (the role of the exactness of Pontryagin duality in the
  proof of Corollary 1.4).
* The induced model `inducedModel D` is `Ind_{H(A)}^{H(W)} ψ_A`, realized as the subrepresentation
  of `regular B ψ` (functions on `W`) spanned by the translates of `ψ_A · 1_A`. It is smooth,
  irreducible (Proposition 1.12), and has central character `ψ`.

The proof of irreducibility is not the book's: in a smooth representation with central character
`ψ`, every non-zero invariant subspace contains a `ψ_A`-eigenvector of `A`
(`SelfDualDatum.exists_eigenvector_mem`), and the `ψ_A`-eigenvectors in the span of the
translates of one of them form a line. The second fact makes the span of the translates of an
eigenvector irreducible (`SelfDualDatum.isIrreducible_translatesSpan`); it is used again for the
uniqueness in `Langlands.Theta.Heisenberg.StoneVonNeumann`.
-/
noncomputable section

open Filter Topology

namespace Langlands.HeisenbergGroup

universe u v w

open Internal

section Datum

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {W : Type v} [AddCommGroup W] [Module R W]
  [TopologicalSpace W]

/-- A self-dual datum: a subgroup `A = subgroup` of `W` that contains its orthogonal for `ψ ∘ B`
(it is in fact equal to it: `A` is self-dual, GKT p. 19), a function `ψ_A = character` on `W`
whose restriction to `A` splits the cocycle `ψ (⅟2 * B a b)` (so that `(a, t) ↦ ψ t ψ_A a` is a
character of `H(A) = A × R` extending `ψ`, GKT Corollary 1.4), such that `A` is a neighbourhood
of `0` on which `ψ_A = 1` near `0`, and such that every neighbourhood of `0` contains the orthogonal
of a set `T` with `A` finite modulo it. -/
structure SelfDualDatum (B : LinearMap.BilinForm R W) (ψ : AddChar R ℂ) where
  /-- The self-dual subgroup `A`. -/
  subgroup : AddSubgroup W
  /-- The extension `ψ_A` of `ψ` to `H(A)`, as a function on `W` (its values off `A` play no
  part). -/
  character : W → ℂ
  character_ne_zero : ∀ a ∈ subgroup, character a ≠ 0
  character_mul : ∀ a ∈ subgroup, ∀ b ∈ subgroup,
    character a * character b = ψ (⅟2 * B a b) * character (a + b)
  charOrthogonal_le : charOrthogonal B ψ subgroup ≤ subgroup
  eventually_mem : ∀ᶠ u in 𝓝 (0 : W), u ∈ subgroup ∧ character u = 1
  exists_finite : ∀ N ∈ 𝓝 (0 : W), ∃ T : Set W, (charOrthogonal B ψ T : Set W) ⊆ N ∧
    Finite (subgroup ⧸ (charOrthogonal B ψ T).addSubgroupOf subgroup)

namespace SelfDualDatum

variable {B : LinearMap.BilinForm R W} {ψ : AddChar R ℂ} (D : SelfDualDatum B ψ)

/-- The character `ψ_A` splits the cocycle `ψ(½ B)` on `A`. -/
theorem splitsOn : SplitsOn (fun x y => ψ (⅟2 * B x y)) D.subgroup D.character :=
  ⟨D.character_ne_zero, D.character_mul⟩

/-- The vector `ψ_A · 1_A` that generates the induced model. -/
def characterVector : W → ℂ := (D.subgroup : Set W).indicator D.character

/-- `ψ_A · 1_A ≠ 0`. -/
theorem characterVector_ne_zero : D.characterVector ≠ 0 := fun h =>
  D.character_ne_zero 0 D.subgroup.zero_mem (by simpa [characterVector] using congrFun h 0)

/-- `ψ_A · 1_A` is a `ψ_A`-eigenvector of `A` in the regular representation. -/
theorem regularFun_characterVector (a : W) (ha : a ∈ D.subgroup) :
    regularFun B ψ a D.characterVector = D.character a • D.characterVector :=
  translate_indicator D.splitsOn a ha

end SelfDualDatum

end Datum

section Local

open ValuativeRel

/-- The orbit of a point of a compact set `K ⊇ A` modulo an open subgroup is finite. -/
private theorem finite_quot {W : Type*} [AddCommGroup W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] (A U : AddSubgroup W) (hU : (U : Set W) ∈ 𝓝 0) {K : Set W}
    (hK : IsCompact K) (hA : (A : Set W) ⊆ K) : Finite (A ⧸ U.addSubgroupOf A) := by
  have := QuotientAddGroup.discreteTopology (U.isOpen_of_mem_nhds hU)
  have hfin : ((QuotientAddGroup.mk : W → W ⧸ U) '' K).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  refine Set.finite_univ_iff.1 (Set.Finite.of_finite_image
    (f := fun q : A ⧸ U.addSubgroupOf A => (q.out.1 : W ⧸ U)) (hfin.subset ?_) fun p _ q _ hpq => ?_)
  · rintro _ ⟨q, -, rfl⟩
    exact ⟨_, hA q.out.2, rfl⟩
  · rw [← p.out_eq, ← q.out_eq]
    have := QuotientAddGroup.eq.1 hpq
    exact QuotientAddGroup.eq.2 this

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

private theorem isCompact_int : IsCompact (𝒪[F] : Set F) :=
  IsNonarchimedeanLocalField.isCompact_closedBall F 1

private theorem exists_ne_zero {p : F → Prop} (hp : ∀ᶠ r in 𝓝 (0 : F), p r) : ∃ r, r ≠ 0 ∧ p r := by
  obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' F).mem_iff.1 hp
  obtain ⟨y, rfl⟩ := ValuativeRel.valuation_surjective γ
  obtain ⟨r, hr, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation F)
  refine ⟨y * r, mul_ne_zero (by simpa using hγ) hr, hs ?_⟩
  show valuation F (y * r) < valuation F y
  rw [map_mul]
  exact mul_lt_of_lt_one_right (zero_lt_iff.2 hγ) hr1

/-- A continuous character is trivial on `𝒪 · z` for `z` near `0`. -/
private theorem eventually_psi {ψ : AddChar F ℂ} (hψ : Continuous ψ) :
    ∀ᶠ z in 𝓝 (0 : F), ∀ o ∈ 𝒪[F], ψ (o * z) = 1 := by
  have h1 : ∀ᶠ z in 𝓝 (0 : F), ∀ o ∈ (𝒪[F] : Set F), ‖ψ (o * z) - 1‖ < 1 / 2 := by
    refine isCompact_int.eventually_forall_of_forall_eventually fun o _ => ?_
    have hc : Continuous fun z : F × F => ‖ψ (z.2 * z.1) - 1‖ := by fun_prop
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [h1] with z hz o ho
  refine Langlands.complex_eq_one_of_forall_norm_pow_sub_one_lt fun n => ?_
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ← mul_assoc]
  exact hz _ (mul_mem (natCast_mem _ n) ho)

private theorem eventually_psi' {ψ : AddChar F ℂ} (hψ : Continuous ψ) :
    ∀ᶠ z in 𝓝 (0 : F), ψ z = 1 := by
  filter_upwards [eventually_psi hψ] with z hz
  simpa using hz 1 (one_mem _)

variable [Invertible (2 : F)] {W : Type v} [AddCommGroup W] [Module F W]
  {B : LinearMap.BilinForm F W}

variable [FiniteDimensional F W] [TopologicalSpace W] [IsModuleTopology F W]

omit [Invertible (2 : F)] in
/-- For each `w`, the character `u ↦ ψ (B u w)` is trivial near `0`. -/
theorem eventually_psi_apply_eq_one {ψ : AddChar F ℂ} (hψ : Continuous ψ) (w : W) :
    ∀ᶠ u in 𝓝 (0 : W), ψ (B u w) = 1 := by
  have hcB : Continuous fun p : W × W => B p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left B
  have hcw : Continuous fun u => B u w := hcB.comp (f := fun u => (u, w)) (by fun_prop)
  exact ((hcw.tendsto' 0 0 (by simp)).eventually (eventually_psi' hψ))

/-- A self-dual datum exists for a non-degenerate alternating form and a non-trivial continuous
character. -/
theorem nonempty_selfDualDatum (hB : B.IsAlt) (hn : B.Nondegenerate) {ψ : AddChar F ℂ}
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) : Nonempty (SelfDualDatum B ψ) := by
  classical
  have := IsModuleTopology.isTopologicalAddGroup F W
  have := IsModuleTopology.toContinuousSMul (R := F) (A := W)
  set h := isAlternatingBicharacter_psi (ψ := ψ) hB
  obtain ⟨t₀, ht₀⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra hc
    push Not at hc
    exact hψ1 (AddChar.ext _ _ hc)
  have ht0 : t₀ ≠ 0 := by rintro rfl; simp at ht₀
  let b := Module.finBasis F W
  let b' := B.dualBasis hn b
  have hcB : Continuous fun p : W × W => B p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left B
  have hcw : ∀ w, Continuous fun u => B u w := fun w => hcB.comp (f := fun u => (u, w)) (by fun_prop)
  let K : Set W := b'.equivFun.symm '' Set.pi Set.univ fun _ => (𝒪[F] : Set F)
  have hK : IsCompact K := (isCompact_univ_pi fun _ => isCompact_int).image
    (IsModuleTopology.continuous_of_linearMap b'.equivFun.symm.toLinearMap)
  let T : F → Set W := fun s => {t | ∃ i, ∃ o ∈ 𝒪[F], t = (s * o) • b i}
  have hmem : ∀ s x, x ∈ charOrthogonal B ψ (T s) ↔
      ∀ i, ∀ o ∈ 𝒪[F], ψ (o * (s * B x (b i))) = 1 := by
    intro s x
    have e : ∀ i o, ψ (B x ((s * o) • b i)) = ψ (o * (s * B x (b i))) := fun i o => by
      rw [map_smul, smul_eq_mul]; congr 1; ring
    constructor
    · intro hx i o ho
      rw [← e]; exact hx _ ⟨i, o, ho, rfl⟩
    · rintro hx _ ⟨i, o, ho, rfl⟩
      exact (e i o).trans (hx i o ho)
  have fA : ∀ r, r ≠ 0 → ∀ x ∈ charOrthogonal B ψ (T (t₀ / r)), ∃ y ∈ K, x = r • y := by
    intro r hr x hx
    refine ⟨r⁻¹ • x, ⟨fun i => r⁻¹ * B x (b i), fun i _ => ?_, ?_⟩, by rw [smul_inv_smul₀ hr]⟩
    · by_contra hc
      have hz : r⁻¹ * B x (b i) ≠ 0 := fun h0 => hc (by beta_reduce; rw [h0]; exact zero_mem _)
      have hi : (r⁻¹ * B x (b i))⁻¹ ∈ 𝒪[F] :=
        ((valuation F).valuationSubring.mem_or_inv_mem _).resolve_left hc
      have := (hmem _ x).1 hx i _ hi
      apply ht₀
      rw [← this]; congr 1
      have := right_ne_zero_of_mul hz
      field_simp
    · rw [LinearEquiv.symm_apply_eq]
      funext i
      simp [b']
  have fB : ∀ s, (charOrthogonal B ψ (T s) : Set W) ∈ 𝓝 0 := by
    intro s
    have : ∀ᶠ x in 𝓝 (0 : W), ∀ i, ∀ o ∈ 𝒪[F], ψ (o * (s * B x (b i))) = 1 := by
      refine eventually_all.2 fun i => ?_
      have hc : Continuous fun x => s * B x (b i) := continuous_const.mul (hcw _)
      exact (hc.tendsto' 0 0 (by simp)).eventually (eventually_psi hψ)
    filter_upwards [this] with x hx using (hmem s x).2 hx
  have fC : ∀ N ∈ 𝓝 (0 : W), ∀ C, IsCompact C → ∃ r : F, r ≠ 0 ∧ ∀ y ∈ C, r • y ∈ N := by
    intro N hN C hC
    refine exists_ne_zero (hC.eventually_forall_of_forall_eventually fun y _ => ?_)
    exact (continuous_smul.tendsto' ((0 : F), y) 0 (by simp)).eventually hN
  obtain ⟨r, hr, hrK⟩ : ∃ r : F, r ≠ 0 ∧ ∀ p ∈ K ×ˢ K, ψ (⅟2 * (r * r * B p.1 p.2)) = 1 := by
    refine exists_ne_zero ((hK.prod hK).eventually_forall_of_forall_eventually fun p _ => ?_)
    have hc : Continuous fun z : F × W × W => ⅟2 * (z.1 * z.1 * B z.2.1 z.2.2) :=
      continuous_const.mul ((continuous_fst.mul continuous_fst).mul (hcB.comp continuous_snd))
    exact (hc.tendsto' (0, p) 0 (by simp)).eventually (eventually_psi' hψ)
  set L := charOrthogonal B ψ (T (t₀ / r))
  have hL : ∀ x ∈ L, ∀ y ∈ L, ψ (⅟2 * B x y) = 1 := by
    intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := fA r hr x hx
    obtain ⟨y', hy', rfl⟩ := fA r hr y hy
    rw [← hrK (x', y') ⟨hx', hy'⟩]; congr 2; simp; ring
  have hL' : L ≤ h.orthogonal L := fun x hx y hy => by
    show ψ (⅟2 * B x y) ^ 2 = 1
    rw [hL x hx y hy, one_pow]
  obtain ⟨A, hLA, hA, hA'⟩ := exists_le_selfOrthogonal h L hL'
  obtain ⟨α, hα, hαL⟩ := exists_splitsOn h hLA hL hA
  obtain ⟨s, hs, hsL⟩ := fC _ (fB (t₀ / r)) (⋃ i, (fun o : F => o • b i) '' (𝒪[F] : Set F))
    (isCompact_iUnion fun i => isCompact_int.image (by fun_prop))
  have hAK : (A : Set W) ⊆ (fun y => (t₀ / s) • y) '' K := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := fA (t₀ / s) (div_ne_zero ht0 hs) a (by
      rintro _ ⟨i, o, ho, rfl⟩
      have hmemL : (t₀ / (t₀ / s) * o) • b i ∈ L := by
        rw [div_div_cancel₀ ht0, mul_smul]
        exact hsL _ (Set.mem_iUnion.2 ⟨i, o, ho, rfl⟩)
      exact (psi_half_sq _).symm.trans (hA ha _ (hLA hmemL)))
    exact ⟨y, hy, rfl⟩
  rw [orthogonal_psi_eq hB] at hA'
  refine ⟨⟨A, α, hα.ne_zero, hα.mul, hA', ?_, fun N hN => ?_⟩⟩
  · filter_upwards [fB (t₀ / r)] with u hu using ⟨hLA hu, hαL u hu⟩
  · obtain ⟨q, hq, hqN⟩ := fC N hN K hK
    refine ⟨T (t₀ / q), fun x hx => ?_, finite_quot A _ (fB _) (hK.image (by fun_prop)) hAK⟩
    obtain ⟨y, hy, rfl⟩ := fA q hq x hx
    exact hqN y hy

end Local

section Group

variable {F : Type u} [Field F] [Invertible (2 : F)] {W : Type v} [AddCommGroup W] [Module F W]
  {B : LinearMap.BilinForm F W} {M : Type w} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (HeisenbergGroup B) M}

/-- The span of the translates `π (x, 0) e` of a vector, as a subrepresentation (for a
representation with a central character). -/
def translatesSpan (hπ : HasCentralCharacter π ψ) (e : M) : Subrepresentation π where
  toSubmodule := Submodule.span ℂ (Set.range fun x => π (ofVec x) e)
  apply_mem_toSubmodule g v hv := by
    have : (Submodule.span ℂ (Set.range fun x => π (ofVec x) e)).map (π g) ≤
        Submodule.span ℂ (Set.range fun x => π (ofVec x) e) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨y, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul, hπ.apply_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    exact this ⟨v, hv, rfl⟩

/-- A vector lies in the span of its translates. -/
theorem mem_translatesSpan (hπ : HasCentralCharacter π ψ) (e : M) :
    e ∈ (translatesSpan hπ e).toSubmodule :=
  Submodule.subset_span ⟨0, by simp⟩

/-- The span of the translates has central character `ψ`. -/
theorem hasCentralCharacter_translatesSpan (hπ : HasCentralCharacter π ψ) (e : M) :
    HasCentralCharacter (translatesSpan hπ e).toRepresentation ψ :=
  fun t v => Subtype.ext (hπ t v.1)

/-- In the span of the translates of `e`, the translates of `e` span. -/
theorem span_translatesSpan_eq_top (hπ : HasCentralCharacter π ψ) (e : M) :
    Submodule.span ℂ (Set.range fun x => (translatesSpan hπ e).toRepresentation (ofVec x)
      ⟨e, mem_translatesSpan hπ e⟩) = ⊤ := by
  apply Submodule.map_injective_of_injective (translatesSpan hπ e).toSubmodule.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  rfl

section Induced

variable [TopologicalSpace W] (D : SelfDualDatum B ψ)

/-- The induced model `Ind_{H(A)}^{H(W)} ψ_A` (GKT Definition 1.6), realized as the
subrepresentation of `regular B ψ` spanned by the translates of `ψ_A · 1_A`. -/
def inducedModel : Subrepresentation (regular B ψ) :=
  translatesSpan (hasCentralCharacter_regular B ψ) D.characterVector

/-- `ψ_A · 1_A` lies in the induced model. -/
theorem characterVector_mem_inducedModel : D.characterVector ∈ (inducedModel D).toSubmodule :=
  mem_translatesSpan _ _

/-- The induced model has central character `ψ`. -/
theorem hasCentralCharacter_inducedModel :
    HasCentralCharacter (inducedModel D).toRepresentation ψ :=
  hasCentralCharacter_translatesSpan _ _

end Induced

variable [TopologicalSpace F] [TopologicalSpace W]

/-- A smooth representation fixes each vector by all `(u, 0)` with `u` near `0`. -/
theorem eventually_apply_ofVec_eq_self (hs : IsSmooth π) (v : M) :
    ∀ᶠ u in 𝓝 (0 : W), π (ofVec u) v = v := by
  obtain ⟨K, hK⟩ := hs v
  have hK1 : (K : Set (HeisenbergGroup B)) ∈ 𝓝 (ofVec 0) := K.isOpen.mem_nhds K.one_mem
  filter_upwards [continuous_ofVec.continuousAt.preimage_mem_nhds hK1] with u hu
  exact (Representation.mem_invariants _ v).1 hK ⟨ofVec u, hu⟩

variable [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W]
  [IsModuleTopology F W]

/-- A representation with continuous central character in which every vector is fixed by all
`(u, 0)` with `u` near `0` is smooth. -/
theorem isSmooth_of_eventually (hψ : Continuous ψ) (hπ : HasCentralCharacter π ψ)
    (hs : ∀ v, ∀ᶠ u in 𝓝 (0 : W), π (ofVec u) v = v) : IsSmooth π := by
  intro v
  let S : Subgroup (HeisenbergGroup B) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {x y} hx hy => by
        show π (x * y) v = v
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        show π x⁻¹ v = v
        conv_lhs => rw [← show π x v = v from hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  have hS : (S : Set (HeisenbergGroup B)) ∈ 𝓝 1 := by
    filter_upwards [(continuous_vec.tendsto' 1 0 rfl).eventually (hs v),
      (continuous_cen.tendsto' 1 0 rfl).eventually (eventually_psi' hψ)] with g h1 h2
    show π g v = v
    rw [hπ.apply_eq, h1, h2, one_smul]
  exact ⟨⟨S, S.isOpen_of_mem_nhds hS⟩, (Representation.mem_invariants _ v).2 fun g => g.2⟩

variable (hB : B.IsAlt) (D : SelfDualDatum B ψ)
include hB

namespace SelfDualDatum

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W]
  [IsModuleTopology F W] in
/-- Every non-zero subrepresentation of a smooth representation with central character `ψ`
contains a non-zero eigenvector of `(a, 0)`, `a ∈ A`, with eigenvalue `ψ_A a`. -/
theorem exists_eigenvector_mem (hπ : HasCentralCharacter π ψ) (hs : IsSmooth π)
    (P : Subrepresentation π) (hP : P ≠ ⊥) :
    ∃ e ∈ P.toSubmodule, e ≠ 0 ∧ ∀ a ∈ D.subgroup, π (ofVec a) e = D.character a • e := by
  have : P.toSubmodule ≠ ⊥ := fun h => hP (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 this
  obtain ⟨T, hT, hfin⟩ := D.exists_finite _ (D.eventually_mem.and (eventually_apply_ofVec_eq_self hs v))
  rw [← orthogonal_psi_eq hB] at hT hfin
  exact exists_eigenvector (isAlternatingBicharacter_psi hB) (isProjectiveRep_of_hasCentralCharacter hπ)
    D.splitsOn T (fun u hu => (hT hu).1.2) P.toSubmodule
    (fun x m hm => P.apply_mem_toSubmodule _ hm) v hv hv0 fun u hu => (hT hu).2

/-- The span of the translates of a non-zero `ψ_A`-eigenvector is smooth. -/
theorem isSmooth_of_span_eq_top (hψ : Continuous ψ) (hπ : HasCentralCharacter π ψ) {e : M}
    (he : ∀ a ∈ D.subgroup, π (ofVec a) e = D.character a • e)
    (hsp : Submodule.span ℂ (Set.range fun x => π (ofVec x) e) = ⊤) : IsSmooth π := by
  refine isSmooth_of_eventually hψ hπ fun v => ?_
  have hv : v ∈ Submodule.span ℂ (Set.range fun x => π (ofVec x) e) := hsp ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    filter_upwards [D.eventually_mem, eventually_psi_apply_eq_one hψ x] with u hu hu'
    have := (isProjectiveRep_of_hasCentralCharacter hπ).comm (isAlternatingBicharacter_psi hB) u x e
    beta_reduce at this ⊢
    rw [this, psi_half_sq, hu', he u hu.1, hu.2, one_smul, one_smul]
  | zero => simp
  | add a b _ _ ha hb => filter_upwards [ha, hb] with u ha hb using by rw [map_add, ha, hb]
  | smul r a _ ha => filter_upwards [ha] with u ha using by rw [map_smul, ha]

/-- A representation with central character `ψ` spanned by the translates of a non-zero
`ψ_A`-eigenvector is irreducible. -/
theorem isIrreducible_of_span_eq_top (hψ : Continuous ψ) (hπ : HasCentralCharacter π ψ) {e : M}
    (he0 : e ≠ 0) (he : ∀ a ∈ D.subgroup, π (ofVec a) e = D.character a • e)
    (hsp : Submodule.span ℂ (Set.range fun x => π (ofVec x) e) = ⊤) : π.IsIrreducible := by
  have hs := D.isSmooth_of_span_eq_top hB hψ hπ he hsp
  have : Nontrivial (Subrepresentation π) := ⟨⊥, ⊤, fun h => he0 (by
    have : e ∈ (⊥ : Subrepresentation π).toSubmodule := h ▸ Submodule.mem_top
    exact this)⟩
  refine ⟨fun P => or_iff_not_imp_left.2 fun hP => ?_⟩
  obtain ⟨e', hP', he0', he'⟩ := D.exists_eigenvector_mem hB hπ hs P hP
  have hA := D.charOrthogonal_le
  rw [← orthogonal_psi_eq hB] at hA
  obtain ⟨r, rfl⟩ := exists_eq_smul_of_mem_span (isAlternatingBicharacter_psi hB)
    (isProjectiveRep_of_hasCentralCharacter hπ) D.splitsOn hA he (v := e')
    (hsp ▸ Submodule.mem_top) he'
  have heP : e ∈ P.toSubmodule := (Submodule.smul_mem_iff _ (left_ne_zero_of_smul he0')).1 hP'
  refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 ?_)
  rw [← hsp, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact P.apply_mem_toSubmodule _ heP

/-- The span of the translates of a non-zero `ψ_A`-eigenvector is smooth. -/
theorem isSmooth_translatesSpan (hψ : Continuous ψ) (hπ : HasCentralCharacter π ψ) {e : M}
    (he : ∀ a ∈ D.subgroup, π (ofVec a) e = D.character a • e) :
    IsSmooth (translatesSpan hπ e).toRepresentation :=
  D.isSmooth_of_span_eq_top hB hψ (hasCentralCharacter_translatesSpan hπ e)
    (e := ⟨e, mem_translatesSpan hπ e⟩) (fun a ha => Subtype.ext (he a ha))
    (span_translatesSpan_eq_top hπ e)

/-- The span of the translates of a non-zero `ψ_A`-eigenvector is irreducible. -/
theorem isIrreducible_translatesSpan (hψ : Continuous ψ) (hπ : HasCentralCharacter π ψ) {e : M}
    (he0 : e ≠ 0) (he : ∀ a ∈ D.subgroup, π (ofVec a) e = D.character a • e) :
    (translatesSpan hπ e).toRepresentation.IsIrreducible :=
  D.isIrreducible_of_span_eq_top hB hψ (hasCentralCharacter_translatesSpan hπ e)
    (e := ⟨e, mem_translatesSpan hπ e⟩) (fun h => he0 (congrArg Subtype.val h))
    (fun a ha => Subtype.ext (he a ha)) (span_translatesSpan_eq_top hπ e)

end SelfDualDatum

include hB

/-- The induced model is smooth. -/
theorem isSmooth_inducedModel (hψ : Continuous ψ) : IsSmooth (inducedModel D).toRepresentation :=
  D.isSmooth_translatesSpan hB hψ _ fun a ha => by
    simpa using D.regularFun_characterVector a ha

/-- The induced model is irreducible (GKT Proposition 1.12). -/
theorem isIrreducible_inducedModel (hψ : Continuous ψ) :
    (inducedModel D).toRepresentation.IsIrreducible :=
  D.isIrreducible_translatesSpan hB hψ _ D.characterVector_ne_zero fun a ha => by
    simpa using D.regularFun_characterVector a ha

end Group

/-! ### The induced model of a closed self-dual subgroup -/

section Closed

open scoped Pointwise

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {W : Type v} [AddCommGroup W] [Module R W]
  [TopologicalSpace W]

/-- **A closed self-dual subgroup with an extension of `ψ`** (GKT §1.2.1: Lemma 1.2, the definition
of a self-dual subgroup, p. 19, and Corollary 1.4): a closed subgroup `A` of `W` equal to its
orthogonal for `ψ ∘ B`, and a function `ψ_A` on `W` whose restriction to `A` splits the cocycle
`ψ(½ B)` on `A`, so that `(a, t) ↦ ψ t ψ_A a` is a character of `H(A) = A × R` extending `ψ`. The
values of `ψ_A` off `A` play no part. -/
structure InducingDatum (B : LinearMap.BilinForm R W) (ψ : AddChar R ℂ) where
  /-- The closed self-dual subgroup `A`. -/
  subgroup : AddSubgroup W
  isClosed : IsClosed (subgroup : Set W)
  charOrthogonal_eq : charOrthogonal B ψ subgroup = subgroup
  /-- The extension `ψ_A` of `ψ` to `H(A)`, as a function on `W`. -/
  character : W → ℂ
  character_ne_zero : ∀ a ∈ subgroup, character a ≠ 0
  character_mul : ∀ a ∈ subgroup, ∀ b ∈ subgroup,
    character a * character b = ψ (⅟2 * B a b) * character (a + b)

namespace InducingDatum

variable {B : LinearMap.BilinForm R W} {ψ : AddChar R ℂ} (D : InducingDatum B ψ)

/-- The space of the induced model `Ind_{H(A)}^{H(W)} ψ_A` in its realization on functions on `W`
(GKT p. 29): the functions `f` with `f (a + w) = ψ_A(a) ψ(½ B(w, a)) f(w)` for `a ∈ A`, locally
constant, and vanishing off `A + K` for a compact set `K` (compactly supported modulo `A`,
Corollary 1.10). -/
def inducedSubmodule : Submodule ℂ (W → ℂ) where
  carrier := {f | (∀ a ∈ D.subgroup, ∀ w, f (a + w) = D.character a * ψ (⅟2 * B w a) * f w) ∧
    IsLocallyConstant f ∧ ∃ K : Set W, IsCompact K ∧ ∀ w, f w ≠ 0 → w ∈ (D.subgroup : Set W) + K}
  add_mem' := by
    rintro f g ⟨hf1, hf2, K, hK, hfK⟩ ⟨hg1, hg2, L, hL, hgL⟩
    refine ⟨fun a ha w => ?_, hf2.add hg2, K ∪ L, hK.union hL, fun w hw => ?_⟩
    · simp only [Pi.add_apply, hf1 a ha w, hg1 a ha w]; ring
    · by_cases h : f w = 0
      · have : g w ≠ 0 := by simpa [h] using hw
        exact Set.add_subset_add_left Set.subset_union_right (hgL w this)
      · exact Set.add_subset_add_left Set.subset_union_left (hfK w h)
  zero_mem' := ⟨fun a _ w => by simp, IsLocallyConstant.const 0, ∅, isCompact_empty,
    fun w hw => absurd rfl hw⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2, K, hK, hfK⟩
    refine ⟨fun a ha w => ?_, hf2.comp fun z => c • z, K, hK, fun w hw => hfK w fun h => hw ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf1 a ha w]; ring
    · simp [h]

theorem mem_inducedSubmodule {f : W → ℂ} : f ∈ D.inducedSubmodule ↔
    (∀ a ∈ D.subgroup, ∀ w, f (a + w) = D.character a * ψ (⅟2 * B w a) * f w) ∧
      IsLocallyConstant f ∧
      ∃ K : Set W, IsCompact K ∧ ∀ w, f w ≠ 0 → w ∈ (D.subgroup : Set W) + K :=
  Iff.rfl

variable [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalAddGroup W]

/-- The translation operators of the regular representation preserve the induced space. -/
theorem regularFun_mem (hB : B.IsAlt) (hψ : IsLocallyConstant ψ)
    (hBc : ∀ v, Continuous fun z => B z v) (v : W) {f : W → ℂ} (hf : f ∈ D.inducedSubmodule) :
    regularFun B ψ v f ∈ D.inducedSubmodule := by
  obtain ⟨hf1, hf2, K, hK, hfK⟩ := hf
  refine ⟨fun a ha w => ?_, ?_, (fun k => k - v) '' K, hK.image (continuous_sub_right v),
    fun z hz => ?_⟩
  · simp only [regularFun_apply]
    rw [add_assoc, hf1 a ha (w + v)]
    have e : ⅟2 * B (a + w) v + ⅟2 * B (w + v) a = ⅟2 * B w a + ⅟2 * B w v := by
      simp only [map_add, LinearMap.add_apply]
      rw [← hB.neg_eq a v]
      ring
    calc ψ (⅟2 * B (a + w) v) * (D.character a * ψ (⅟2 * B (w + v) a) * f (w + v))
        = D.character a * (ψ (⅟2 * B (a + w) v) * ψ (⅟2 * B (w + v) a)) * f (w + v) := by ring
      _ = D.character a * (ψ (⅟2 * B w a) * ψ (⅟2 * B w v)) * f (w + v) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, e]
      _ = _ := by ring
  · exact (hψ.comp_continuous (continuous_const.mul (hBc v))).mul
      (hf2.comp_continuous (continuous_id.add continuous_const))
  · simp only [regularFun_apply] at hz
    obtain ⟨a, ha, k, hk, hak⟩ := hfK (z + v) (right_ne_zero_of_mul hz)
    exact ⟨a, ha, k - v, ⟨k, hk, rfl⟩, by
      change a + (k - v) = z
      rw [← add_sub_assoc, show a + k = z + v from hak, add_sub_cancel_right]⟩

/-- **The induced model** `Ind_{H(A)}^{H(W)} ψ_A` of a closed self-dual subgroup (GKT Definition
1.6, p. 20), realized on functions on `W` (p. 29) as a subrepresentation of `regular B ψ`; the
element `(w, t)` acts by `f ↦ (z ↦ ψ t ψ(½ B(z, w)) f(z + w))` (right translation). -/
def inducedSpace (hB : B.IsAlt) (hψ : IsLocallyConstant ψ)
    (hBc : ∀ v, Continuous fun z => B z v) : Subrepresentation (regular B ψ) where
  toSubmodule := D.inducedSubmodule
  apply_mem_toSubmodule g f hf := by
    rw [regular_apply]
    exact Submodule.smul_mem _ _ (D.regularFun_mem hB hψ hBc g.vec hf)

/-- The induced model has central character `ψ`. -/
theorem hasCentralCharacter_inducedSpace (hB : B.IsAlt) (hψ : IsLocallyConstant ψ)
    (hBc : ∀ v, Continuous fun z => B z v) :
    HasCentralCharacter (D.inducedSpace hB hψ hBc).toRepresentation ψ :=
  fun t f => Subtype.ext (hasCentralCharacter_regular B ψ t f.1)

end InducingDatum

namespace SelfDualDatum

variable {B : LinearMap.BilinForm R W} {ψ : AddChar R ℂ}

/-- The subgroup of a self-dual datum is open. -/
theorem isOpen_subgroup [IsTopologicalAddGroup W] (D : SelfDualDatum B ψ) :
    IsOpen (D.subgroup : Set W) :=
  AddSubgroup.isOpen_of_mem_nhds D.subgroup (D.eventually_mem.mono fun _ hu => hu.1)

/-- The subgroup of a self-dual datum is contained in its orthogonal (it is self-dual). -/
theorem le_charOrthogonal (hB : B.IsAlt) (D : SelfDualDatum B ψ) :
    D.subgroup ≤ charOrthogonal B ψ D.subgroup := by
  intro a ha b hb
  have h1 := D.character_mul a ha b hb
  have h2 := D.character_mul b hb a ha
  rw [add_comm b a, mul_comm (D.character b)] at h2
  have hne := D.character_ne_zero (a + b) (D.subgroup.add_mem ha hb)
  have h3 : ψ (⅟2 * B a b) = ψ (⅟2 * B b a) := mul_right_cancel₀ hne (h1.symm.trans h2)
  rw [← psi_half_sq, pow_two]
  nth_rewrite 2 [h3]
  rw [← AddChar.map_add_eq_mul, ← mul_add, ← hB.neg_eq a b, add_neg_cancel, mul_zero,
    AddChar.map_zero_eq_one]

/-- **An open self-dual datum is a closed one**: the datum of
`Langlands.Theta.Heisenberg.InducedModel` (an open self-dual subgroup with an extension of `ψ`)
as an `InducingDatum`. -/
def toInducingDatum [IsTopologicalAddGroup W] (hB : B.IsAlt) (D : SelfDualDatum B ψ) :
    InducingDatum B ψ where
  subgroup := D.subgroup
  isClosed := AddSubgroup.isClosed_of_isOpen _ D.isOpen_subgroup
  charOrthogonal_eq := le_antisymm D.charOrthogonal_le (D.le_charOrthogonal hB)
  character := D.character
  character_ne_zero := D.character_ne_zero
  character_mul := D.character_mul

variable [IsTopologicalAddGroup W]

@[simp] theorem toInducingDatum_subgroup (hB : B.IsAlt) (D : SelfDualDatum B ψ) :
    (D.toInducingDatum hB).subgroup = D.subgroup := rfl

@[simp] theorem toInducingDatum_character (hB : B.IsAlt) (D : SelfDualDatum B ψ) :
    (D.toInducingDatum hB).character = D.character := rfl

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- `ψ_A · 1_A` lies in the space of the induced model of the closed datum. -/
theorem characterVector_mem_inducedSubmodule (hB : B.IsAlt) (hψ : IsLocallyConstant ψ)
    (hBc : ∀ v, Continuous fun z => B z v) (D : SelfDualDatum B ψ) :
    D.characterVector ∈ (D.toInducingDatum hB).inducedSubmodule := by
  have hA : IsOpen (D.subgroup : Set W) := D.isOpen_subgroup
  refine ⟨fun a ha w => ?_, ?_, {0}, isCompact_singleton, fun w hw => ?_⟩
  · simp only [characterVector, toInducingDatum_character]
    by_cases hw : w ∈ D.subgroup
    · have haw : a + w ∈ D.subgroup := D.subgroup.add_mem ha hw
      rw [Set.indicator_of_mem (show a + w ∈ (D.subgroup : Set W) from haw),
        Set.indicator_of_mem (show w ∈ (D.subgroup : Set W) from hw)]
      have h1 := D.character_mul a ha w hw
      have h2 : ψ (⅟2 * B w a) * ψ (⅟2 * B a w) = 1 := by
        rw [← AddChar.map_add_eq_mul, ← mul_add, ← hB.neg_eq a w, neg_add_cancel, mul_zero,
          AddChar.map_zero_eq_one]
      calc D.character (a + w) = ψ (⅟2 * B w a) * ψ (⅟2 * B a w) * D.character (a + w) := by
            rw [h2, one_mul]
        _ = D.character a * ψ (⅟2 * B w a) * D.character w := by
            rw [mul_assoc, ← h1]; ring
    · have haw : a + w ∉ D.subgroup := fun h => hw (by
        simpa using D.subgroup.sub_mem h ha)
      rw [Set.indicator_of_notMem (show a + w ∉ (D.subgroup : Set W) from haw),
        Set.indicator_of_notMem (show w ∉ (D.subgroup : Set W) from hw), mul_zero]
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro z
    by_cases hz : z ∈ D.subgroup
    · rw [← map_add_left_nhds_zero z, Filter.eventually_map]
      have hc : Continuous fun u => ⅟2 * B u z := continuous_const.mul (hBc z)
      have hψ1 : ∀ᶠ u in 𝓝 (0 : W), ψ (⅟2 * B u z) = 1 := by
        have h0 : ⅟2 * B 0 z = 0 := by simp
        have := (hc.tendsto 0).eventually (h0 ▸ hψ.eventually_eq 0)
        simpa using this
      filter_upwards [D.eventually_mem, hψ1] with u hu hψu
      simp only [characterVector]
      rw [Set.indicator_of_mem (show z + u ∈ (D.subgroup : Set W) from
        D.subgroup.add_mem hz hu.1), Set.indicator_of_mem (show z ∈ (D.subgroup : Set W) from hz)]
      have h1 := D.character_mul z hz u hu.1
      rw [hu.2, mul_one] at h1
      rw [h1, ← hB.neg_eq u z, mul_neg, AddChar.map_neg_eq_inv, hψu, inv_one, one_mul]
    · have hcl : IsOpen (D.subgroup : Set W)ᶜ :=
        (AddSubgroup.isClosed_of_isOpen _ hA).isOpen_compl
      filter_upwards [hcl.mem_nhds hz] with y hy
      simp only [characterVector, Set.indicator_of_notMem hy, Set.indicator_of_notMem hz]
  · simp only [toInducingDatum_subgroup, add_zero, Set.add_singleton, Set.image_id']
    by_contra h
    exact hw (Set.indicator_of_notMem h _)

/-- **The induced model of an open self-dual subgroup lies in the induced model of the
closed datum**: the span of the translates of `ψ_A · 1_A` is contained in the space of
`InducingDatum.inducedSpace`. -/
theorem inducedModel_le_inducedSubmodule {F : Type u} [Field F] [Invertible (2 : F)]
    [TopologicalSpace F] [IsTopologicalRing F] {W : Type v} [AddCommGroup W] [Module F W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] {B : LinearMap.BilinForm F W}
    {ψ : AddChar F ℂ} (hB : B.IsAlt) (hψ : IsLocallyConstant ψ)
    (hBc : ∀ v, Continuous fun z => B z v) (D : SelfDualDatum B ψ) :
    (inducedModel D).toSubmodule ≤ (D.toInducingDatum hB).inducedSubmodule := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, rfl⟩
  exact ((D.toInducingDatum hB).inducedSpace hB hψ hBc).apply_mem_toSubmodule (ofVec x)
    (D.characterVector_mem_inducedSubmodule hB hψ hBc)

end SelfDualDatum

end Closed

end Langlands.HeisenbergGroup

/-! ### Deprecated aliases -/

namespace Langlands.HeisenbergGroup

@[deprecated SelfDualDatum (since := "2026-11-23")]
alias PolarizingDatum := SelfDualDatum

@[deprecated SelfDualDatum.charOrthogonal_le (since := "2026-11-23")]
alias PolarizingDatum.charOrthogonal_le := SelfDualDatum.charOrthogonal_le

@[deprecated SelfDualDatum.eventually_mem (since := "2026-11-23")]
alias PolarizingDatum.eventually_mem := SelfDualDatum.eventually_mem

@[deprecated SelfDualDatum.exists_eigenvector_mem (since := "2026-11-23")]
alias PolarizingDatum.exists_eigenvector_mem := SelfDualDatum.exists_eigenvector_mem

@[deprecated SelfDualDatum.exists_finite (since := "2026-11-23")]
alias PolarizingDatum.exists_finite := SelfDualDatum.exists_finite

@[deprecated SelfDualDatum.isIrreducible_of_span_eq_top (since := "2026-11-23")]
alias PolarizingDatum.isIrreducible_of_span_eq_top := SelfDualDatum.isIrreducible_of_span_eq_top

@[deprecated SelfDualDatum.isIrreducible_translatesSpan (since := "2026-11-23")]
alias PolarizingDatum.isIrreducible_translatesSpan := SelfDualDatum.isIrreducible_translatesSpan

@[deprecated SelfDualDatum.isSmooth_of_span_eq_top (since := "2026-11-23")]
alias PolarizingDatum.isSmooth_of_span_eq_top := SelfDualDatum.isSmooth_of_span_eq_top

@[deprecated SelfDualDatum.isSmooth_translatesSpan (since := "2026-11-23")]
alias PolarizingDatum.isSmooth_translatesSpan := SelfDualDatum.isSmooth_translatesSpan

@[deprecated SelfDualDatum.characterVector (since := "2026-11-23")]
alias PolarizingDatum.latticeVector := SelfDualDatum.characterVector

@[deprecated SelfDualDatum.characterVector_ne_zero (since := "2026-11-23")]
alias PolarizingDatum.latticeVector_ne_zero := SelfDualDatum.characterVector_ne_zero

@[deprecated SelfDualDatum.mk (since := "2026-11-23")]
alias PolarizingDatum.mk := SelfDualDatum.mk

@[deprecated SelfDualDatum.regularFun_characterVector (since := "2026-11-23")]
alias PolarizingDatum.regularFun_latticeVector := SelfDualDatum.regularFun_characterVector

@[deprecated SelfDualDatum.splitsOn (since := "2026-11-23")]
alias PolarizingDatum.splitsOn := SelfDualDatum.splitsOn

@[deprecated SelfDualDatum.character (since := "2026-11-23")]
alias PolarizingDatum.splitting := SelfDualDatum.character

@[deprecated SelfDualDatum.character_mul (since := "2026-11-23")]
alias PolarizingDatum.splitting_mul := SelfDualDatum.character_mul

@[deprecated SelfDualDatum.character_ne_zero (since := "2026-11-23")]
alias PolarizingDatum.splitting_ne_zero := SelfDualDatum.character_ne_zero

@[deprecated SelfDualDatum.subgroup (since := "2026-11-23")]
alias PolarizingDatum.subgroup := SelfDualDatum.subgroup

@[deprecated hasCentralCharacter_inducedModel (since := "2026-11-23")]
alias hasCentralCharacter_latticeModel := hasCentralCharacter_inducedModel

@[deprecated isIrreducible_inducedModel (since := "2026-11-23")]
alias isIrreducible_latticeModel := isIrreducible_inducedModel

@[deprecated isSmooth_inducedModel (since := "2026-11-23")]
alias isSmooth_latticeModel := isSmooth_inducedModel

@[deprecated inducedModel (since := "2026-11-23")]
alias latticeModel := inducedModel

@[deprecated characterVector_mem_inducedModel (since := "2026-11-23")]
alias latticeVector_mem_latticeModel := characterVector_mem_inducedModel

@[deprecated nonempty_selfDualDatum (since := "2026-11-23")]
alias nonempty_polarizingDatum := nonempty_selfDualDatum

end Langlands.HeisenbergGroup
