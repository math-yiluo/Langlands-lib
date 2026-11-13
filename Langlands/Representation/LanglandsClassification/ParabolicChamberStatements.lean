import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Langlands.GroupScheme.Rational.LanglandsDecompositionCones
import Langlands.GroupScheme.Rational.RestrictedSimpleRootCones
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsStatement
import Langlands.Representation.LanglandsClassification.SimpleCorootFaces
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-! # Renard V.3.14–V.3.16: `Δ̂(P)`, `Δ^∨(P)`, `β̌`, the chambers and their cell decompositions

For a maximal split torus `T`, a generic cocharacter `ν` (a minimal parabolic `P_∅`), integral
reflection data `D` and a set `J` of simple roots (a standard parabolic `P = MN`), this file
gives the objects of Renard V.3.14–V.3.16 in two settings:

* inside `𝔞*_∅ = Vstar T` and `𝔞_∅ = V T`, where `𝔞*_M` is the coroot annihilator of `J` and
  `𝔞_M` is the root annihilator of `J` (V.3.13);
* on the split component `A` of `M`, with factor `f : A ⟶ T`, so that `𝔞*_M = Vstar A` and
  `𝔞_M = V A`.

The cell decompositions of V.3.16 are proved here. The remaining assertions of V.3.14–V.3.16
are the two statement targets at the end of the file.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped Pointwise

namespace Langlands.GroupScheme

open RealTorusSpace

/-! ### A combinatorial cell decomposition -/

section Cells

variable {ι κ E : Type*} (e : ι → κ) (q : ι → E → ℝ) (Z : Set E) (Δ : Set κ)

/-- The open cell with index `K`: points of `Z` where `q a` vanishes when `e a ∈ K` and is
positive when `e a ∈ Δ ∖ K`. -/
private def openCell (K : Set κ) : Set E :=
  {y | y ∈ Z ∧ (∀ a, e a ∈ K → q a y = 0) ∧ ∀ a, e a ∈ Δ → e a ∉ K → 0 < q a y}

/-- The closed cell with index `J`: the same with `q a ≥ 0` when `e a ∈ Δ ∖ J`. -/
private def closedCell (J : Set κ) : Set E :=
  {y | y ∈ Z ∧ (∀ a, e a ∈ J → q a y = 0) ∧ ∀ a, e a ∈ Δ → e a ∉ J → 0 ≤ q a y}

private theorem closedCell_eq_iUnion (he : Function.Injective e) {J : Set κ} (hJ : J ⊆ Δ) :
    closedCell e q Z Δ J = ⋃ (K : Set κ) (_ : J ⊆ K ∧ K ⊆ Δ), openCell e q Z Δ K := by
  ext y
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hZ, hzero, hnonneg⟩
    refine ⟨J ∪ {χ | χ ∈ Δ ∧ ∀ a, e a = χ → q a y = 0}, ⟨Set.subset_union_left, ?_⟩,
      hZ, ?_, ?_⟩
    · exact Set.union_subset hJ fun χ hχ => hχ.1
    · rintro a (ha | ha)
      · exact hzero a ha
      · exact ha.2 a rfl
    · intro a haΔ haK
      have haJ : e a ∉ J := fun h => haK (Or.inl h)
      refine lt_of_le_of_ne (hnonneg a haΔ haJ) ?_
      intro h0
      refine haK (Or.inr ⟨haΔ, fun b hb => ?_⟩)
      rw [he hb]
      exact h0.symm
  · rintro ⟨K, ⟨hJK, -⟩, hZ, hzero, hpos⟩
    refine ⟨hZ, fun a ha => hzero a (hJK ha), fun a haΔ _ => ?_⟩
    by_cases haK : e a ∈ K
    · exact (hzero a haK).ge
    · exact (hpos a haΔ haK).le

private theorem pairwiseDisjoint_openCell (hΔ : Δ ⊆ Set.range e) :
    Set.PairwiseDisjoint {K : Set κ | K ⊆ Δ} (openCell e q Z Δ) := by
  have key : ∀ {K K' : Set κ}, K ⊆ Δ → ∀ y, y ∈ openCell e q Z Δ K →
      y ∈ openCell e q Z Δ K' → K ⊆ K' := by
    intro K K' hK y hy hy' χ hχ
    by_contra hχ'
    obtain ⟨a, rfl⟩ := hΔ (hK hχ)
    exact (hy'.2.2 a (hK hχ) hχ').ne' (hy.2.1 a hχ)
  intro K hK K' hK' hne
  refine Set.disjoint_left.mpr fun y hy hy' => hne ?_
  exact le_antisymm (key hK y hy hy') (key hK' y hy' hy)

end Cells

section Definitions

variable {k : Type u} [Field k] {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (D : RelativeRootReflectionData i)

/-! ### V.3.14 inside `𝔞*_∅` and `𝔞_∅` -/

/-- Renard V.3.14, `Δ(P)` realized in `𝔞*_M ⊂ 𝔞*_∅`: the projections to
`𝔞*_M = corootAnnihilator i D J`, along the real span of `J`, of the simple roots outside `J`. -/
def parabolicRoots (J : Set (characterLattice T)) : Set (Vstar T) :=
  D.projectedRoots J (simpleRelativeRoots i ν \ J)

/-- Renard V.3.14, `Δ^∨(P)` realized in `𝔞_M ⊂ 𝔞_∅`: the projections `β̌` to
`𝔞_M = rootAnnihilator T J`, along the span of the coroots of `J`, of the coroots `α̌` of the
simple roots `α` outside `J`. -/
def parabolicCoroots (J : Set (characterLattice T)) : Set (V T) :=
  D.projectedCoroots J (simpleRelativeRoots i ν \ J)

/-- Renard V.3.14, `Δ̂(P)` realized in `𝔞*_∅`: the fundamental weights `ϖ_α` of the simple
roots `α` outside `J`. They lie in `𝔞*_M` (`parabolicFundamentalWeights_subset`), so each is
its own projection to `𝔞*_M`, the realization there of `ϖ_α|_{𝔞_M}`. -/
def parabolicFundamentalWeights (J : Set (characterLattice T)) : Set (Vstar T) :=
  {x | ∃ α : simpleRelativeRoots i ν, α.1 ∉ J ∧ D.IsRealFundamentalWeight ν α x}

/-- Renard V.3.14, `Δ̂^∨(P)` realized in `𝔞_∅`: the fundamental coweights `ϖ^∨_α` of the simple
roots `α` outside `J`. They lie in `𝔞_M` (`parabolicFundamentalCoweights_subset`). -/
def parabolicFundamentalCoweights (J : Set (characterLattice T)) : Set (V T) :=
  {v | ∃ α : simpleRelativeRoots i ν, α.1 ∉ J ∧ IsRealFundamentalCoweight i ν α v}

/-- Renard V.3.14, the assignment `β ↦ β̌` realized in `𝔞*_∅ × 𝔞_∅`: `y` is the projection to
`𝔞*_M` of a simple root `α ∉ J` and `v` is the projection to `𝔞_M` of its coroot `α̌`. -/
def IsParabolicCorootOf (J : Set (characterLattice T)) (y : Vstar T) (v : V T) : Prop :=
  ∃ α ∈ simpleRelativeRoots i ν \ J, y ∈ D.projectedRoots J {α} ∧ v ∈ D.projectedCoroots J {α}

/-! ### V.3.15–V.3.16 inside `𝔞*_∅` and `𝔞_∅` -/

/-- Renard V.3.15, the closure of `^G_P[𝔞*_M]^+` realized in `𝔞*_∅`: the vectors with
`⟨y, α̌⟩ = 0` for every root `α ∈ J` and `⟨y, α̌⟩ ≥ 0` for every simple root `α ∉ J`. The open
chamber is the published `openSimpleCorootFace i ν D J`. -/
def closedSimpleCorootFace (J : Set (characterLattice T)) : Set (Vstar T) :=
  {x | (∀ α : relativeRoots i, α.val ∈ J → pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0) ∧
    ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν → α.val ∉ J →
      0 ≤ pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)}

/-- Renard V.3.15, `⁺[𝔞*_M]^G_P` realized in `𝔞*_M ⊂ 𝔞*_∅` for `S = Δ_∅ ∖ J`: the vectors of
`𝔞*_M` congruent, modulo the real span of `J`, to a combination of all the roots of the finite
set `S` with strictly positive coefficients. The nonnegative version is the published
`projectedRootNonnegCone i D J S`. -/
def projectedRootPositiveCone (J S : Set (characterLattice T)) : Set (Vstar T) :=
  {y | y ∈ corootAnnihilator i D J ∧ ∃ (s : Finset (characterLattice T))
      (c : characterLattice T → ℝ), (s : Set (characterLattice T)) = S ∧
      (∀ α ∈ s, 0 < c α) ∧
      y - ∑ α ∈ s, c α • ((1 : ℝ) ⊗ₜ[ℤ] α) ∈
        Submodule.span ℝ ((fun β : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] β) '' J)}

/-- Renard V.3.15, `⁺[𝔞_M]^G_P` realized in `𝔞_M ⊂ 𝔞_∅` for `S = Δ_∅ ∖ J`: the vectors of
`𝔞_M` congruent, modulo the span of the coroots of `J`, to a combination of the coroots of all
the roots of the finite set `S` with strictly positive coefficients. -/
def projectedCorootPositiveCone (J S : Set (characterLattice T)) : Set (V T) :=
  {v | v ∈ rootAnnihilator T J ∧ ∃ (s : Finset (relativeRoots i)) (c : relativeRoots i → ℝ),
      (∀ α : relativeRoots i, α ∈ s ↔ α.1 ∈ S) ∧ (∀ α ∈ s, 0 < c α) ∧
      ∑ α ∈ s, c α • D.realCoroot α - v ∈ Submodule.span ℝ (D.realCorootsOf J)}

/-- Renard V.3.15, the closure of `⁺[𝔞_M]^G_P` realized in `𝔞_M ⊂ 𝔞_∅` for `S = Δ_∅ ∖ J`: the
vectors of `𝔞_M` congruent, modulo the span of the coroots of `J`, to a nonnegative combination
of coroots of roots in `S`. -/
def projectedCorootNonnegCone (J S : Set (characterLattice T)) : Set (V T) :=
  {v | v ∈ rootAnnihilator T J ∧ ∃ w ∈ PointedCone.hull ℝ (D.realCorootsOf S),
      w - v ∈ Submodule.span ℝ (D.realCorootsOf J)}

/-- Renard V.3.16, `^G_P[(𝔞^G_M)*]^+` as a convex cone of `𝔞*_∅`: the published open coroot face
`openCorootFace i ν D J`. -/
def openCorootFaceCone (J : Set (characterLattice T)) : ConvexCone ℝ (Vstar T) where
  carrier := openCorootFace i ν D J
  smul_mem' := by
    rintro c hc y ⟨hy, hzero, hpos⟩
    refine ⟨Submodule.smul_mem _ c hy, fun α hα => ?_, fun α hα hαJ => ?_⟩
    · rw [map_smul, LinearMap.smul_apply, hzero α hα, smul_zero]
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact mul_pos hc (hpos α hα hαJ)
  add_mem' := by
    rintro x ⟨hx, hxz, hxp⟩ y ⟨hy, hyz, hyp⟩
    refine ⟨Submodule.add_mem _ hx hy, fun α hα => ?_, fun α hα hαJ => ?_⟩
    · rw [map_add, LinearMap.add_apply, hxz α hα, hyz α hα, add_zero]
    · rw [map_add, LinearMap.add_apply]
      exact add_pos (hxp α hα hαJ) (hyp α hα hαJ)

/-- Renard V.3.16, the closure of `^G_P[(𝔞^G_M)*]^+` as a closed-type (pointed) convex cone of
`𝔞*_∅`: the published closed coroot face `closedCorootFace i ν D J`. -/
def closedCorootFaceCone (J : Set (characterLattice T)) : PointedCone ℝ (Vstar T) where
  carrier := closedCorootFace i ν D J
  zero_mem' := ⟨Submodule.zero_mem _, fun α _ => by simp, fun α _ _ => by simp⟩
  add_mem' := by
    rintro x y ⟨hx, hxz, hxp⟩ ⟨hy, hyz, hyp⟩
    refine ⟨Submodule.add_mem _ hx hy, fun α hα => ?_, fun α hα hαJ => ?_⟩
    · rw [map_add, LinearMap.add_apply, hxz α hα, hyz α hα, add_zero]
    · rw [map_add, LinearMap.add_apply]
      exact add_nonneg (hxp α hα hαJ) (hyp α hα hαJ)
  smul_mem' := by
    rintro ⟨c, hc⟩ y ⟨hy, hzero, hpos⟩
    have hsmul : (⟨c, hc⟩ : {c : ℝ // 0 ≤ c}) • y = c • y := rfl
    rw [hsmul]
    refine ⟨Submodule.smul_mem _ c hy, fun α hα => ?_, fun α hα hαJ => ?_⟩
    · rw [map_smul, LinearMap.smul_apply, hzero α hα, smul_zero]
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact mul_nonneg hc (hpos α hα hαJ)

/-! ### V.3.14–V.3.15 on the split component `A`, `f : A ⟶ T` -/

/-- Renard V.3.14, `Δ̂(P) = {ϖ_α|_{𝔞_M} | α ∈ Δ_∅ ∖ Δ^M_∅}` in `𝔞*_M = Vstar A`: the
restrictions along `f` of the fundamental weights of the simple roots outside `J`. -/
def restrictedFundamentalWeights (J : Set (characterLattice T)) (f : A ⟶ T) : Set (Vstar A) :=
  rationalCharacterRestrictReal (CommGroupScheme.groupHom f) '' parabolicFundamentalWeights i ν D J

/-- Renard V.3.14, `Δ^∨(P)` in `𝔞_M = V A`: the real cocharacters of `A` whose image in `𝔞_∅`
is the projection to `𝔞_M` of the coroot of a simple root outside `J`. -/
def restrictedParabolicCoroots (J : Set (characterLattice T)) (f : A ⟶ T) : Set (V A) :=
  cocharacterMapReal f ⁻¹' parabolicCoroots i ν D J

/-- Renard V.3.14, `Δ̂^∨(P)` in `𝔞_M = V A`: the real cocharacters of `A` whose image in `𝔞_∅`
is the fundamental coweight of a simple root outside `J`. -/
def restrictedFundamentalCoweights (J : Set (characterLattice T)) (f : A ⟶ T) : Set (V A) :=
  cocharacterMapReal f ⁻¹' parabolicFundamentalCoweights i ν J

/-- Renard V.3.14, `β̌` for `β ∈ Δ(P)` in `𝔞_M = V A`: `β = α|_{𝔞_M}` for a simple root
`α ∉ J`, and the image of `v` in `𝔞_∅` is the projection to `𝔞_M` of the coroot `α̌`. -/
def IsRestrictedParabolicCoroot (J : Set (characterLattice T)) (f : A ⟶ T) (β : Vstar A)
    (v : V A) : Prop :=
  ∃ α ∈ simpleRelativeRoots i ν \ J, restrictedRootVector f α = β ∧
    cocharacterMapReal f v ∈ D.projectedCoroots J {α}

/-- Renard V.3.15 as printed, `^G_P[𝔞*]^+ = {χ ∈ 𝔞* | ⟨χ, β̌⟩ > 0, β ∈ Δ(P)}` in
`𝔞*_M = Vstar A`. The published `restrictedCorootChamber` is defined instead by lifting to
`𝔞*_∅`. -/
def parabolicCorootChamber (J : Set (characterLattice T)) (f : A ⟶ T) : Set (Vstar A) :=
  {x | ∀ β v, IsRestrictedParabolicCoroot i ν D J f β v → 0 < pair A x v}

/-- Renard V.3.15 as printed, the closure `{χ ∈ 𝔞* | ⟨χ, β̌⟩ ≥ 0, β ∈ Δ(P)}` in `Vstar A`. -/
def parabolicClosedCorootChamber (J : Set (characterLattice T)) (f : A ⟶ T) : Set (Vstar A) :=
  {x | ∀ β v, IsRestrictedParabolicCoroot i ν D J f β v → 0 ≤ pair A x v}

/-- Renard V.3.15, `⁺[𝔞]^G_P` in `𝔞_M = V A`: the real cocharacters of `A` whose image in `𝔞_∅`
lies in the realization `projectedCorootPositiveCone i D J (Δ_∅ ∖ J)` of `⁺[𝔞_M]^G_P`. -/
def restrictedCorootPositiveCone (J : Set (characterLattice T)) (f : A ⟶ T) : Set (V A) :=
  cocharacterMapReal f ⁻¹' projectedCorootPositiveCone i D J (simpleRelativeRoots i ν \ J)

/-- Renard V.3.15, the closure of `⁺[𝔞]^G_P` in `𝔞_M = V A`, through
`projectedCorootNonnegCone i D J (Δ_∅ ∖ J)`. -/
def restrictedCorootNonnegCone (J : Set (characterLattice T)) (f : A ⟶ T) : Set (V A) :=
  cocharacterMapReal f ⁻¹' projectedCorootNonnegCone i D J (simpleRelativeRoots i ν \ J)

/-! ### Proved facts -/

variable {i ν D}

/-- The fundamental weights of simple roots outside `J` lie in `(𝔞^G_M)* = 𝔞*_M ∩ (𝔞^G_∅)*`. -/
theorem parabolicFundamentalWeights_subset {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    parabolicFundamentalWeights i ν D J ⊆
      (corootAnnihilator i D J ⊓ relativeRootSpanReal i : Submodule ℝ (Vstar T)) := by
  rintro x ⟨α, hαJ, hspan, -, hother⟩
  refine ⟨(mem_corootAnnihilator i D J x).mpr fun β hβ => ?_, hspan⟩
  have hne : (⟨β.1, hJ hβ⟩ : simpleRelativeRoots i ν) ≠ α := by
    intro h
    exact hαJ (h ▸ hβ)
  have h := hother _ hne
  have hβ' : simpleToRelativeRoot i ν ⟨β.1, hJ hβ⟩ = β := Subtype.ext rfl
  rwa [hβ'] at h

omit [Mono i.hom.hom.left] in
/-- The fundamental coweights of simple roots outside `J` lie in `𝔞^G_M = 𝔞_M ∩ 𝔞^G_∅`. -/
theorem parabolicFundamentalCoweights_subset {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    parabolicFundamentalCoweights i ν J ⊆
      (rootAnnihilator T J ⊓
        cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i)) :
        Submodule ℝ (V T)) := by
  intro v hv
  obtain ⟨α, hαJ, hann, -, hother⟩ := hv
  rw [SetLike.mem_coe, Submodule.mem_inf]
  refine ⟨?_, hann⟩
  rw [mem_rootAnnihilator]
  intro β hβ
  have hne : (⟨β, hJ hβ⟩ : simpleRelativeRoots i ν) ≠ α := by
    intro h
    apply hαJ
    rw [← h]
    exact hβ
  exact hother ⟨β, hJ hβ⟩ hne

/-- On `𝔞*_M`, pairing with the projection `β̌` of a coroot `α̌` is pairing with `α̌`. -/
theorem pair_eq_of_mem_projectedCoroots {J : Set (characterLattice T)} {y : Vstar T}
    (hy : y ∈ corootAnnihilator i D J) (α : relativeRoots i) {v : V T}
    (hv : v ∈ D.projectedCoroots J {α.1}) :
    pair T y v = pair T y (D.realCoroot α) := by
  obtain ⟨-, w, ⟨α', hα', rfl⟩, hw⟩ := hv
  have hα'' : α' = α := Subtype.ext hα'
  subst hα''
  have hle : Submodule.span ℝ (D.realCorootsOf J) ≤ LinearMap.ker (pair T y) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨β, hβ, rfl⟩
    exact (mem_corootAnnihilator i D J y).mp hy β hβ
  have h0 := hle hw
  rw [LinearMap.mem_ker, map_sub] at h0
  linarith

/-- On `𝔞_M`, pairing with the projection `β` of a root `α` to `𝔞*_M` is evaluating `α`. -/
theorem pair_eq_of_mem_projectedRoots {J : Set (characterLattice T)} {v : V T}
    (hv : v ∈ rootAnnihilator T J) (α : characterLattice T) {y : Vstar T}
    (hy : y ∈ D.projectedRoots J {α}) :
    pair T y v = eval T α v := by
  obtain ⟨-, α', hα', hdiff⟩ := hy
  rw [Set.mem_singleton_iff] at hα'
  subst hα'
  have hle : Submodule.span ℝ ((fun β : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] β) '' J) ≤
      LinearMap.ker ((pair T).flip v) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨β, hβ, rfl⟩
    change pair T ((1 : ℝ) ⊗ₜ[ℤ] β) v = 0
    rw [← eval_eq_pair]
    exact (mem_rootAnnihilator J v).mp hv β hβ
  have h0 := hle hdiff
  rw [LinearMap.mem_ker, map_sub, LinearMap.flip_apply, LinearMap.flip_apply] at h0
  rw [eval_eq_pair]
  linarith

/-- A point of `^G_P[𝔞*_M]^+` is positive on every `β̌`, `β ∈ Δ(P)` (realized in `𝔞*_∅`). -/
theorem pair_pos_of_mem_openSimpleCorootFace {J : Set (characterLattice T)} {x : Vstar T}
    (hx : x ∈ openSimpleCorootFace i ν D J) {y : Vstar T} {v : V T}
    (hyv : IsParabolicCorootOf i ν D J y v) : 0 < pair T x v := by
  obtain ⟨α, ⟨hαs, hαJ⟩, -, hv⟩ := hyv
  have hαR : α ∈ relativeRoots i := simpleRelativeRoots_subset_relativeRoots i ν hαs
  have hxJ : x ∈ corootAnnihilator i D J :=
    (mem_corootAnnihilator i D J x).mpr fun β hβ => hx.1 β hβ
  rw [pair_eq_of_mem_projectedCoroots hxJ ⟨α, hαR⟩ hv]
  exact hx.2 ⟨α, hαR⟩ hαs hαJ

/-- Every point of the open coroot face of `J` lies in `(𝔞^G_M)* = 𝔞*_M ∩ (𝔞^G_∅)*`. -/
theorem openCorootFace_subset {J : Set (characterLattice T)} :
    openCorootFace i ν D J ⊆
      (corootAnnihilator i D J ⊓ relativeRootSpanReal i : Submodule ℝ (Vstar T)) :=
  fun _ hy => ⟨(mem_corootAnnihilator i D J _).mpr hy.2.1, hy.1⟩

/-- Every point of the closed coroot face of `J` lies in `(𝔞^G_M)*`. -/
theorem closedCorootFace_subset {J : Set (characterLattice T)} :
    closedCorootFace i ν D J ⊆
      (corootAnnihilator i D J ⊓ relativeRootSpanReal i : Submodule ℝ (Vstar T)) :=
  fun _ hy => ⟨(mem_corootAnnihilator i D J _).mpr hy.2.1, hy.1⟩

/-- Renard V.3.16, first display: `^G_P[(𝔞^G_M)*]^+ = ^G_P[𝔞*_M]^+ ∩ (𝔞^G_∅)*`, realized in
`𝔞*_∅` (the face already lies in `𝔞*_M`). -/
theorem openCorootFace_eq_inter (J : Set (characterLattice T)) :
    openCorootFace i ν D J = openSimpleCorootFace i ν D J ∩ relativeRootSpanReal i := by
  ext y
  simp only [openCorootFace, openSimpleCorootFace, Set.mem_inter_iff, Set.mem_ofPred_eq,
    SetLike.mem_coe]
  tauto

/-- Renard V.3.16, second display: the closure of `^G_P[(𝔞^G_M)*]^+` is the closure of
`^G_P[𝔞*_M]^+` intersected with `(𝔞^G_∅)*`, realized in `𝔞*_∅`. -/
theorem closedCorootFace_eq_inter (J : Set (characterLattice T)) :
    closedCorootFace i ν D J = closedSimpleCorootFace i ν D J ∩ relativeRootSpanReal i := by
  ext y
  simp only [closedCorootFace, closedSimpleCorootFace, Set.mem_inter_iff, Set.mem_ofPred_eq,
    SetLike.mem_coe]
  tauto

theorem openSimpleCorootFace_subset_closed (J : Set (characterLattice T)) :
    openSimpleCorootFace i ν D J ⊆ closedSimpleCorootFace i ν D J :=
  fun _ hy => ⟨hy.1, fun α hα hαJ => (hy.2 α hα hαJ).le⟩

theorem openCorootFace_subset_closed (J : Set (characterLattice T)) :
    openCorootFace i ν D J ⊆ closedCorootFace i ν D J :=
  fun _ hy => ⟨hy.1, hy.2.1, fun α hα hαJ => (hy.2.2 α hα hαJ).le⟩

theorem convex_openCorootFace (J : Set (characterLattice T)) :
    Convex ℝ (openCorootFace i ν D J) :=
  (openCorootFaceCone i ν D J).convex

theorem convex_closedCorootFace (J : Set (characterLattice T)) :
    Convex ℝ (closedCorootFace i ν D J) :=
  (closedCorootFaceCone i ν D J).convex

private theorem openCorootFace_eq_openCell (K : Set (characterLattice T)) :
    openCorootFace i ν D K =
      openCell Subtype.val (fun (α : relativeRoots i) (y : Vstar T) =>
        pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) (relativeRootSpanReal i : Set (Vstar T))
        (simpleRelativeRoots i ν) K := by
  ext y
  simp only [openCorootFace, openCell, Set.mem_ofPred_eq, SetLike.mem_coe]

private theorem closedCorootFace_eq_closedCell (J : Set (characterLattice T)) :
    closedCorootFace i ν D J =
      closedCell Subtype.val (fun (α : relativeRoots i) (y : Vstar T) =>
        pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) (relativeRootSpanReal i : Set (Vstar T))
        (simpleRelativeRoots i ν) J := by
  ext y
  simp only [closedCorootFace, closedCell, Set.mem_ofPred_eq, SetLike.mem_coe]

private theorem openSimpleCorootFace_eq_openCell (K : Set (characterLattice T)) :
    openSimpleCorootFace i ν D K =
      openCell Subtype.val (fun (α : relativeRoots i) (y : Vstar T) =>
        pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) Set.univ (simpleRelativeRoots i ν) K := by
  ext y
  simp only [openSimpleCorootFace, openCell, Set.mem_ofPred_eq, Set.mem_univ, true_and]

private theorem closedSimpleCorootFace_eq_closedCell (J : Set (characterLattice T)) :
    closedSimpleCorootFace i ν D J =
      closedCell Subtype.val (fun (α : relativeRoots i) (y : Vstar T) =>
        pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) Set.univ (simpleRelativeRoots i ν) J := by
  ext y
  simp only [closedSimpleCorootFace, closedCell, Set.mem_ofPred_eq, Set.mem_univ, true_and]

omit [Mono i.hom.hom.left] in
private theorem simple_subset_range_val :
    simpleRelativeRoots i ν ⊆ Set.range (Subtype.val : relativeRoots i → characterLattice T) :=
  fun χ hχ => ⟨⟨χ, simpleRelativeRoots_subset_relativeRoots i ν hχ⟩, rfl⟩

/-- Renard V.3.16, the cell decomposition of the closure of `^G_P[(𝔞^G_M)*]^+` into the cones
`^G_Q[(𝔞^G_L)*]^+` of the standard parabolic subgroups `Q = LU ⊇ P`, indexed by their
simple-root sets `K` with `J ⊆ K ⊆ Δ_∅`, realized in `𝔞*_∅`. -/
theorem closedCorootFace_eq_iUnion {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    closedCorootFace i ν D J =
      ⋃ (K : Set (characterLattice T)) (_ : J ⊆ K ∧ K ⊆ simpleRelativeRoots i ν),
        openCorootFace i ν D K := by
  rw [closedCorootFace_eq_closedCell, closedCell_eq_iUnion _ _ _ _ Subtype.val_injective hJ]
  simp only [openCorootFace_eq_openCell]

/-- The cones `^G_Q[(𝔞^G_L)*]^+` of distinct standard parabolic subgroups are disjoint. -/
theorem pairwiseDisjoint_openCorootFace :
    Set.PairwiseDisjoint {K : Set (characterLattice T) | K ⊆ simpleRelativeRoots i ν}
      (openCorootFace i ν D) := by
  have h := pairwiseDisjoint_openCell (Subtype.val : relativeRoots i → characterLattice T)
    (fun (α : relativeRoots i) (y : Vstar T) => pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (relativeRootSpanReal i : Set (Vstar T)) (simpleRelativeRoots i ν) simple_subset_range_val
  have he : openCorootFace i ν D = openCell Subtype.val
      (fun (α : relativeRoots i) (y : Vstar T) => pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
      (relativeRootSpanReal i : Set (Vstar T)) (simpleRelativeRoots i ν) :=
    funext openCorootFace_eq_openCell
  rw [he]
  exact h

/-- Renard V.3.16, the decomposition of the closure of `^G_P[𝔞*_M]^+` into the chambers
`^G_Q[𝔞*_L]^+` of the standard parabolic subgroups `Q = LU ⊇ P`, realized in `𝔞*_∅`. -/
theorem closedSimpleCorootFace_eq_iUnion {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    closedSimpleCorootFace i ν D J =
      ⋃ (K : Set (characterLattice T)) (_ : J ⊆ K ∧ K ⊆ simpleRelativeRoots i ν),
        openSimpleCorootFace i ν D K := by
  rw [closedSimpleCorootFace_eq_closedCell,
    closedCell_eq_iUnion _ _ _ _ Subtype.val_injective hJ]
  simp only [openSimpleCorootFace_eq_openCell]

/-- The chambers `^G_Q[𝔞*_L]^+` of distinct standard parabolic subgroups are disjoint. -/
theorem pairwiseDisjoint_openSimpleCorootFace :
    Set.PairwiseDisjoint {K : Set (characterLattice T) | K ⊆ simpleRelativeRoots i ν}
      (openSimpleCorootFace i ν D) := by
  have h := pairwiseDisjoint_openCell (Subtype.val : relativeRoots i → characterLattice T)
    (fun (α : relativeRoots i) (y : Vstar T) => pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    Set.univ (simpleRelativeRoots i ν) simple_subset_range_val
  have he : openSimpleCorootFace i ν D = openCell Subtype.val
      (fun (α : relativeRoots i) (y : Vstar T) => pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
      Set.univ (simpleRelativeRoots i ν) :=
    funext openSimpleCorootFace_eq_openCell
  rw [he]
  exact h

/-! ### Duality on the split component -/

/-- The vectors of `Δ^∨(P)` in `V A` are exactly the vectors `β̌` related to some `β`. -/
theorem mem_restrictedParabolicCoroots {J : Set (characterLattice T)} {f : A ⟶ T} {v : V A} :
    v ∈ restrictedParabolicCoroots i ν D J f ↔
      ∃ β, IsRestrictedParabolicCoroot i ν D J f β v := by
  constructor
  · rintro ⟨hann, _, ⟨α, hα, rfl⟩, hw⟩
    exact ⟨_, α.1, hα, rfl, hann, _, ⟨α, Set.mem_singleton _, rfl⟩, hw⟩
  · rintro ⟨β, α, hα, -, hann, _, ⟨α', hα', rfl⟩, hw⟩
    have h : α'.1 = α := Set.mem_singleton_iff.mp hα'
    refine ⟨hann, _, ⟨α', ?_, rfl⟩, hw⟩
    show α'.1 ∈ simpleRelativeRoots i ν \ J
    rw [h]
    exact hα

omit [Mono i.hom.hom.left] in
/-- On `𝔞_M = V A`, the restricted simple roots are dual to the fundamental coweights: if the
image of `w` in `𝔞_∅` is `ϖ^∨_α`, then `⟨α'|_{𝔞_M}, w⟩` is `1` for `α' = α` and `0` for the
other simple roots `α'`. -/
theorem pair_restrictedRootVector_of_isRealFundamentalCoweight {f : A ⟶ T}
    {α : simpleRelativeRoots i ν} {w : V A}
    (hw : IsRealFundamentalCoweight i ν α (cocharacterMapReal f w))
    (α' : simpleRelativeRoots i ν) :
    (α' = α → pair A (restrictedRootVector f α'.1) w = 1) ∧
      (α' ≠ α → pair A (restrictedRootVector f α'.1) w = 0) := by
  rw [pair_restrictedRootVector]
  refine ⟨fun h => ?_, fun h => hw.2.2 α' h⟩
  subst h
  exact hw.2.1

/-- On `𝔞_M = V A`, `Δ̂(P)` is dual to `Δ^∨(P)`: if `x = ϖ_α` for a simple root `α ∉ J` and the
image of `v` in `𝔞_∅` is the projection `β̌` of the coroot of a simple root `α'`, then
`⟨ϖ_α|_{𝔞_M}, v⟩` is `1` for `α' = α` and `0` otherwise. -/
theorem pair_restrict_of_isRealFundamentalWeight {J : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) {α : simpleRelativeRoots i ν} (hαJ : α.1 ∉ J)
    {x : Vstar T} (hx : D.IsRealFundamentalWeight ν α x) {f : A ⟶ T}
    (α' : simpleRelativeRoots i ν) {v : V A}
    (hv : cocharacterMapReal f v ∈ D.projectedCoroots J {α'.1}) :
    (α' = α → pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x) v = 1) ∧
      (α' ≠ α → pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x) v = 0) := by
  have hmem := parabolicFundamentalWeights_subset (D := D) hJ ⟨α, hαJ, hx⟩
  rw [SetLike.mem_coe, Submodule.mem_inf] at hmem
  rw [← pair_cocharacterMapReal,
    pair_eq_of_mem_projectedCoroots hmem.1 (simpleToRelativeRoot i ν α') hv]
  refine ⟨fun h => ?_, fun h => hx.2.2 α' h⟩
  subst h
  exact hx.2.1

end Definitions

/-! ### Statement targets -/

/-- Renard V.3.14–V.3.16 inside `𝔞*_∅` and `𝔞_∅`. For a maximal split torus of a connected
reductive group, a generic cocharacter, integral reflection data `D` and a set `J` of simple
roots:
* (V.3.14) each simple root `α ∉ J` has exactly one projection to `𝔞*_M` and its coroot exactly
  one projection to `𝔞_M`, and distinct such roots have distinct projections, so `β ↦ β̌` is
  well defined;
* (V.3.14, V.3.16) the fundamental weights (resp. coweights) of the simple roots outside `J`
  form a basis of `(𝔞^G_M)*` (resp. `𝔞^G_M`); in the weight basis, `^G_P[(𝔞^G_M)*]^+` and its
  closure are the combinations with positive (resp. nonnegative) coefficients, and (V.3.15)
  `^G_P[𝔞*_M]^+` and its closure are these plus `𝔞*_G`;
* (V.3.15) `^G_P[𝔞*_M]^+` and its closure are cut out in `𝔞*_M` by `⟨·, β̌⟩ > 0`
  (resp. `≥ 0`) for `β ∈ Δ(P)`;
* (V.3.16) `^G_P[𝔞*_M]^+ = ^G_P[(𝔞^G_M)*]^+ + 𝔞*_G`, and the same for the closures (the sum is
  direct by `relativeCharacterRootComplement`);
* (V.3.16) `^G_P[(𝔞^G_M)*]^+` is open in `(𝔞^G_M)*` and its closure in `𝔞*_∅` is the closed
  face, for the canonical topology of the finite-dimensional real vector space `𝔞*_∅`. -/
def ParabolicChamberLinearAlgebraStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ D : RelativeRootReflectionData i,
    ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      (∀ α ∈ simpleRelativeRoots i ν \ J,
        (∃! y, y ∈ D.projectedRoots J {α}) ∧ ∃! v, v ∈ D.projectedCoroots J {α}) ∧
      (∀ α ∈ simpleRelativeRoots i ν \ J, ∀ α' ∈ simpleRelativeRoots i ν \ J, ∀ y,
        y ∈ D.projectedRoots J {α} → y ∈ D.projectedRoots J {α'} → α = α') ∧
      (∃ b : Module.Basis {α : simpleRelativeRoots i ν // α.1 ∉ J} ℝ
          (corootAnnihilator i D J ⊓ relativeRootSpanReal i : Submodule ℝ (Vstar T)),
        (∀ α, D.IsRealFundamentalWeight ν α.1 (b α : Vstar T)) ∧
        openCorootFace i ν D J =
          {y | ∃ c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ, (∀ α, 0 < c α) ∧
            y = ∑ᶠ α, c α • (b α : Vstar T)} ∧
        closedCorootFace i ν D J =
          {y | ∃ c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ, (∀ α, 0 ≤ c α) ∧
            y = ∑ᶠ α, c α • (b α : Vstar T)} ∧
        openSimpleCorootFace i ν D J =
          {y | ∃ c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ, (∀ α, 0 < c α) ∧
            ∃ μ ∈ LinearMap.range (rationalCharacterRestrictReal i),
              y = ∑ᶠ α, c α • (b α : Vstar T) + μ} ∧
        closedSimpleCorootFace i ν D J =
          {y | ∃ c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ, (∀ α, 0 ≤ c α) ∧
            ∃ μ ∈ LinearMap.range (rationalCharacterRestrictReal i),
              y = ∑ᶠ α, c α • (b α : Vstar T) + μ}) ∧
      (∃ b : Module.Basis {α : simpleRelativeRoots i ν // α.1 ∉ J} ℝ
          (rootAnnihilator T J ⊓
            cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i)) :
            Submodule ℝ (V T)),
        ∀ α, IsRealFundamentalCoweight i ν α.1 (b α)) ∧
      openSimpleCorootFace i ν D J =
        {y | y ∈ corootAnnihilator i D J ∧
          ∀ y' v, IsParabolicCorootOf i ν D J y' v → 0 < pair T y v} ∧
      closedSimpleCorootFace i ν D J =
        {y | y ∈ corootAnnihilator i D J ∧
          ∀ y' v, IsParabolicCorootOf i ν D J y' v → 0 ≤ pair T y v} ∧
      openSimpleCorootFace i ν D J =
        openCorootFace i ν D J +
          (LinearMap.range (rationalCharacterRestrictReal i) : Set (Vstar T)) ∧
      closedSimpleCorootFace i ν D J =
        closedCorootFace i ν D J +
          (LinearMap.range (rationalCharacterRestrictReal i) : Set (Vstar T)) ∧
      (letI : TopologicalSpace (Vstar T) := moduleTopology ℝ (Vstar T);
        IsOpen ((↑) ⁻¹' openCorootFace i ν D J :
          Set (corootAnnihilator i D J ⊓ relativeRootSpanReal i : Submodule ℝ (Vstar T))) ∧
        closure (openCorootFace i ν D J) = closedCorootFace i ν D J)

/-- Renard V.3.14–V.3.15 on the split component. For a maximal split torus of a connected
reductive group, a generic cocharacter, integral reflection data `D`, a set `J` of simple roots,
a closed representative `L` of the standard Levi of `J`, a split component `A` of `L` and the
factor `f : A ⟶ T` of its inclusion:
* restriction along `f` maps `𝔞*_M = corootAnnihilator i D J` bijectively onto `Vstar A`, and
  carries the projected simple roots outside `J` onto `Δ(P)`;
* the simple roots outside `J` have distinct restrictions, every `β ∈ Δ(P)` has exactly one
  `β̌` in `V A`, and every fundamental coweight `ϖ^∨_α`, `α ∉ J`, is the image of exactly one
  vector of `V A`;
* the chambers `{⟨χ, β̌⟩ > 0}` and `{⟨χ, β̌⟩ ≥ 0}` of V.3.15 are the published lifted chambers
  `restrictedCorootChamber` and `restrictedClosedCorootChamber`, and (the remark of V.3.15) they
  consist of the restrictions of `∑ c_α ϖ_α + μ` with `c_α > 0` (resp. `≥ 0`) and `μ ∈ 𝔞*_G`;
* `⁺[𝔞]^G_P` and its closure are the combinations of the `β̌` with positive (resp. nonnegative)
  coefficients, one for each simple root outside `J`;
* restriction carries the realizations of `⁺[𝔞*]^G_P` and of its closure onto the published
  `restrictedRootPositiveCone` and `restrictedRootNonnegCone`. -/
def ParabolicSplitComponentChamberStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ D : RelativeRootReflectionData i,
    ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
    ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j → (standardLevi i ν J).IsRepresentedBy j →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ L),
      IsSplitComponent a →
    ∀ f : A ⟶ T, CommGroupScheme.groupHom f ≫ i = a ≫ j →
      Set.BijOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
        (corootAnnihilator i D J) Set.univ ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f) '' parabolicRoots i ν D J =
        restrictedSimpleRoots i ν J f ∧
      (∀ α ∈ simpleRelativeRoots i ν \ J, ∀ α' ∈ simpleRelativeRoots i ν \ J,
        restrictedRootVector f α = restrictedRootVector f α' → α = α') ∧
      (∀ β ∈ restrictedSimpleRoots i ν J f, ∃! v, IsRestrictedParabolicCoroot i ν D J f β v) ∧
      (∀ α : simpleRelativeRoots i ν, α.1 ∉ J →
        ∃! w : V A, IsRealFundamentalCoweight i ν α (cocharacterMapReal f w)) ∧
      parabolicCorootChamber i ν D J f = restrictedCorootChamber i ν J f D ∧
      parabolicClosedCorootChamber i ν D J f = restrictedClosedCorootChamber i ν J f D ∧
      parabolicCorootChamber i ν D J f =
        {x | ∃ (c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ)
            (ϖ : {α : simpleRelativeRoots i ν // α.1 ∉ J} → Vstar T),
          (∀ α, 0 < c α) ∧ (∀ α, D.IsRealFundamentalWeight ν α.1 (ϖ α)) ∧
          ∃ μ ∈ LinearMap.range (rationalCharacterRestrictReal i),
            x = rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
              (∑ᶠ α, c α • ϖ α + μ)} ∧
      parabolicClosedCorootChamber i ν D J f =
        {x | ∃ (c : {α : simpleRelativeRoots i ν // α.1 ∉ J} → ℝ)
            (ϖ : {α : simpleRelativeRoots i ν // α.1 ∉ J} → Vstar T),
          (∀ α, 0 ≤ c α) ∧ (∀ α, D.IsRealFundamentalWeight ν α.1 (ϖ α)) ∧
          ∃ μ ∈ LinearMap.range (rationalCharacterRestrictReal i),
            x = rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
              (∑ᶠ α, c α • ϖ α + μ)} ∧
      restrictedCorootPositiveCone i ν D J f =
        {v | ∃ (s : Finset (characterLattice T)) (c : characterLattice T → ℝ)
            (w : characterLattice T → V A), (s : Set (characterLattice T)) =
              simpleRelativeRoots i ν \ J ∧
            (∀ α ∈ s, 0 < c α ∧
              IsRestrictedParabolicCoroot i ν D J f (restrictedRootVector f α) (w α)) ∧
            v = ∑ α ∈ s, c α • w α} ∧
      restrictedCorootNonnegCone i ν D J f =
        {v | ∃ (s : Finset (characterLattice T)) (c : characterLattice T → ℝ)
            (w : characterLattice T → V A), (s : Set (characterLattice T)) =
              simpleRelativeRoots i ν \ J ∧
            (∀ α ∈ s, 0 ≤ c α ∧
              IsRestrictedParabolicCoroot i ν D J f (restrictedRootVector f α) (w α)) ∧
            v = ∑ α ∈ s, c α • w α} ∧
      ∀ hfin : (simpleRelativeRoots i ν).Finite,
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ''
            projectedRootPositiveCone i D J (simpleRelativeRoots i ν \ J) =
          restrictedRootPositiveCone i ν J f hfin ∧
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ''
            projectedRootNonnegCone i D J (simpleRelativeRoots i ν \ J) =
          restrictedRootNonnegCone i ν J f hfin

/-- Renard V.3.14–V.3.16: the two statement targets of this file. -/
def ParabolicChamberStatement : Prop :=
  ParabolicChamberLinearAlgebraStatement.{u} ∧ ParabolicSplitComponentChamberStatement.{u}

end Langlands.GroupScheme
