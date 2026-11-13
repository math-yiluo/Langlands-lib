import Langlands.GroupScheme.Rational.LanglandsInvariantForm
import Langlands.GroupScheme.Rational.RelativeRankStatement
import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.Geometry.Building.RealTorusDuality
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-! # Real coroots, real bases and standard Levi decompositions (Renard V.3.7, V.3.12, V.3.13)

Inside `𝔞_∅ = X_*(A_∅) ⊗ ℝ = V T` and `𝔞^*_∅ = X^*(A_∅) ⊗ ℝ = Vstar T`, for a maximal split torus
`T` of a connected reductive group and integral reflection data `D`: the real coroots, the coroot
span, the fundamental weights and coweights, and the pieces `(𝔞^L_M)^*` and `𝔞^L_M` of a pair of
standard Levi subgroups (in the corrected form of the book's V.3.13, see the Markdown). Four
statement targets record V.3.7, the real form of V.3.12 and V.3.13.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

section Definitions

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

/-- The simple relative roots for a cocharacter are relative roots. -/
theorem simpleRelativeRoots_subset_relativeRoots (ν : cocharacterLattice T) :
    simpleRelativeRoots i ν ⊆ relativeRoots i :=
  (simpleRelativeRoots_subset_positive i ν).trans (positiveRelativeRoots_subset_relativeRoots i ν)

/-- A simple relative root regarded as an element of the index type of all relative roots. -/
abbrev simpleToRelativeRoot (ν : cocharacterLattice T) :
    simpleRelativeRoots i ν → relativeRoots i :=
  Set.inclusion (simpleRelativeRoots_subset_relativeRoots i ν)

/-- Renard V.3.12, the fundamental coweight `ϖ^∨_α`: the vector `v` of
`𝔞^G_∅ ⊂ 𝔞_∅` (the cocharacters annihilated by the restrictions to `T` of the real rational
characters of `G`, V.3.6) with `⟨α, v⟩ = 1` and `⟨β, v⟩ = 0` for the other simple roots `β`. -/
def IsRealFundamentalCoweight (ν : cocharacterLattice T) (α : simpleRelativeRoots i ν)
    (v : V T) : Prop :=
  v ∈ cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i)) ∧
    eval T α.1 v = 1 ∧ ∀ β : simpleRelativeRoots i ν, β ≠ α → eval T β.1 v = 0

variable [Mono i.hom.hom.left]

/-- Renard V.3.7, the inner product on `𝔞_∅`: a symmetric positive definite real bilinear form
on the full real cocharacter space, invariant under the actual relative Weyl group. This is the
cocharacter-side companion of `IsWeylInvariantInnerProduct`. -/
def IsWeylInvariantCocharacterInnerProduct (C : LinearMap.BilinForm ℝ (V T)) : Prop :=
  (∀ v w : V T, C v w = C w v) ∧ (∀ v : V T, v ≠ 0 → 0 < C v v) ∧
    ∀ (w : relativeWeylGroup i) (v v' : V T),
      C (relativeWeylRealAction i w v) (relativeWeylRealAction i w v') = C v v'

namespace RelativeRootReflectionData

variable {i} (D : RelativeRootReflectionData i)

/-- Renard V.3.7, the coroot `α̌ ∈ 𝔞_∅` of a relative root `α`: the real image `1 ⊗ α̌` of the
integral coroot supplied by `D`. -/
def realCoroot (α : relativeRoots i) : V T :=
  (1 : ℝ) ⊗ₜ[ℤ] D.coroot α

@[simp] theorem pair_tmul_realCoroot (r : ℝ) (χ : characterLattice T) (α : relativeRoots i) :
    pair T (r ⊗ₜ[ℤ] χ) (D.realCoroot α) = r * (latticePairing T χ (D.coroot α) : ℝ) := by
  rw [realCoroot, pair_tmul_tmul, mul_one]

/-- `⟨α, α̌⟩ = 2` in the real pairing. -/
theorem pair_root_realCoroot (α : relativeRoots i) :
    pair T ((1 : ℝ) ⊗ₜ[ℤ] α.1) (D.realCoroot α) = 2 := by
  rw [pair_tmul_realCoroot, D.pair_self]
  norm_num

/-- Renard V.3.7, the real span of the coroots `Σ^∨(A_∅)` in `𝔞_∅`. -/
def realCorootSpan : Submodule ℝ (V T) :=
  Submodule.span ℝ (Set.range D.realCoroot)

/-- The real coroots `α̌` of the relative roots `α ∈ J`. -/
def realCorootsOf (J : Set (characterLattice T)) : Set (V T) :=
  D.realCoroot '' {α : relativeRoots i | α.1 ∈ J}

/-- Renard V.3.12, the fundamental weight `ϖ_α`: the vector `x` of the real root span
`(𝔞^G_∅)^*` with `⟨x, α̌⟩ = 1` and `⟨x, β̌⟩ = 0` for the other simple roots `β`. -/
def IsRealFundamentalWeight (ν : cocharacterLattice T) (α : simpleRelativeRoots i ν)
    (x : Vstar T) : Prop :=
  x ∈ relativeRootSpanReal i ∧
    pair T x (D.realCoroot (simpleToRelativeRoot i ν α)) = 1 ∧
    ∀ β : simpleRelativeRoots i ν, β ≠ α →
      pair T x (D.realCoroot (simpleToRelativeRoot i ν β)) = 0

/-- Renard V.3.13, corrected (source issue I4): for `J ⊆ K` the simple-root sets of standard
Levi subgroups `M ⊆ L`, the subspace `(𝔞^L_M)^*` of `𝔞^*_M ⊂ 𝔞^*_∅`, namely the part of
`𝔞^*_M = corootAnnihilator i D J` lying in the real span of `K`. -/
def leviRootSpace (J K : Set (characterLattice T)) : Submodule ℝ (Vstar T) :=
  corootAnnihilator i D J ⊓
    Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' K)

/-- The projections to `𝔞^*_M = corootAnnihilator i D J`, along the real span of `J`, of the
roots in `S`: the vectors `y ∈ 𝔞^*_M` with `α - y` in the span of `J` for some `α ∈ S`. -/
def projectedRoots (J S : Set (characterLattice T)) : Set (Vstar T) :=
  {y | y ∈ corootAnnihilator i D J ∧ ∃ α ∈ S,
    (1 : ℝ) ⊗ₜ[ℤ] α - y ∈
      Submodule.span ℝ ((fun β : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] β) '' J)}

/-- Renard V.3.13, corrected dually: `𝔞^L_M ⊂ 𝔞_M ⊂ 𝔞_∅`, the part of
`𝔞_M = rootAnnihilator T J` lying in the real span of the coroots of `K`. -/
def leviCorootSpace (J K : Set (characterLattice T)) : Submodule ℝ (V T) :=
  rootAnnihilator T J ⊓ Submodule.span ℝ (D.realCorootsOf K)

/-- The projections to `𝔞_M = rootAnnihilator T J`, along the real span of the coroots of `J`,
of the coroots of the roots in `S`. -/
def projectedCoroots (J S : Set (characterLattice T)) : Set (V T) :=
  {v | v ∈ rootAnnihilator T J ∧ ∃ w ∈ D.realCorootsOf S,
    w - v ∈ Submodule.span ℝ (D.realCorootsOf J)}

end RelativeRootReflectionData

end Definitions

/-- Renard V.3.12, real form: for a maximal split torus of a connected reductive group and a
generic cocharacter, the simple relative roots `1 ⊗ α` form a real basis of the real root span
`(𝔞^G_∅)^*`. This is the scalar extension of `RelativeSimpleRootBasisStatement`. -/
def RelativeRealSimpleRootBasisStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
    haveI := hG.isAffineHom
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
      ∃ b : Module.Basis (simpleRelativeRoots i ν) ℝ (relativeRootSpanReal i),
        ∀ α, (b α : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] α.1

/-- Renard V.3.7 for the minimal Levi: for a maximal split torus of a connected reductive group
and any integral reflection data `D`,
* `W`-invariant inner products exist on `𝔞^*_∅` and on `𝔞_∅`, and the integral coroots do not
  depend on `D`;
* for every `W`-invariant inner product on `𝔞^*_∅`, the real coroot `α̌` is the unique vector of
  `𝔞_∅` with `⟨λ, α̌⟩ (α, α) = 2 (α, λ)` for all `λ`;
* the coroots span `𝔞^G_∅`, the annihilator of the restricted rational characters of `G`, and
  `𝔞_∅ = 𝔞_G ⊕ 𝔞^G_∅` with `𝔞_G` the common root annihilator;
* the finitely many roots in `(𝔞^G_∅)^*` and the coroots in `𝔞^G_∅` form a crystallographic
  real root system for the real pairing, whose reflections and coreflections are the actions of
  the representatives of `D` on `𝔞^*_∅` and `𝔞_∅`;
* the indivisible roots `Σ(A_∅)` with their coroots form a reduced crystallographic real root
  system in the same spaces. -/
def RelativeRealCorootStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ D : RelativeRootReflectionData i,
      (∃ B : LinearMap.BilinForm ℝ (Vstar T), IsWeylInvariantInnerProduct i B) ∧
      (∃ C : LinearMap.BilinForm ℝ (V T), IsWeylInvariantCocharacterInnerProduct i C) ∧
      (∀ D' : RelativeRootReflectionData i, D'.coroot = D.coroot) ∧
      (∀ B : LinearMap.BilinForm ℝ (Vstar T), IsWeylInvariantInnerProduct i B →
        ∀ (α : relativeRoots i) (v : V T),
          (∀ x : Vstar T, pair T x v * B ((1 : ℝ) ⊗ₜ[ℤ] α.1) ((1 : ℝ) ⊗ₜ[ℤ] α.1) =
              2 * B x ((1 : ℝ) ⊗ₜ[ℤ] α.1)) ↔
            v = D.realCoroot α) ∧
      D.realCorootSpan =
        cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i)) ∧
      IsCompl (relativeCentralDirections i)
        (cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))) ∧
      Finite (relativeRoots i) ∧
      (∃ P : RootPairing (relativeRoots i) ℝ (relativeRootSpanReal i) D.realCorootSpan,
        P.IsRootSystem ∧ P.IsCrystallographic ∧
        (∀ α, (P.root α : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] α.1) ∧
        (∀ α, (P.coroot α : V T) = D.realCoroot α) ∧
        (∀ x y, P.toLinearMap x y = pair T (x : Vstar T) (y : V T)) ∧
        (∀ α x, (P.reflection α x : Vstar T) =
          relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α)) (x : Vstar T)) ∧
        ∀ α y, (P.coreflection α y : V T) =
          relativeWeylRealAction i (QuotientGroup.mk (D.representative α)) (y : V T)) ∧
      ∃ P : RootPairing (RelativeRoot.indivisibleRoots i) ℝ (relativeRootSpanReal i)
          D.realCorootSpan,
        P.IsRootSystem ∧ P.IsCrystallographic ∧ P.IsReduced ∧
        (∀ α, (P.root α : Vstar T) = (1 : ℝ) ⊗ₜ[ℤ] α.1) ∧
        (∀ α, (P.coroot α : V T) = D.realCoroot ⟨α.1, α.2.1⟩) ∧
        ∀ x y, P.toLinearMap x y = pair T (x : Vstar T) (y : V T)

/-- Renard V.3.12: for a maximal split torus of a connected reductive group, a generic
cocharacter and integral reflection data `D`, the simple coroots form a basis of `𝔞^G_∅`; each
simple root has exactly one fundamental weight and exactly one fundamental coweight, and the
fundamental weights (resp. coweights) form a basis of `(𝔞^G_∅)^*` (resp. `𝔞^G_∅`). -/
def RelativeFundamentalWeightStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ D : RelativeRootReflectionData i,
      (∃ b : Module.Basis (simpleRelativeRoots i ν) ℝ
          (cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))),
        ∀ α, (b α : V T) = D.realCoroot (simpleToRelativeRoot i ν α)) ∧
      (∃ b : Module.Basis (simpleRelativeRoots i ν) ℝ (relativeRootSpanReal i),
        ∀ α, D.IsRealFundamentalWeight ν α (b α)) ∧
      (∃ b : Module.Basis (simpleRelativeRoots i ν) ℝ
          (cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i))),
        ∀ α, IsRealFundamentalCoweight i ν α (b α)) ∧
      (∀ α x y, D.IsRealFundamentalWeight ν α x → D.IsRealFundamentalWeight ν α y → x = y) ∧
      ∀ α v w, IsRealFundamentalCoweight i ν α v → IsRealFundamentalCoweight i ν α w → v = w

/-- Renard V.3.13, in the corrected form of source issue I4: for a maximal split torus of a
connected reductive group, a generic cocharacter and integral reflection data `D`,
* `𝔞^*_G` (the coroot annihilator of all simple roots) is the space of restricted real rational
  characters of `G`, `𝔞_G` (the annihilator of all simple roots) is the common root annihilator,
  and the simple coroots span `𝔞^G_∅`;
* for simple-root sets `J ⊆ K` of standard Levi subgroups `M ⊆ L`: `𝔞^*_∅ = 𝔞^*_M ⊕ span J`,
  `𝔞_∅ = 𝔞_M ⊕ span J^∨`, the real pairing restricts to a perfect pairing of `𝔞^*_M` with
  `𝔞_M`, `𝔞^*_M = 𝔞^*_L ⊕ (𝔞^L_M)^*` and `𝔞_M = 𝔞_L ⊕ 𝔞^L_M`, where `(𝔞^L_M)^*` (resp.
  `𝔞^L_M`) is spanned by the projections to `𝔞^*_M` (resp. `𝔞_M`) of the roots (resp. coroots)
  of `K ∖ J`, and both decompositions are orthogonal for every invariant inner product. -/
def StandardLeviRealDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ ν : cocharacterLattice T, IsGenericCocharacter i ν →
    ∀ D : RelativeRootReflectionData i,
      corootAnnihilator i D (simpleRelativeRoots i ν) =
        LinearMap.range (rationalCharacterRestrictReal i) ∧
      rootAnnihilator T (simpleRelativeRoots i ν) = relativeCentralDirections i ∧
      Submodule.span ℝ (D.realCorootsOf (simpleRelativeRoots i ν)) =
        cocharacterAnnihilator (LinearMap.range (rationalCharacterRestrictReal i)) ∧
      ∀ J K : Set (characterLattice T), J ⊆ K → K ⊆ simpleRelativeRoots i ν →
        IsCompl (corootAnnihilator i D J)
          (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J)) ∧
        IsCompl (rootAnnihilator T J) (Submodule.span ℝ (D.realCorootsOf J)) ∧
        ((pair T).domRestrict₁₂ (corootAnnihilator i D J) (rootAnnihilator T J)).IsPerfPair ∧
        Disjoint (corootAnnihilator i D K) (D.leviRootSpace J K) ∧
        corootAnnihilator i D K ⊔ D.leviRootSpace J K = corootAnnihilator i D J ∧
        D.leviRootSpace J K = Submodule.span ℝ (D.projectedRoots J (K \ J)) ∧
        Disjoint (rootAnnihilator T K) (D.leviCorootSpace J K) ∧
        rootAnnihilator T K ⊔ D.leviCorootSpace J K = rootAnnihilator T J ∧
        D.leviCorootSpace J K = Submodule.span ℝ (D.projectedCoroots J (K \ J)) ∧
        (∀ B : LinearMap.BilinForm ℝ (Vstar T), IsWeylInvariantInnerProduct i B →
          ∀ x ∈ corootAnnihilator i D K, ∀ y ∈ D.leviRootSpace J K, B x y = 0) ∧
        ∀ C : LinearMap.BilinForm ℝ (V T), IsWeylInvariantCocharacterInnerProduct i C →
          ∀ v ∈ rootAnnihilator T K, ∀ w ∈ D.leviCorootSpace J K, C v w = 0

/-- The linear algebra of Renard V.3.7, V.3.12 (real form) and V.3.13 (corrected) for the
minimal standard parabolic and pairs of standard Levi subgroups. -/
def RelativeRealCorootLinearAlgebraStatement : Prop :=
  RelativeRealSimpleRootBasisStatement.{u} ∧ RelativeRealCorootStatement.{u} ∧
    RelativeFundamentalWeightStatement.{u} ∧ StandardLeviRealDecompositionStatement.{u}

end Langlands.GroupScheme
