import Langlands.GroupScheme.Rational.ArthurRelativeCombinatorics
import Langlands.Global.AdelicEisensteinSeries
import Langlands.Global.AdelicGroupHaarMeasure
import Langlands.Global.AdelicEisensteinConstantTermStatement
import Langlands.Global.AdelicParabolicQuotient
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.Global.ArthurParabolicSpaces

/-! # Arthur's truncation operator

Arthur 2005, §13; Lapid 2011, §2, p.312. For a connected reductive group `G` over a number field
`F`, a maximal split torus `i : T → G`, a generic cocharacter `ν` (the minimal parabolic `P_0`),
a compact subgroup `K` with `P_0(𝔸)K = G(𝔸)` and `T ∈ 𝔞_0 = V T`:

`Λ^T φ(x) = ∑_{P ⊇ P_0} (−1)^{dim(A_P/A_G)} ∑_{δ ∈ P(F)\G(F)} φ_P(δx) τ̂_P(H_P(δx) − T)`,

and the relative operators `Λ^{T,P}`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints ArthurParabolicSpaces

variable (F : Type u) [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)

section Instances

variable {i ν}

scoped instance instIsAffineG : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

scoped instance instClosedParabolic (J : Set (characterLattice T)) :
    IsClosedImmersion (Standard.parabolicHom i ν J).hom.hom.left :=
  Standard.isClosedSubgroup_parabolicHom i ν J

scoped instance instAffineParabolic (J : Set (characterLattice T)) :
    IsAffine (Standard.parabolicScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.parabolicHom i ν J).hom.hom.left

scoped instance instClosedUnipotent (J : Set (characterLattice T)) :
    IsClosedImmersion (Standard.unipotentHom i ν J).hom.hom.left :=
  Standard.isClosedSubgroup_unipotentHom i ν J

scoped instance instAffineUnipotent (J : Set (characterLattice T)) :
    IsAffine (Standard.unipotentScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.unipotentHom i ν J).hom.hom.left

end Instances

section Heights

variable {F i ν}

/-- The point of `𝔞_0 = V T` attached to `H ∈ Hom(X(P_0), ℝ)` through the identification
`X(P_0) ⊗ ℝ ≅ X(T) ⊗ ℝ` (restriction, assumed bijective) and the perfect pairing of `V T` with
`Vstar T`: `⟨y, v⟩ = H(ρ⁻¹ y)` for `y ∈ Vstar T`. -/
def toA0 (hT : IsSplitTorus T.toGrp)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (H : RealCharacterDual F (Standard.parabolicScheme i ν ∅)) : V T :=
  haveI := isPerfPair_of_isSplitTorus hT
  (pair T).flip.toPerfPair.symm
    (((AdelicGroupPoints.realParameterPairing F (Standard.parabolicScheme i ν ∅)).flip H).comp
      (LinearEquiv.ofBijective (restrictToTorus F i ν ∅) hρ).symm.toLinearMap)

omit [NumberField F] [Mono i.hom.hom.left] in
theorem pair_toA0 (hT : IsSplitTorus T.toGrp)
    (hρ : Function.Bijective (restrictToTorus F i ν ∅))
    (H : RealCharacterDual F (Standard.parabolicScheme i ν ∅))
    (m : RealCharacterParameter F (Standard.parabolicScheme i ν ∅)) :
    pair T (restrictToTorus F i ν ∅ m) (toA0 hT hρ H) =
      AdelicGroupPoints.realParameterPairing F (Standard.parabolicScheme i ν ∅) m H := by
  have := isPerfPair_of_isSplitTorus hT
  have h := LinearMap.toPerfPair_apply (pair T).flip
    ((pair T).flip.toPerfPair.symm
      (((AdelicGroupPoints.realParameterPairing F (Standard.parabolicScheme i ν ∅)).flip H).comp
        (LinearEquiv.ofBijective (restrictToTorus F i ν ∅) hρ).symm.toLinearMap))
    (restrictToTorus F i ν ∅ m)
  rw [LinearEquiv.apply_symm_apply] at h
  simp only [LinearMap.flip_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] at h
  rw [toA0, ← h, LinearEquiv.ofBijective_symm_apply_apply]

end Heights

section ConstantTerm

variable [LocallyOfFiniteType G.X.hom]

/-- The constant term `φ_P(x) = ∫_{N_P(F) \ N_P(𝔸)} φ(n x) dn` along the standard parabolic
subgroup with `Δ_0^P = J`: the published `AdelicGroupPoints.subgroupConstantTerm` of the closed
unipotent representative `Standard.unipotentHom i ν J`, for the mass-normalized quotient Haar
measure `normalizedRationalQuotientHaarMeasure`. -/
abbrev constantTerm (J : Set (characterLattice T)) (φ : AdelicGroupPoints F G → ℂ)
    (x : AdelicGroupPoints F G) : ℂ :=
  subgroupConstantTerm F (Standard.unipotentHom i ν J) φ x

/-- The integrand `n ↦ φ(nx)` of `constantTerm F i ν J φ x` is integrable on `N_P(F) \ N_P(𝔸)`
for the measure of `subgroupConstantTerm` (with the same chosen representatives): the constant
term is a convergent integral. -/
def HasConstantTerm (J : Set (characterLattice T)) (φ : AdelicGroupPoints F G → ℂ)
    (x : AdelicGroupPoints F G) : Prop :=
  haveI : IsClosed (AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (Standard.unipotentHom i ν J)) : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G (Standard.unipotentHom i ν J)
  Integrable (fun y => φ (((Quotient.out y : AdelicSubgroupPoints.adelicPoints F G
      (SubgroupFunctor.range (Standard.unipotentHom i ν J))) : AdelicGroupPoints F G) * x))
    (AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G
      (SubgroupFunctor.range (Standard.unipotentHom i ν J)))

end ConstantTerm

section Truncation

variable {F i ν} [LocallyOfFiniteType G.X.hom]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

variable (ν) in
/-- `Δ_0`, the simple relative roots, as a finite set. -/
def simpleFinset : Finset (characterLattice T) :=
  ((ArthurRelative.finite_relativeRoots hG hi).subset
    (simpleRelativeRoots_subset_relativeRoots i ν)).toFinset

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem mem_simpleFinset {α : characterLattice T} :
    α ∈ simpleFinset ν hG hi ↔ α ∈ simpleRelativeRoots i ν := by
  simp [simpleFinset]

/-- The height `H_0(x) ∈ 𝔞_0 = V T` of `x ∈ G(𝔸)`: the Iwasawa height of `K` for `P_0`, read in
`V T` (`toA0`). -/
def height (x : AdelicGroupPoints F G) : V T :=
  toA0 hi.isSplitSubtorus.1 hρ (hK.height x)

/-- The coset space `Q(F) \ P(F)` for standard parabolic subgroups with `Δ_0^Q = JQ` and
`Δ_0^P = JP`: the right cosets in `P(F)` of its intersection with `Q(F)`. -/
abbrev RelativeCosets (JQ JP : Set (characterLattice T)) :=
  Quotient (QuotientGroup.rightRel
    ((parabolicRationalSubgroup F (Standard.parabolicHom i ν JQ)).subgroupOf
      (parabolicRationalSubgroup F (Standard.parabolicHom i ν JP))))

/-- **Arthur's truncation operator** (Arthur 2005, (13.1); Lapid 2011, p.312):
`Λ^T φ(x) = ∑_{P ⊇ P_0} (−1)^{dim(A_P/A_G)} ∑_{δ ∈ P(F)\G(F)} φ_P(δx) τ̂_P(H_P(δx) − T)`,
for `T ∈ 𝔞_0`. The standard parabolic subgroups `P` are indexed by `S = Δ_0^P ⊆ Δ_0`, with
`dim(A_P/A_G) = |Δ_0 ∖ S|`; `τ̂_P(H_P(δx) − T)` is `ArthurRelative.tauHat` evaluated at
`H_0(δx) − T`, which only depends on the `𝔞_P^G`-component. Each inner sum is the unconditional
sum over the cosets, `0` if not summable. -/
def truncation (Tp : V T) (φ : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G) : ℂ :=
  ∑ S ∈ (simpleFinset ν hG hi).powerset,
    (-1 : ℂ) ^ ((simpleFinset ν hG hi).card - S.card) *
      ∑' c : ParabolicRationalCosets F (Standard.parabolicHom i ν (S : Set (characterLattice T))),
        constantTerm F i ν (S : Set (characterLattice T)) φ
            (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
          (ArthurRelative.tauHat hG hi ν D (S : Set (characterLattice T)) (simpleRelativeRoots i ν)
            (height hi hK hρ (((Quotient.out c : rationalSubgroup F G) : AdelicGroupPoints F G) * x)
              - Tp) : ℂ)

/-- **The relative truncation operator** `Λ^{T,P}` (Arthur 2005, p.73; Lapid 2011, p.312), for the
standard parabolic subgroup `P` with `Δ_0^P = SP`:
`Λ^{T,P} φ(x) = ∑_{P_0 ⊆ Q ⊆ P} (−1)^{dim(A_Q/A_P)} ∑_{δ ∈ Q(F)\P(F)} φ_Q(δx) τ̂_Q^P(H_Q(δx) − T)`,
with `dim(A_Q/A_P) = |SP ∖ SQ|`. -/
def relativeTruncation (SP : Finset (characterLattice T)) (Tp : V T)
    (φ : AdelicGroupPoints F G → ℂ) (x : AdelicGroupPoints F G) : ℂ :=
  ∑ SQ ∈ SP.powerset,
    (-1 : ℂ) ^ (SP.card - SQ.card) *
      ∑' c : RelativeCosets (F := F) (i := i) (ν := ν) (SQ : Set (characterLattice T))
          (SP : Set (characterLattice T)),
        constantTerm F i ν (SQ : Set (characterLattice T)) φ
            ((((Quotient.out c : parabolicRationalSubgroup F
              (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                rationalSubgroup F G) : AdelicGroupPoints F G) * x) *
          (ArthurRelative.tauHat hG hi ν D (SQ : Set (characterLattice T))
            (SP : Set (characterLattice T))
            (height hi hK hρ ((((Quotient.out c : parabolicRationalSubgroup F
              (Standard.parabolicHom i ν (SP : Set (characterLattice T)))) :
                rationalSubgroup F G) : AdelicGroupPoints F G) * x) - Tp) : ℂ)

end Truncation

section Functions

variable {F} {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Arthur's class `B_loc`: measurable functions on `G(𝔸)` that are bounded on compact sets and
left invariant under a subgroup `Γ` (`Γ = G(F)` for `B_loc(G(F) \ G(𝔸))`, `Γ = P(F)` for
`B_loc(P(F) \ G(𝔸))`). -/
def IsLocallyBoundedInvariant (Γ : Subgroup (AdelicGroupPoints F G))
    (φ : AdelicGroupPoints F G → ℂ) : Prop :=
  Measurable φ ∧ (∀ C : Set (AdelicGroupPoints F G), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖φ x‖ ≤ M) ∧
    ∀ g ∈ Γ, ∀ x, φ (g * x) = φ x

/-- The image of `P(F)` in `G(𝔸)`, for `p : P → G`. -/
def parabolicRationalImage {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    [IsAffine P.X.left] (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] :
    Subgroup (AdelicGroupPoints F G) :=
  (parabolicRationalSubgroup F p).map (rationalSubgroup F G).subtype

end Functions

end Langlands.Global.ArthurTruncation
