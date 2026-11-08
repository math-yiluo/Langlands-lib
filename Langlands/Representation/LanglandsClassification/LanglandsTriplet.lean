import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Coroot chambers and Langlands triplets (Renard V.3.15 and VII.4.1)

For a maximal split torus `T` of `G` with a generic cocharacter `ν` (a minimal parabolic
`P_∅`), integral reflection data `D` (a coroot for every relative root), a set `J` of simple
roots (a standard parabolic `P = MN` with standard Levi `M`) and the factor `f : A_M → T` of
the split component of `M`, the open and closed coroot chambers `^G_P[𝔞*_M]^+` and its closure
are subsets of the real character space of `A_M`.

A Langlands triplet consists of a standard parabolic `P = MN`, an irreducible tempered smooth
representation `σ` of `M(F)` and an unramified character `ψ` of `M(F)` whose real part lies in
the open coroot chamber. The module also defines the real part of `ψ`; the twist `σ ⊗ ψ` is
the published `SmoothRep.twist`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {A T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (J : Set (characterLattice T)) (f : A ⟶ T) (D : RelativeRootReflectionData i)

open RealTorusSpace

/-- Renard V.3.15, `^G_P[𝔞*]^+`: the open coroot chamber of the standard parabolic with
simple-root index `J`, as a subset of the real character space of `A`. An element `x` lies in
it when it is the restriction along `f` of some `y` in the real character space of `T` with
`⟨y, α̌⟩ = 0` for every root `α ∈ J` and `⟨y, α̌⟩ > 0` for every simple root `α ∉ J`, the
coroots `α̌` being those of `D`. -/
def restrictedCorootChamber : Set (Vstar A) :=
  {x | ∃ y : Vstar T, rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = x ∧
    (∀ α : relativeRoots i, α.1 ∈ J → pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0) ∧
    (∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
      0 < pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))}

/-- Renard V.3.15, the closure `^G_P[𝔞*]^+` (overlined): the same condition with
`⟨y, α̌⟩ ≥ 0` for every simple root `α ∉ J`. -/
def restrictedClosedCorootChamber : Set (Vstar A) :=
  {x | ∃ y : Vstar T, rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y = x ∧
    (∀ α : relativeRoots i, α.1 ∈ J → pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0) ∧
    (∀ α : relativeRoots i, α.1 ∈ simpleRelativeRoots i ν → α.1 ∉ J →
      0 ≤ pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))}

theorem restrictedCorootChamber_subset_closed :
    restrictedCorootChamber i ν J f D ⊆ restrictedClosedCorootChamber i ν J f D := by
  rintro x ⟨y, hy, hJ, hpos⟩
  exact ⟨y, hy, hJ, fun α hα hαJ => (hpos α hα hαJ).le⟩

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

section Unramified

variable (l : M ⟶ P) (hl : IsRationalLeviSubgroup l)

/-- Renard's `X(M)`: the unramified characters of `M(F)`, the continuous characters trivial
on the common kernel `M(F)¹` of the norms `|χ|_F` of all rational characters `χ` of `M`. -/
abbrev leviUnramifiedCharacters : Type u :=
  letI := leviPointTopology l hl
  Plancherel.unramifiedCharacters
    (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)

/-- The real part `ℜ(ψ)` of an unramified character of `M(F)`, as an element of the real
character space of the split component `A`: the normalized real part of the restriction of
`ψ` to `A(F)`. -/
def leviUnramifiedRealPart (a : A.toGrp ⟶ M) (ha : IsSplitComponent a)
    (ψ : leviUnramifiedCharacters l hl) : RealTorusSpace.Vstar A :=
  letI := leviPointTopology l hl
  Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1
    (ψ.val.toMonoidHom.comp (rationalPoints.map a))

end Unramified

section Triplet

local instance tripletAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Renard VII.4.1, Definition: `(P = MN, σ, ψ)` is a Langlands triplet relative to the
minimal parabolic of the maximal split torus `i : T → G` and the generic cocharacter `ν`, and
to the reflection data `D`. The simple-root index `J` and the factor `f : A → T` present `P`
as a standard parabolic with standard Levi `M` and split component `a : A → M`; `σ` is an
irreducible tempered smooth representation of `M(F)`; and the real part of the unramified
character `ψ` lies in the open coroot chamber `^G_P[𝔞*_M]^+`. -/
def IsLanglandsTriplet (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
    (D : RelativeRootReflectionData i)
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a)
    (J : Set (characterLattice T)) (f : A ⟶ T)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (ψ : leviUnramifiedCharacters l hl) : Prop :=
  haveI := hl.isConnectedReductive.isAffineHom
  letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  (⟨T, i, ν, J, f⟩ : ParabolicRootPresentationData A G).IsCompatible p l a ∧
    σ.IsIrreducible ∧ IsNormalizedExponentTempered hl.isConnectedReductive σ ∧
    leviUnramifiedRealPart l hl a ha ψ ∈ restrictedCorootChamber i ν J f D

end Triplet

end Langlands.Aubert.General.RepresentedParabolic
