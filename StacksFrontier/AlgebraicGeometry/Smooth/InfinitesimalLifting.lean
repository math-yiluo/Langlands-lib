module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The infinitesimal lifting criterion for smoothness

The scheme-theoretic infinitesimal lifting criterion for smoothness over a locally
Noetherian base.

Let `f : X → S` be a morphism of schemes and `x ∈ X` a point. Assume that `S` is
locally Noetherian and that `f` is locally of finite type. Then the following
four conditions are equivalent:

1. `f` is smooth at `x` (i.e. smooth on some open neighbourhood of `x`).
2. The infinitesimal lifting property holds against every square-zero surjection
   of local rings.
3. The same lifting property restricted to small extensions.
4. The same lifting property restricted to residually trivial small extensions
   (those for which the induced residue-field map is an isomorphism).

## Definitions used

A ring map `φ : B' → B` between local rings is a *square-zero surjection* if `φ`
is surjective and `(ker φ)^2 = 0`.

A ring map `φ : B' → B` is a *small extension* if `B'`, `B` are local Artinian
rings, `φ` is surjective, and `ker φ` has length `1` as a `B'`-module
(equivalently `ker φ` is a simple `B'`-module, which forces `(ker φ)^2 = 0`).

## Notation / setup for the lifting diagram

A ring surjection `φ : B' → B` induces a closed immersion of affine schemes
`i = Spec(φ) : Spec B → Spec B'`.

A *solid commutative diagram* consists of morphisms `α : Spec B → X` and
`β : Spec B' → S` with `f ∘ α = β ∘ i` and with `α` sending the closed point of
`Spec B` (the maximal ideal `𝔪 ⊆ B`) to `x`.

A *dotted arrow making the diagram commute* is a morphism `γ : Spec B' → X` with
`γ ∘ i = α` and `f ∘ γ = β`.

Pictorially (Stacks horizontal arrows point to the left):

  X ←α─ Spec B
  │f      │i
  S ←β─ Spec B'   with the dotted lift γ : Spec B' → X.

In Lean's left-to-right composition `g ∘ h = h ≫ g`, the compatibility
`f ∘ α = β ∘ i` reads `α ≫ f = Spec.map φ ≫ β`, and the lift conditions
`γ ∘ i = α`, `f ∘ γ = β` read `Spec.map φ ≫ γ = α` and `γ ≫ f = β`.
-/

@[expose] public section
-- needed file-wide: `stalkClosedPointTo_specMap`,
-- `formallySmooth_stalkMap_liftsAgainstSquareZero`, `otilde_smul_mP_eq_zero`, `otilde_smul`,
-- `defect_link`, `residueFieldMap_isIso_of_surjective`,
-- `LiftsAgainstResiduallyTrivialSmallExtension.algLiftsResTrivSmall_of_lifts` and
-- `formallySmooth_stalkMap_smoothAt` all rewrite (or synthesize instances) through the
-- `CommRingCat`/`Scheme.presheaf.stalk`/`TrivSqZeroExt` bundling, which only unfolds with defeq
-- transparency relaxed.
-- (`backward.isDefEq.respectTransparency.types` was also set here and was not needed.)
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace InfinitesimalLifting

universe u

/- Smoothness on a neighbourhood of `x`, not a lifting property at `x`: the three
`LiftsAgainst…` conditions below quantify over square-zero surjections of local rings and
over morphisms out of their spectra, and this condition meets them only through the file's
equivalence theorem, not by unfolding. -/

/-- `f` is *smooth at* `x` if there is an open neighbourhood `U` of `x` such that
the restricted morphism `f|_U : U → S` is smooth. -/
def SmoothAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ U : X.Opens, x ∈ U ∧ Smooth (f.resLE ⊤ U le_top)

/-! ## Reduction to the local ring at `x`

Both substantive directions of Stacks 02HX are proved by passing to the local
rings at `x` and `f(x)`.  Write `A := 𝒪_{X,x}` (the stalk `X.presheaf.stalk x`)
and `R := 𝒪_{S,f(x)}`; the morphism `f` induces, at the level of stalks, a
**local** ring homomorphism `R ⟶ A` (`f.stalkMap x`, local by
`AlgebraicGeometry.Scheme.Hom.isLocalHom_stalkMap`).  We regard `A` as an
`R`-algebra via this map.

The bridge that converts the scheme-theoretic lifting diagrams into ring-theoretic
ones is `AlgebraicGeometry.SpecToEquivOfLocalRing X B`, the natural bijection
`(Spec B ⟶ X) ≃ Σ y, {ψ : 𝒪_{X,y} ⟶ B // IsLocalHom ψ}` valid for any local ring
`B`.  Under it:
* `α : Spec B ⟶ X` with `α.base (closedPoint B) = x` corresponds to a local hom
  `a : A = 𝒪_{X,x} ⟶ B`;
* `β : Spec B' ⟶ S` corresponds to a local hom `b : R = 𝒪_{S,f(x)} ⟶ B'` (after
  identifying `β.base (closedPoint B') = f(x)`, which follows from the
  compatibility `α ≫ f = Spec.map φ ≫ β` together with `α (closedPoint) = x`);
* the compatibility `α ≫ f = Spec.map φ ≫ β` becomes the commuting square of
  ring maps `a ∘ (f.stalkMap x) = φ ∘ b` (i.e. `a` is an `R`-algebra map to `B`
  and reduces, mod `ker φ`, the `R`-algebra map `b`);
* a lift `γ : Spec B' ⟶ X` with `Spec.map φ ≫ γ = α`, `γ ≫ f = β` corresponds to
  a local `R`-algebra hom `c : A ⟶ B'` with `φ ∘ c = a`.

Thus the scheme lifting problem against `φ : B' ⟶ B` is *equivalent* to the
algebraic lifting problem for the `R`-algebra `A` against the surjection
`φ : B' ⟶ B`. -/

/-- Formal smoothness of the stalk map at a point `y` of an open `U` of the source is unchanged
by restricting `f` to `U`. -/
private theorem formallySmooth_resLE_stalkMap_iff {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (y : U) : ((f.resLE ⊤ U le_top).stalkMap y).hom.FormallySmooth ↔
      (f.stalkMap (U.ι.base y)).hom.FormallySmooth :=
  RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (f.resLEStalkMap (U := ⊤) (V := U) le_top y)

/-- If `f` is smooth at `x`, then
the stalk map `𝒪_{S,f(x)} ⟶ 𝒪_{X,x}` is formally smooth as an `R`-algebra.

*Informal proof.*  Smoothness of `f` at `x` means `f` is a smooth morphism on an
open neighbourhood `U ∋ x`.  By `AlgebraicGeometry.smooth_iff` /
`Scheme.Hom.smooth_appLE`, choosing affine opens `Spec R₀ ⊆ S` around `f(x)` and
`Spec A₀ ⊆ U` around `x` with `A₀` mapping into `R₀`, the ring map
`R₀ ⟶ A₀` is `Smooth`, hence `FormallySmooth` (`RingHom.Smooth.formallySmooth`).
Formal smoothness is preserved under the localizations `R₀ ⟶ 𝒪_{S,f(x)} = R` and
`A₀ ⟶ 𝒪_{X,x} = A` at the points `f(x)`, `x` (localization is formally smooth,
`Algebra.FormallySmooth.localization_base` / `…of_isLocalization`, and formal
smoothness composes, `Algebra.FormallySmooth.comp`), so the induced local map
`R ⟶ A` is formally smooth. -/
theorem SmoothAt.formallySmooth_stalkMap
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (hf : SmoothAt f x) :
    letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
  -- direction 1→2: a smooth morphism's stalk map is formally smooth.
  obtain ⟨U, hxU, hsmooth⟩ := hf
  set g := f.resLE ⊤ U le_top with hg
  -- the point `x` as an element of `U`
  set y : (U : X.Opens) := ⟨x, hxU⟩ with hy
  -- `g.stalkMap y` is formally smooth since `g` is smooth (smooth locus is ⊤)
  have hmem : y ∈ g.smoothLocus := by
    rw [g.smoothLocus_eq_top]; trivial
  have hsm : (g.stalkMap y).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp hmem
  -- transfer to `f.stalkMap x` via the `resLEStalkMap` arrow isomorphism
  have key : (f.stalkMap (↑y)).hom.FormallySmooth :=
    (formallySmooth_resLE_stalkMap_iff f U y).mp hsm
  -- `↑y = x` definitionally, so this matches the algebra structure in the goal
  exact RingHom.FormallySmooth.toAlgebra key

/-!
### The obstruction calculus behind Stacks 02HT

The results in this section isolate the deformation-theoretic heart of Algebra Lemma 10.141.2
as self-contained ring theory, with no scheme machinery.

Let `A` be a local algebra of finite presentation over a Noetherian local ring `R` that lifts
against residually trivial small extensions, i.e. satisfies `AlgLiftsResTrivSmall R A`.  Then
`A` is formally smooth over `R`.  Fix a finite presentation `P = R[x₁,…,xₙ] ↠ A` with
`I = ker f`, which is finitely generated, and write `P := Algebra.Extension.ofSurjective f hf`,
so `P.Ring = MvPolynomial (Fin n) R` and `P.ker = I`.  By
`Algebra.Extension.subsingleton_h1Cotangent` it suffices to show that the conormal map
`d : I/I² → Ω_{P/R} ⊗_P A` is injective, equivalently that its base change to the residue
field `κ = κ(A)`,

```
    P.cotangentComplex.baseChange κ : κ ⊗_A (I/I²) → κ ⊗_A (A ⊗_P Ω_{P/R})
```

is injective, equivalently that `P.cotangentComplex` admits an `A`-linear retraction.

The argument is a contradiction.  The conormal module `N = I/I²` is a *finite* `A`-module, so
Krull's intersection theorem `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing` detects a nonzero
kernel class `ξ` at a finite truncation level `n₀`: there is an `n₀` with `ξ ∉ 𝔪^{n₀}·N`.  A
length-one simple quotient `q : N ↠ V ≅ κ` with `q(ξ) ≠ 0` classifies a residually trivial
length-one square-zero small extension `B'_q ↠ A/𝔪^{n₀+1}` of local Artinian `R`-algebras,
along which the truncation `a : A → A/𝔪^{n₀+1}` lifts exactly when `q ∈ Im(dᵛ)`.  But every
`δ∘d` kills `ξ ∈ ker d` while `q(ξ) ≠ 0`, so no lift exists, contradicting the hypothesis.
Hence `ker d = 0`.  The identification of lifting with the cocycle lying in the image uses the
conormal–Kähler exact sequence `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`
and `Algebra.H1Cotangent.exact_δ_mapBaseChange`, together with formal smoothness of the
polynomial ring `P`.  Splitness over the local ring `A` is the André–Quillen expression of
formal smoothness, and the passage from the retraction to the κ-base-change injectivity is
`IsLocalRing.split_injective_iff_lTensor_residueField_injective`, which needs `P.Cotangent`
finite and `P.CotangentSpace` finite and free — both supplied by `hker` and the polynomial
presentation.

The statement actually proved in the substantive step is that *every* `A`-linear functional
`o : P.Cotangent → κ` on the conormal module factors through `d`, that is `o = δ ∘ₗ d` for
some `A`-linear `δ : P.CotangentSpace → κ`.  Its construction half builds, from `o`, the
classifying extension together with the data linking it back to `o`:

* lift `o` to `õ : I → κ` through `Ideal.Cotangent.lift`; then `õ` is `P`-linear and kills
  both `I²` and `𝔪·I`, the latter because `o` is `A`-linear into `κ`;
* fix `m ≥ 1` with `Ā_m := A/𝔪_A^{m+1}` Artinian local, by
  `isArtinianRing_iff_isNilpotent_maximalIdeal`, and let `P̄_m := P/𝔪^{m+1}` for
  `𝔪 = f⁻¹(𝔪_A)`, which is Artinian local and surjects onto `Ā_m`;
* build the *cocycle-twisted quotient* `B'_o := (P̄_m ⊕ κ)/K` with
  `K := ⟨(ḡ, −õ(g)) : g ∈ I⟩`, an ideal because `õ` is `P`-linear.  Its first projection
  `φ : B'_o ↠ Ā_m` has `ker φ =: J ≅ κ`, square-zero of length one and residually trivial,
  and the reference lift `q₀ : P → B'_o`, `q₀(h) := (h̄, 0) mod K`, satisfies
  `φ ∘ q₀ = a ∘ f` for the truncation `a`.

The bundle also carries the κ-isomorphism `θ : J ≃ₗ[R] κ`, the κ-coordinate of the chosen
`J`-representative, and the *defect link* `θ (q₀ g) = o([g])` for every `g ∈ ker f`, which
holds because `(ḡ, 0) ≡ (0, õ(g)) mod K` and `õ(g) = o([g])`.  The twisting is essential: for
the untwisted `TrivSqZeroExt κ κ` the defect of `q₀` on `I` is forced to be `0`, giving
`δ = 0 ≠ o`.  For the same reason `θ` and the defect link must be built alongside the ring
`B'_o` rather than afterwards — they depend on the concrete `K`, and for a degenerate bundle
such as `B' = B`, `φ = id`, `q₀ = a∘f` one has `q₀ g = 0` for `g ∈ ker f`, so
`θ (q₀ g) = 0 ≠ o([g])` whenever `o ≠ 0`.
-/

/-! ### S1 cocycle-twisted quotient construction (formal sketch)

The construction is `B'_o = (TrivSqZeroExt P̄ κ)/K` (the `Module Pbarᵐᵒᵖ κ` and
`IsCentralScalar` friction is
tamed via `opToPbar`, a comm-ring `unop` ring hom).  The sub-lemmas below are the
RingTheory content (II)–(V) together with the defect link. -/
section S1Construct
namespace S1Construct

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing R] [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
  (P : Type u) [CommRing P] [Algebra R P] [IsNoetherianRing P]
  (f : P →ₐ[R] A) (hf : Function.Surjective f)
  (m : ℕ)

section WithO
variable [Algebra P A]
  (o : (Algebra.Extension.ofSurjective f hf).Cotangent →ₗ[A] IsLocalRing.ResidueField A)

end WithO
end S1Construct
end S1Construct

end InfinitesimalLifting
