# Actual derivative level and homogeneity

This module defines the derivative level and homogeneity of actual smooth
mirabolic representations, then defines homogeneity of positive-rank general
linear representations through actual mirabolic restriction. It composes the
published determinant inverse-half normalized minus functors. Their comparison
with the original Haar-modulus normalization remains a separate proof obligation.

## Sources and provenance

The registered original `zelevinsky-1980-induced-ii`, Zelevinsky,
*Induced representations of reductive p-adic groups II* (1980), defines level
in §4.3, printed p.184 (one-based PDF page 21), homogeneity in §5.1, and general
linear homogeneity through mirabolic restriction in §5.2, printed p.187
(PDF page 24). Its SHA256 is
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The relevant definition pages were read and visually checked. No applicable
erratum was found in the project literature index or source-specific errata.

The derivative formula and changing ranks follow the registered original
`bernstein-zelevinsky-1977-induced-i`, Bernstein–Zelevinsky,
*Induced representations of reductive p-adic groups I* (1977), §3.5 and its
footnote (2), printed p.452 (PDF page 13), and §4.3, printed p.454
(PDF page 15). Its SHA256 is
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
These passages were read and the derivative/rank formulas visually checked.
No applicable registered erratum was found.

The source defines level using the largest nonzero derivative order and
homogeneity using equality of levels for every nonzero invariant subspace.
The finite-maximum implementation, its zero default in the absence of any
nontrivial derivative, equality transports, source-rank/order wrapper, and
helper equations are internal Lean packaging. No assertion that every nonzero
representation has a nontrivial derivative is supplied by this packaging.

## Parameters and ranks

Every interface uses implicit `{p : ℕ} [Fact p.Prime]` and
`{F : PadicField.{uF} p}`, explicit `T : F.TopologicalData`, and
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`.
The supplied topology `T.topology` is installed throughout. Carriers remain in
`Type uV`, independently of the field universe `uF`; the categories are
`SmoothRep.{0,uF,uV} ℂ`.

Here `GeneralLinear.mirabolic N F.Carrier` is the actual matrix subgroup
`P_(N+1)` of `GL_(N+1)`. The published
`mirabolicDerivative T ψ n j` applies `j` successive `Φ⁻` functors followed
by `Ψ⁻`, with source `mirabolic (n+j)`, target `GL_n`, and order `j+1`.

## The concrete order wrapper

`mirabolicRankCast T h`, for `h : a = b`, is equality elimination of the
identity functor between the mirabolic categories at ranks `a` and `b`.
Its object equation is the category cast along `h`, and its morphism equation
is heterogeneous equality with the original morphism. At equal ranks it is
the identity functor; it also preserves a subsingleton carrier.

For `hk : 0 < k ∧ k ≤ N+1`, `mirabolic_rank_eq_of_order hk` proves
`N = (N+1-k)+(k-1)`. The actual functor is

```lean
mirabolicDerivativeOfOrder T ψ N k hk =
  mirabolicRankCast T (mirabolic_rank_eq_of_order hk) ⋙
    mirabolicDerivative T ψ (N+1-k) (k-1)
```

Thus its source is `SmoothRep ℂ (mirabolic N F.Carrier)` and its target is
`SmoothRep ℂ (GeneralLinear (N+1-k) F.Carrier)`. This equation is equality
of functors. The accompanying object and morphism equations expose the same
composite, and `mirabolicDerivativeOfOrder_proof_irrel` removes dependence on
the proof `hk`. There is no derivative at an invalid order in this wrapper.

Order one is the published `Mirabolic.psiMinus T N`. At `N=0`, the only
valid order is one, giving the actual `P₁ → GL₀` functor
`Mirabolic.psiMinus T 0`. At top order `N+1`, the explicit target transport
`generalLinearRankCast T (Nat.sub_self (N+1))` identifies the result with
`mirabolicDerivative T ψ 0 N`, after source transport along `N = 0+N`.
All these identifications include morphisms.

## Level and its elementary laws

`HasNonzeroDerivative T ψ A k : Prop` means that some proof of
`0 < k ∧ k ≤ N+1` exists and the carrier of the actual order-`k` derivative
of `A` is nontrivial. For any supplied valid-order proof,
`hasNonzeroDerivative_iff` identifies this predicate with that derivative's
carrier nontriviality. Proof irrelevance makes the choice of proof immaterial.

`level T ψ A : ℕ` is `Nat.findGreatest (HasNonzeroDerivative T ψ A) (N+1)`.
It is therefore zero when no valid derivative has a nontrivial carrier. This
is explicit internal totalization, including for the zero representation.
The bound is `0 ≤ level T ψ A ≤ N+1`; the lower inequality follows from its
natural-number type, and `level_le` proves the upper inequality.

For `0 < k`, `level_eq_iff` says that `level T ψ A = k` exactly when
`k ≤ N+1`, the order `k` predicate holds, and it fails at every larger order
at most `N+1`. `le_level_of_hasNonzeroDerivative` bounds every such order by
the level. `level_pos_iff` characterizes positivity by existence of some
nontrivial valid derivative. `level_eq_zero_iff` characterizes zero by absence
of nontrivial carriers at all valid orders. These proofs use Mathlib's finite
maximum lemmas and the valid-order predicate; none proves derivative detection.

`level_eq_zero_of_subsingleton` proves that a zero carrier has level zero.
Its proof first shows by induction that `phiMinusIterate` preserves a
subsingleton carrier: each actual quotient map `phiMinusQuotient` is
surjective, so its codomain is subsingleton when its domain is. The final
`psiMinusQuotient` gives the same conclusion for `mirabolicDerivative`.
Equality transport then gives it for the order wrapper. Nontriviality of any
such carrier contradicts subsingletonness, giving the maximum-zero criterion.
Twisting does not change these quotient carriers. This proof uses no exactness.

## Actual subrepresentations and homogeneity

The principal declaration is `Langlands.Derivative.IsHomogeneous`:

```lean
IsHomogeneous T ψ A ↔
  ∀ U : Subrepresentation A.representation,
    U ≠ ⊥ → level T ψ (SmoothRep.subrepresentation A U) = level T ψ A
```

`isHomogeneous_iff` is its defining equation. The existing
`SmoothRep.subrepresentation A U` has the actual submodule carrier
`U.toSubmodule`; the action on `v` is the restriction of
`A.representation g v.val`, with membership certified by invariance of `U`.
Its smoothness comes from transfer along the injective actual inclusion.
There is no abstract representative or separate homogeneity hypothesis bundle.

`isHomogeneous_of_subsingleton` proves zero-carrier homogeneity vacuously.
Every invariant submodule of a subsingleton ambient module is bottom, since
every vector equals zero; hence the condition `U ≠ ⊥` is impossible.

For `A` on `GL_(N+1)`, the defining equation is

```lean
IsGeneralLinearHomogeneous T ψ A ↔
  IsHomogeneous T ψ ((generalLinearRestriction T N).obj A)
```

`isGeneralLinearHomogeneous_iff` proves it by reflexivity. This restriction
is the published actual subgroup pullback and keeps the carrier and linear
maps. Consequently a zero-carrier general linear representation also satisfies
the predicate. The interface is only at positive rank `N+1`: it introduces no
predicate for `GL₀` and asserts no mirabolic group of rank zero.

## Normalization and dependency boundary

The iteration uses the published minus functors with their explicit
`|det|^(-1/2)` twists at each step. Identifying those characters with the
source Haar-modulus normalizations is a separate proof obligation. The source
citations do not supply that missing comparison.

The transitive project import closure was audited: its 52 existing modules
are the actual local-field, matrix-group, smooth representation, twist,
coinvariant/localization, elementary Whittaker-model and derivative-iteration
infrastructure. Their import edges contain no classification or socle results.
The extra subrepresentation import uses only the already independent actual
category and injective/surjective smoothness-transfer modules. Existing Library
pairs are not edited.

No positive-level existence theorem, derivative detection, exactness, plus-model
embedding, highest-layer essentiality, lattice isomorphism, finite-length,
irreducibility or ordered-product homogeneity assertion is made here. The unit
uses no ordered-socle existence or exhaustion, analytic segment classification,
special-head product irreducibility or exhaustion, generic product uniqueness,
ordered special-head existence or conversion, quotient coverage, tempered block
uniqueness, square-integrable classification or exhaustion, regular exhaustion,
or forward special-segment essential square-integrability conclusion, proof
successor or transitive dependency.
