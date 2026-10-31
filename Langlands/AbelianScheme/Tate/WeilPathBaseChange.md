# Base change and path transport of actual Weil-compatible levels

Author: Worker 142.

This module proves that actual pointed base change commutes with path transport
on Weil-compatible frames and on their monodromy-fixed right orbit classes.
It constructs diagonal frame comparisons and diagonal fixed-level pullbacks.
The latter are injective and independent of the supplied path. Full and away
systems are treated separately, with the same respective scalar comparison on
both bases.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines the full and away Tate inverse limits
and their rationalizations over the integers. Section III.1, printed
pp.90–92 / PDF pp.98–100, uses pairing-compatible frames, monodromy-fixed
level orbits and independence from a geometric base point. The registered
source is `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
Chapter X section 3, (10.25)–(10.26), printed p.150 / PDF p.154, defines
actual finite-etale covers and geometric-fibre functors. Items (10.29)–(10.30),
printed p.151 / PDF p.155, provide the change-of-point and pullback conventions.
The registered source is `edixhoven-vandergeer-moonen-abelian-varieties-draft`,
SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The squares and diagonal maps here are internal deductions from the imported
actual Tate comparisons, compatible-frame constructions and fixed-orbit
constructions. They are not separately quoted theorems in these sources.
The proofs restrict the actual Tate square from
[PathBaseChange](PathBaseChange.md), invert it, and pass to right orbit classes.
The actual pairing transport used by the frame and level definitions is the
published proof `rationalWeilGeometricTransport`, described in
[WeilGeometricTransportProof](WeilGeometricTransportProof.md).

## Geometry and explicit hypotheses

Let `b : S' ⟶ S` be a scheme morphism and let `A/S` be an actual abelian scheme.
Both bases are quasi-separated. Put `A' = (baseChange b).obj A`. The rational
algebra action is an actual map `i : D →ₐ[ℚ] End0 A`, and on `A'` it is
`i' = (rationalBaseChangeEnd b A).comp i`. The given homomorphism `lam`
lands in the constructed dual of `A`; on `A'` the module uses precisely
`canonicalDualValuedBaseChange … lam`. This is the actual dual comparison
from [WeilAlongHomBaseChange](WeilAlongHomBaseChange.md).

The following construction inputs remain explicit: pullback tensor comparison
invertibility and its composition, unit, associativity, left-unitor and symmetry
coherences; Picard-zero pullback and universal base change; dual representability
and `DualSchemeGeometry` on each base; a line bundle and evaluation isomorphism
on each corresponding relative product; and
`RelativeFiniteWeilTransitionStatement`. None is proved by this module.
These are the inputs of the existing actual dual, Weil pairing and frame
base-change constructions.

Let `s : Spec Ω ⟶ S'` and `t : Spec Ω' ⟶ S'`. The fields may differ.
Finite-fibre witnesses `hs`, `ht`, `hsb`, `htb` are explicit at `s`, `t`,
`s ≫ b`, `t ≫ b`. Given
`p : fiberFunctor s hs ≅ fiberFunctor t ht`, write `b_*p` for the actual
`pathPushforward b hsb htb p`. The acting fundamental groups are the actual
automorphism groups of these finite-etale fibre functors.

`htor : TorsionFiniteEtaleStatement` is an explicit theorem input.
For the full system, every positive selected order must be a unit in both
`Γ(S, ⊤)` and `Γ(S', ⊤)`. For the away system, this is required only at
positive orders coprime to the natural modulus `m`. At those same orders,
finiteness and etaleness of the actual root kernels `mu S n` and `mu S' n`
are explicit typeclass hypotheses. They enable the actual Tate and twist
path transports at both bases.

The full comparison `h : RationalProfiniteIntegerAdeleComparison` is shared
throughout. The away case uses one coupled
`hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m`.
The underlying rational Tate module remains the rationalization over the
integers of the actual selected torsion inverse limit.

## Compatible-frame square and diagonal

Write `F'_s`, `F'_t` for the existing `WeilAdelicFrame` spaces of
`(A', lam', i')` at `s`, `t`, and `F_s`, `F_t` for those of `(A, lam, i)`
at `s ≫ b`, `t ≫ b`. These are tensor-algebra-linear frame spaces with the
existing `FormCompatible` predicate for the actual Weil form. A twist
trivialization is quantified existentially in that predicate; no choice of
compatible roots or of a trivialization is introduced here.

Let `B_s : F'_s ≃ F_s` and `B_t : F'_t ≃ F_t` be the actual
`weilAdelicFrameBaseChange` maps. Let `T'_p` and `T_(b_*p)` denote the
existing `weilAdelicFrameTransport` maps, instantiated with the published
geometric Weil transport proof. Then `weilAdelicFrameBaseChange_transport`
proves the square

```text
F'_s  -- T'_p -->  F'_t
 |                  |
B_s                B_t
 |                  |
 v                  v
F_s -- T_(b_*p) --> F_t.
```

The proof removes the form-compatibility proof field by subtype
extensionality and compares the underlying linear equivalences pointwise.
The resulting equation is exactly `rationalBaseChange_transport` on an
actual Tate vector. Thus the geometric square is proved rather than
assumed as compatibility data.

`weilAdelicFrameBaseChange_symm_transport` proves the inverse square:

```text
B_t⁻¹ (T_(b_*p) eta) = T'_p (B_s⁻¹ eta).
```

It applies injectivity of `B_t`, rewrites by the forward square, and cancels
the inverse comparisons.

`weilAdelicFrameBaseChangeAlongPath p : F'_s ≃ F_t` is the composite
`B_t ∘ T'_p`. Its `_apply` theorem identifies it with
`T_(b_*p) ∘ B_s`. The definition needs the new-base transport hypotheses;
the alternate-route theorem also needs the original-base transport
hypotheses. There is no assertion that the frame comparison itself is
independent of `p`.

Every declaration in this section has a parallel declaration with prefix
`weilPrimeToAdelic` for the actual away frame spaces and the ring
`Global.PrimeToFiniteAdeles m`. The proof of the forward square is
`rationalBaseChange_transport` with selection
`fun n => Nat.Coprime n m`; the other proofs follow the same steps.

## Fixed-orbit square

Let `U` be any subgroup of
`ScalarExtensionSimilitudes D V (Global.FiniteAdeles ℚ) ψ`. Compact-open
subgroups are included without an additional topology hypothesis for these
set maps. Write `L_s`, `L_t`, `L'_s`, `L'_t` for the corresponding existing
`WeilAdelicLevel` sets: their elements are right `U`-orbit classes fixed
under the actual fundamental group at the relevant point.

The existing pointed level pullbacks
`P_s : L_s → L'_s` and `P_t : L_t → L'_t` go in the direction opposite
to the forward frame comparisons. On underlying right orbit classes they
are induced by `B_s⁻¹` and `B_t⁻¹`. They restrict original-base fixedness
along the actual fundamental-group map. Neither a fixed representative nor
surjectivity of this group map is required.

Let `E'_p` and `E_(b_*p)` be the existing level-transport equivalences.
`weilAdelicLevelBaseChange_transport` proves

```text
P_t (E_(b_*p) q) = E'_p (P_s q).
```

The proof installs the four actual right actions, monodromy actions and their
commutation instances. Subtype extensionality reduces equality of fixed
levels to equality of their underlying orbit classes. Unfolding the two
existing constructions identifies these with the maps of classes induced
by inverse frame base change and frame transport. Quotient induction
reduces the equality to the inverse frame square above, followed by
`congrArg (RightOrbit.mk U)`. The representative used in quotient induction
is arbitrary; its monodromy fixedness is never asserted.

`weilPrimeToAdelicLevelBaseChange_transport` proves exactly the same square
for an arbitrary subgroup of the away similitude group, with the corresponding
away frame comparisons and actual geometric actions.

## Diagonal pullback, path independence and injectivity

`weilAdelicLevelBaseChangeAlongPath U p : L_s → L'_t` is defined by
`E'_p ∘ P_s`. Its `_apply` theorem gives the alternate formula
`P_t ∘ E_(b_*p)` by symmetry of the fixed-orbit square.

The `_path_independent` theorem says that any two supplied paths from `s`
to `t` give the same entire function `L_s → L'_t`. It applies the existing
`weilAdelicLevelTransport_path_independent` on the new base to the level
`P_s q`, then uses function extensionality. This uses fixedness of orbit
classes, where the change of path acts trivially; it does not trivialize
monodromy on frames or on the Tate twist.

The `_injective` theorem composes injectivity of the existing pointed
pullback with injectivity of the level-transport equivalence. It holds for
an arbitrary scheme morphism with the stated hypotheses. It makes no
surjectivity claim.

The three corresponding theorems for
`weilPrimeToAdelicLevelBaseChangeAlongPath` have the same meaning and proof
for the away system. Prime `m = p` gives the prime-to-`p` case; the Lean
declarations permit any natural modulus.

These are conditional comparisons using supplied paths. They do not prove
path existence. Connectedness, local noetherianity and algebraic closure
can supply geometric paths through the separate published existence
results; they are not needed for the conditional squares. The module does
not assemble an unpointed moduli functor.

The algebra `D`, its compatible rational module `V` and the rational bilinear
form `ψ` remain as general as the existing frame interface. There is no
finite-dimensionality, faithfulness, involution, alternation, nondegeneracy
or frame nonemptiness assertion here. Likewise `lam` is an actual
dual-valued homomorphism; this module does not prove a polarization predicate.
It supplies coherence for the already constructed actual frame and level
spaces under the explicit geometric and scalar dependencies above.
