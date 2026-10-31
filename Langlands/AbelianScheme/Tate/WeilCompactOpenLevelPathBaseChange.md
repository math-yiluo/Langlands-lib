# Base change and geometric-point comparison of actual Weil level towers

Author: Worker 142.

This module assembles the actual Weil fixed-level base-change/path square
into a square of compact-open tower morphisms. It constructs the diagonal
natural transformation, proves path independence and component injectivity,
and constructs a canonical geometric-point version using the proved
existence of geometric paths. The full and prime-to-modulus constructions
have the same meaning.

## Sources and provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura Varieties*
(2001), printed p.18 / PDF p.26, defines the full and away Tate modules and
their rationalizations over the integers. Section III.1, printed
pp.90–92 / PDF pp.98–100, uses pairing-compatible frames, monodromy-fixed
level orbits, base-point independence, level forgetting and right Hecke
translation. The registered source is
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft,
Chapter X section 3, (10.25)–(10.26), printed p.150 / PDF p.154, and
(10.29)–(10.30), printed p.151 / PDF p.155, supplies the conventions for
actual finite-etale fibre functors, different endpoint fields, point
comparison and pullback. The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.

The new natural transformations and their coherence proofs are internal
deductions from the existing actual constructions. Their component square
is [WeilPathBaseChange](WeilPathBaseChange.md). The pointed pullback and
tower transport are those of
[WeilCompactOpenLevelBaseChange](WeilCompactOpenLevelBaseChange.md) and
[WeilCompactOpenLevelTransport](WeilCompactOpenLevelTransport.md).
The geometric-path theorem is described in
[GeometricPathProof](../../AlgebraicGeometry/FiniteEtale/GeometricPathProof.md).
No additional geometric transport or path-existence hypothesis is introduced.

## Actual objects and explicit hypotheses

Let `b : S' ⟶ S` be a scheme morphism, with both bases quasi-separated,
and let `A/S` be an actual abelian scheme. Put `A' = (baseChange b).obj A`.
The actual rational algebra action `i : D →ₐ[ℚ] End0 A` pulls back to
`i' = (rationalBaseChangeEnd b A).comp i`. The actual dual-valued
homomorphism `lam` pulls back by `canonicalDualValuedBaseChange … lam`.
The module retains the named pullback-tensor comparison and coherence
statements, Picard-zero pullback and universal base change, dual-scheme
geometry, Poincare evaluation data on each base, and
`RelativeFiniteWeilTransitionStatement`. It does not prove these inputs.

The rational source is a `D`-module `V` with compatible scalar tower and a
rational bilinear form `ψ`. The coefficient ring is the existing
`Global.FiniteAdeles ℚ`, or `Global.PrimeToFiniteAdeles m`. The full
construction uses one `RationalProfiniteIntegerAdeleComparison h`; the
away construction uses one coupled
`hAway : PrimeToRationalProfiniteIntegerAdeleComparison h m`.
Each comparison is shared between the actual Tate module and its twist
and between the two bases. Rational Tate modules remain rationalizations
over `ℤ` of the actual torsion inverse limits.

Write `s : Spec Ω ⟶ S'` and `t : Spec Ω' ⟶ S'`. The fields may differ.
Explicit finite-fibre witnesses are retained at `s`, `t`, `s ≫ b` and
`t ≫ b`. The construction retains `TorsionFiniteEtaleStatement`,
invertibility of all selected positive torsion orders on both bases, and
finite etaleness of the corresponding actual root kernels `mu S n` and
`mu S' n`. In the full system every positive order is selected; in the
away system only orders coprime to the natural modulus `m` are selected.
For prime `m = p`, this is the prime-to-`p` system.

The index category is `FiniteAdelicScalarExtensionLevel D V ψ` or
`PrimeToScalarExtensionLevel D V ψ m`. Its objects are actual compact
open subgroups of the scalar-extension similitude group. An arrow
`f : K ⟶ L` is a transporter with element `g` and condition
`g⁻¹ K g ≤ L`; its tower map sends a frame orbit to the orbit of
`eta ∘ g`.

Write `T_As`, `T_At` for the actual Weil-compatible towers of `(A, lam, i)`
at `s ≫ b`, `t ≫ b`, and `T_bs`, `T_bt` for those of `(A', lam', i')`
at `s`, `t`. At `K`, these are right `K`-orbit classes of actual compatible
frames fixed by the automorphism group of the actual finite-etale fibre
functor. The compatible-frame predicate existentially quantifies a
trivialization of the actual Tate twist. No roots of unity or twist
trivialization are chosen here. A fixed orbit need not have a fixed frame.
The towers instantiate pairing transport with the published
`rationalWeilGeometricTransport` proof.

## Tower square and diagonal

Given `p : fiberFunctor s hs ≅ fiberFunctor t ht`, let `b_*p` denote
`pathPushforward b hsb htb p`. Let `P_s : T_As ⟶ T_bs` and
`P_t : T_At ⟶ T_bt` be the existing pointed pullback transformations,
and let `E_A(b_*p)` and `E_b(p)` be the existing tower transport
isomorphisms. The theorem
`weilAdelicCompactOpenLevelBaseChange_transport` proves

```text
E_A(b_*p).hom ≫ P_t = P_s ≫ E_b(p).hom.
```

Composition is written in categorical order. The proof uses natural
transformation and function extensionality. At each compact open subgroup
and each fixed class, the resulting equation is precisely
`weilAdelicLevelBaseChange_transport … K.toSubgroup p q`.

`weilAdelicCompactOpenLevelBaseChangeAlongPath p : T_As ⟶ T_bt` is
defined as `P_s ≫ E_b(p).hom`. Its `_app` theorem identifies each component
definitionally with `weilAdelicLevelBaseChangeAlongPath` at
`K.toSubgroup`. Its `_eq` theorem gives the alternate route
`E_A(b_*p).hom ≫ P_t` by symmetry of the tower square.

The `_path_independent` theorem proves equality of the entire natural
transformations from any two supplied paths with the same endpoints.
It reduces by extensionality to the existing fixed-level path-independence
equation. The `_injective` theorem applies the existing diagonal
fixed-level injectivity theorem to every `K`. It neither assumes
surjectivity of the fundamental-group map nor asserts surjectivity of
pullback on fixed orbits.

The `_arrow` theorem is the elementwise naturality square for every
compact-open transporter arrow. Thus it includes level forgetting and,
when `Module.Finite ℚ V` supplies their compact open intersection level,
both existing Hecke legs. No additional finite-dimensionality hypothesis
is required for general transporter naturality. The proofs use the
actual tower maps, with the same right-action order as the existing tower.

## Canonical geometric-point pullback

For this section additionally assume that `S'` is connected and locally
noetherian and both endpoint fields are algebraically closed. The proved
`geometricPathExists s t hs ht` supplies a path. The definition
`weilAdelicCompactOpenLevelGeometricBaseChange : T_As ⟶ T_bt` chooses
one such path and applies the diagonal transformation.

The theorem `_GeometricBaseChange_eq_path` identifies this canonical
transformation with the diagonal for every supplied path. Its proof is
the preceding path-independence theorem. The definition is therefore
independent of the auxiliary path choice. The theorem
`_GeometricBaseChange_eq_transport` identifies it with pointed pullback
followed by the existing canonical geometric comparison on the new base:

```text
P_s ≫ GeometricTransport_b(s,t).hom.
```

This equality holds definitionally because both constructions use the
same proved path-existence theorem. The theorem
`_GeometricBaseChange_injective` specializes the diagonal component
injectivity theorem to the chosen path.

For the last theorem additionally assume that `S` is connected and
locally noetherian. Then
`_GeometricBaseChange_eq_pushed_transport` gives the other canonical route:

```text
GeometricTransport_A(s ≫ b, t ≫ b).hom ≫ P_t.
```

The proof chooses a path on `S'`, rewrites the new canonical map by
`_eq_path`, applies the alternate diagonal formula, and identifies old-base
canonical transport with transport along `b_*p` by the existing
`GeometricTransport_eq_path` theorem. This proves compatibility of pointed
pullback with canonical geometric-point comparison of the actual towers.

Every declaration with prefix `weilAdelicCompactOpenLevel` has its
corresponding construction or theorem with prefix
`weilPrimeToAdelicCompactOpenLevel`, using the restricted orders and the
coupled away scalar comparison above. The away proofs repeat the same
component equations and natural transformation arguments.

This module supplies coherence and canonical point comparison for actual
fixed-orbit towers under the stated geometric and scalar inputs. It does
not assert positivity of `lam`, nondegeneracy of `ψ`, nonempty frame spaces,
or a polarization predicate for an arbitrary dual-valued map. It does not
construct the PEL moduli functor or its representing scheme.
