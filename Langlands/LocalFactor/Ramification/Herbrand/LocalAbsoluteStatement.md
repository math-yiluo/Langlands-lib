# Absolute upper ramification in any characteristic: statements

Worker 988 authors this statement unit for Task 7421. Its six declarations are
Prop-valued definitions in `Langlands.Ramification.Local`. They state the
properties of the general absolute upper filtration of `Herbrand.GeneralAbsolute`
(Task 7403) and of the general inertia of `Galois.Local.AbsoluteDefinitions`
(Task 7404). The p-adic forms of these properties are in
`Herbrand/AbsoluteStatement.lean`. The declarations here are targets for later
proof tasks; nothing here proves them, and none is used as a hypothesis of a
construction. There is no hypothesis on the characteristic.

## Objects and quantifiers

`K` is a nonarchimedean local field of either characteristic,
`[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
and `Ω` is a specified separable closure,
`[Field Ω] [Algebra K Ω] [IsSepClosure K Ω]`, in an independent universe. Write
`G = Ω ≃ₐ[K] Ω` with its Krull topology, and:

- `G^v = localAbsoluteUpperRamificationGroup K Ω v`, Task 7403's absolute upper
  group: the intersection, over all finite Galois subextensions, of the preimages
  of the finite upper groups. Every finite level is realized with the spectral
  norm extending the published local norm `LocalGalois.localNormedField K` of `K`
  itself (base `K₀ = K`);
- `L` ranges over all `FiniteGaloisIntermediateField K Ω`;
- `r_L = (absoluteFiniteRestriction K Ω L).toMonoidHom`, the actual restriction
  `G → Gal(L/K)` (`AlgEquiv.restrictNormalHom`); `Gal(L/K)` is finite and
  discrete;
- `G_L^v = localUpperRamificationGroup K L v`, the finite upper group of `L/K`
  for the canonical realization `localTopologicalData K L`; and
  `(G_L)_1 = lowerRamificationGroup (localTopologicalData K L) K 1`, its first
  lower group;
- `I = LocalGalois.SepClosed.absoluteInertia K Ω`, Task 7404's inertia, the
  kernel of the residue projection of `G`;
- `localWildInertia K Ω`, Task 7403's wild inertia, which is by definition
  `(⨆ (v : ℝ) (_ : 0 < v), G^v).topologicalClosure`.

All indices are real numbers. No family of groups, fields or homomorphisms is supplied
by the caller.

## The statements

Page numbers are Serre's printed pages; PDF pages are seven larger.

| Declaration | Assertion | Source or provenance |
| --- | --- | --- |
| `AbsoluteUpperFiniteImage K Ω` | For every `L` and real `v ≥ -1`, `(G^v).map r_L = G_L^v`. | Serre IV §3 Proposition 14, pp. 74–75, and Remark 1, p. 75. Surjectivity onto each finite level is derived from the finite quotient theorem and compactness of the inverse system. |
| `AbsoluteUpperInertia K Ω` | `G^0 = I`. | Serre IV §1 Proposition 1, p. 62 (`G_0` is the inertia group), with the upper numbering of IV §3, p. 74, and Remark 1, p. 75. |
| `AbsoluteUpperLeftContinuity K Ω` | For real `v > -1`, `G^v = ⨅ (w : ℝ) (_ : -1 ≤ w ∧ w < v), G^w`. | Serre IV §3 Remark 1, p. 75, on the domain `[-1, ∞)`. |
| `AbsoluteUpperClosedRightImage K Ω` | For every `L` and real `v ≥ -1`, `((⨆ (w : ℝ) (_ : v < w), G^w).topologicalClosure).map r_L = ⨆ (w : ℝ) (_ : v < w), G_L^w`. | Derived: finite image, continuity of `r_L` into a finite discrete group, and compatibility of subgroup images with suprema. Not a verbatim source statement. |
| `AbsoluteUpperWildInertia K Ω` | `localWildInertia K Ω = ⨅ L, ((G_L)_1).comap r_L`. | Derived from Serre IV §2 Proposition 7 and Corollaries 1–4, pp. 67–68 (`G_1` is a p-group and `G_0/G_1` has order prime to p, so `G_1` is the p-Sylow subgroup of `G_0`), the conventions of IV §3, pp. 73–74, and the closed right image at `0`. |
| `AbsoluteHerbrandArithmetic` | For every `K` and `Ω` as above, in independent universes, the conjunction of the five statements. | Internal organization of the five statements. |

Notes on the individual statements:

- Both image statements assert equality. The construction itself only gives the
  containment `(G^v).map r_L ≤ G_L^v` (Task 7403's
  `absoluteUpperRamificationGroup_map_restriction_le`).
- Left continuity intersects over the restricted interval `[-1, v)`. At
  `v = -1` that interval is empty, and the statement excludes this case. The
  endpoint `G^{-1} = ⊤` is Task 7403's lemma
  `localAbsoluteUpperRamificationGroup_neg_one` and is not restated, as the task
  specifies. Task 7403 also proves `G^w = ⊤` for every `w ≤ -1`. With this
  extension, the restricted formula agrees with Serre's intersection over all
  `w < v`.
- The closure in the right-limit statement is taken in the Krull topology of
  `G`. The positive family is directed, so the supremum is the union. For a
  continuous homomorphism into a finite discrete group, the image of the closure
  of a subgroup is the image of the subgroup.
- At each finite level, there is a positive interval on which `0 < ψ(w) ≤ 1`.
  On it the ceiling lower index is `1`, so the finite positive upper supremum is
  the first lower group `(G_L)_1`. A closed subgroup of the profinite group `G` is
  determined by its images in all finite Galois quotients. With the closed right
  image at `0`, this gives the wild inertia statement. Its two sides are different
  constructions; their equality is a proposition to prove.
- `AbsoluteUpperInertia` compares two independent constructions. `G^0` comes
  from the finite integer rings of the canonical realizations. `I` comes from the
  residue action on the integers of `Ω` (Task 7404). No definitional equality
  is claimed.

## Relation to the p-adic statements

The p-adic module works with `F : PadicField p`, `Ω = AlgebraicClosure F.Carrier`
and the p-adic `absoluteUpperRamificationGroup F v`. Task 7403 defines that group in
place as the general spectral construction at base `K₀ = Padic p`: every finite
level uses the spectral norm extending the norm of `Padic p`. The general
statements here use `localAbsoluteUpperRamificationGroup K Ω`, which is the same
spectral construction at base `K₀ = K`, using the local norm of `K` itself. For
`K = F.Carrier` with the structure of a realization `T : F.TopologicalData`, the
two absolute groups are therefore built from integer rings of finite levels taken
for two different base norms. Both rings are the integral closure of the integers
of `F` in the finite level, so they are equal. That equality is a theorem, not a
definitional unfolding, and so the statements here are not `Iff.rfl`-equivalent to
the p-adic ones. Following the task, the relation is explained in words here, and
no comparison theorem is added.

Apart from this base norm, the statements correspond clause by clause:

- the right-hand sides of `AbsoluteUpperInertia` agree definitionally. For
  `Ω = AlgebraicClosure K` in characteristic zero, Task 7404's
  `SepClosed.absoluteInertia K Ω` unfolds to the characteristic-zero
  `absoluteInertia K`, and the p-adic `F.absoluteInertia T` is that subgroup for
  the instances of `T`. This is the definitional agreement that the residue
  projection module `Galois.Local.ResidueProjectionStatement` checks by `Iff.rfl`;
- the left-hand side of `AbsoluteUpperWildInertia` unfolds definitionally to the
  closed positive upper limit that the p-adic statement writes out. A private
  check file compiled, for arbitrary `K` and `Ω`:

```lean
example (v : ℝ) :
    localAbsoluteUpperRamificationGroup K Ω v =
      ⨅ L : FiniteGaloisIntermediateField K Ω,
        (localUpperRamificationGroup K L v).comap
          (absoluteFiniteRestriction K Ω L).toMonoidHom :=
  rfl

example :
    localWildInertia K Ω =
      (⨆ (v : ℝ) (_ : 0 < v), localAbsoluteUpperRamificationGroup K Ω v).topologicalClosure :=
  rfl
```

- the p-adic `AbsoluteUpperInertia F T` quantifies over realizations `T`. The
  general statement takes the structure of `K` as instances, and its universal
  form `AbsoluteHerbrandArithmetic` quantifies over all such structures. The p-adic
  `AbsoluteUpperCanonicalInertia` (the canonical realization) and
  `AbsoluteUpperEndpoint` (`G^{-1} = ⊤`, a published lemma) have no general
  counterpart.

So once the general statements are proved, the p-adic ones follow at
`K = F.Carrier` (with the instances of `T`) and
`Ω = AlgebraicClosure F.Carrier`, after the base-norm comparison of the finite
integer rings. In characteristic zero `AlgebraicClosure F.Carrier` is a separable
closure by `IsSepClosure.of_isAlgClosure_of_perfectField`.

| General statement (`Langlands.Ramification.Local`) | P-adic counterpart (`Langlands.Ramification.Padic`) |
| --- | --- |
| `AbsoluteUpperFiniteImage K Ω` | `AbsoluteUpperFiniteImage F` |
| `AbsoluteUpperInertia K Ω` | `AbsoluteUpperInertia F T` (all `T`); also `AbsoluteUpperCanonicalInertia F` |
| none (published lemma `localAbsoluteUpperRamificationGroup_neg_one`) | `AbsoluteUpperEndpoint F` |
| `AbsoluteUpperLeftContinuity K Ω` | `AbsoluteUpperLeftContinuity F` |
| `AbsoluteUpperClosedRightImage K Ω` | `AbsoluteUpperClosedRightImage F` |
| `AbsoluteUpperWildInertia K Ω` | `AbsoluteUpperWildInertia F` |
| `AbsoluteHerbrandArithmetic.{uK, uΩ}` | `AbsoluteHerbrandArithmetic.{u}` |

The general and p-adic declarations have the same leaf names in different
namespaces. In the general version `Ω` is any separable closure, not only
`AlgebraicClosure K`.

## Declaration audit

The complete unapplied types were printed with universes. Each of the five
components takes `K`, `[Field K]`, `[ValuativeRel K]`, `[TopologicalSpace K]`,
`[IsNonarchimedeanLocalField K]`, `Ω`, `[Field Ω]`, `[Algebra K Ω]`,
`[IsSepClosure K Ω]` and returns `Prop`. The finite-subextension and real-index
quantifiers are inside the components. `AbsoluteHerbrandArithmetic` has type
`Prop` with the two universe parameters `uK`, `uΩ`; the quantifiers over `K`, `Ω`
and their instances are inside it.

## Source

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg, GTM 67,
Springer (1979): Chapter IV, hypotheses p. 61 (PDF 68); §1 Proposition 1, p. 62
(PDF 69); §2 Proposition 7 and Corollaries 1–4, pp. 67–68 (PDF 74–75); §3
conventions, Proposition 14 and Remark 1, pp. 73–75 (PDF 80–82). Registered source
`serre-1979-local-fields`, file
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`. Chapter IV
assumes only a complete discretely valued field with separable residue extensions.
The residue fields here are finite, so the cited results apply in both
characteristics. The properties needed by the route (surjection onto every finite
level, inertia at `0`, wild inertia as the closure of the positive members) are
listed in the operator plan `operator-external-inputs-plan-2026-11-16`, §4.2,
lines 513–570.

This unit does not edit the published p-adic statements, the proof modules, or
the definition modules of Tasks 7403 and 7404.
