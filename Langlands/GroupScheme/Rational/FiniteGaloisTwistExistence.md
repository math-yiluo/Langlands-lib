# Proof of the existence of finite-Galois twisted forms

Author: Worker 1534.

This module proves the published proposition
`Langlands.GroupScheme.FiniteGaloisTwistExistenceStatement.{u}` from
`Langlands.GroupScheme.Rational.FiniteGaloisTwistExistenceStatement`, in
arbitrary universe `u`. The main theorem is

```lean
theorem finiteGaloisTwistExistence : FiniteGaloisTwistExistenceStatement.{u}
```

It uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. The statement module is imported unchanged. The proof adds no
hypothesis. In particular `A` and `G` need no finiteness, smoothness or
reductivity. The proof uses neither `FiniteDimensional K L` nor `IsGalois K L`
directly; it only passes them to the published object-descent theorem, which
takes them as instance arguments.

The module imports the statement, `Langlands.GroupScheme.Descent.AffineEffectivityProof`
(published finite-Galois effective descent), `Langlands.AbelianScheme.KernelBaseChange`
(points of a base change, `baseChangePointsEquiv`) and
`Langlands.GroupScheme.Multiplicative` (Yoneda for group schemes: `isoOfPoints`,
`hom_ext_points`). It sets `maxHeartbeats 800000` and the three `backward.*`
transparency options used elsewhere in the Library's descent modules.

## Route

The classical argument (Milne 2017, 3.37/3.43; Steinberg 1965, §10, both cited
in the statement Markdown) twists the Galois action on `G_L` by the cocycle and
takes the fixed points. The Lean proof follows the same idea, but goes through
the Library's Čech descent of actual group schemes instead of Galois actions:

1. From `a` and `ξ` build a *point-level* overlap datum on `G`: for every test
   `Z` over `K` and every two points `b c : Z ⟶ U` of the cover
   `U = Spec L → Spec K`, the automorphism `g ↦ a.act (ξ(c,b)) g` of `G(Z)`.
2. Turn it into an actual Čech descent datum `Descent.Datum p (p^*G)` on the
   base change `p^*G` of `G` to `Spec L`, with `p = Spec(L) → Spec(K)`.
   The overlap isomorphism comes from Yoneda (`isoOfPoints`). The cocycle
   condition is checked on points.
3. Descend it with the published
   `affineGroupSchemeFiniteGaloisObjectDescent`. This gives an affine group
   scheme `H` over `K`, an isomorphism `ψ : p^*H ≅ p^*G` and the compatibility
   of `ψ` with the canonical datum of `H` and the datum of step 2.
4. Read `ψ⁻¹` on points of the cover as a `LocalGroupIso G H U`. The
   compatibility of step 3 gives exactly the discrepancy condition.

No Galois group, no decomposition of `Spec L ×_K Spec L` and no semilinear
action appears; the finite Galois hypothesis is used only through the
published descent theorem.

## Declarations

All auxiliary declarations are in the namespace
`Langlands.GroupScheme.PointDescent`. Throughout, `p : S ⟶ B` is an arbitrary
morphism of schemes and `G : GroupScheme B`; only the main theorem specialises
to field spectra.

### Points of base changes

- `pointsCongr j X` precomposes points of `X` with an isomorphism `j` of test
  objects in `Over B`. `pointsIso e T` postcomposes with an isomorphism `e` of
  group schemes. Both are multiplicative equivalences.
  `comp_hom_comp_inv` and `comp_inv_comp_hom` are its two inverse laws.
- `baseChangePoints p X V k h` identifies points of `p^*X` over `V : Over S`
  with points of `X` over `Over.mk k`, for any `k : V.left ⟶ B` with
  `V.hom ≫ p = k`. It is the published `baseChangePointsEquiv` followed by
  `pointsCongr` along the identity of `V.left`. The free choice of `k` lets
  the later lemmas rewrite structure maps without transport.
  `baseChangePoints_left` computes its underlying morphism.
  `baseChangePoints_naturality` and `baseChangePoints_symm_naturality` give
  naturality along `t : V' ⟶ V` and a map `τ` over `B` with `τ.left = t.left`.
- `iteratedPoints p G r W k h` does the same for an iterated base change
  `r^*(p^*G)` with `r : T ⟶ S` and `W : Over T`. It has the analogous lemmas
  `iteratedPoints_left` and `iteratedPoints_naturality`, and three
  comparison lemmas:
  - `iteratedPoints_comparison`: compatibility with the published
    `Descent.pullbackComparison` isomorphism `q^*(f^*X) ≅ r^*X` for
    `q ≫ f = r`;
  - `iteratedPoints_map`: compatibility with a base-changed homomorphism
    `r^*f` for `f : p^*Y ⟶ p^*G` (via the published `baseChangePointsEquiv_comp`);
  - `iteratedPoints_canonicalOverlap`: the published canonical overlap
    isomorphism `Descent.canonicalOverlap p G` does not move points of `G`
    (via `Descent.canonicalOverlap_fst`).

### The point-level datum and the Čech datum

- `cover p` is `Over.mk p`.
- `PointOverlap p G` is a structure: for every test `Z : Over B` and two
  points `b c : Z ⟶ cover p`, a multiplicative equivalence
  `toFun b c : G(Z) ≃* G(Z)`, natural in `Z`, with
  `toFun c d ∘ toFun b c = toFun b d`.
- `firstPoint` and `secondPoint` are the two projections of a point of the
  double overlap `Descent.Overlap p = S ×_B S`, as points of the cover.
  `overlap_condition` is the pullback square.
- `overlapPoints φ W` is the composite, on points over a test
  `W : Over (Descent.Overlap p)`, of `iteratedPoints` along `fst`, the
  automorphism `φ.toFun (firstPoint) (secondPoint)` of `G`-points, and the
  inverse of `iteratedPoints` along `snd`. `iteratedPoints_overlapPoints`
  states this, and `overlapPoints_naturality` proves naturality in `W`.
- `overlapIso φ : Descent.OverlapIso p (p^*G)` is
  `isoOfPoints (overlapPoints φ) …`, the actual isomorphism
  `fst^*(p^*G) ≅ snd^*(p^*G)` with these points.
- `pullHom_overlapIso` computes the pullback `Descent.pullHom q hr hs` of this
  isomorphism along any `q : T ⟶ Descent.Overlap p` on points. On a point
  `x` it is `φ.toFun` at the two points `Z.hom ≫ r` and `Z.hom ≫ s` of the cover.
  The proof unfolds `pullHom` into the two `pullbackComparison` isomorphisms
  and the base change of `overlapIso φ` along `q`, and applies
  `iteratedPoints_comparison` twice and `iteratedPoints_overlapPoints` once.
- `overlapIso_cocycle` proves the Čech cocycle condition
  `Descent.Cocycle (overlapIso φ)`. Both sides are compared with
  `hom_ext_points`. Then the point is pushed through `iteratedPoints` along the
  third projection `p3`, which is injective. `pullHom_overlapIso` for `p12`,
  `p23` and `p13` reduces the identity to `φ.cocycle`.
- `pointDatum φ : Descent.Datum p (p^*G)` packages `overlapIso φ` and
  `overlapIso_cocycle φ`.

### From a solution to local isomorphisms

Let `ψ : p^*H ≅ p^*G` for some `H : GroupScheme B`.

- `localPoints ψ V k h : G(Over.mk k) ≃* H(Over.mk k)` is the inverse of
  `baseChangePoints` for `G`, then postcomposition with `ψ⁻¹`, then
  `baseChangePoints` for `H`. `localPoints_apply` unfolds it,
  `localPoints_naturality` gives its naturality, and `localPoints_congr`
  replaces the lift `V = Over.mk f` by an equal one.
- `localPoints_overlap` is the key computation. Assume `ψ` is compatible with the
  canonical datum of `H` and with `pointDatum φ`, i.e.
  `Descent.Compatible (Descent.canonicalDatum p H) (pointDatum φ) ψ.hom`. Then, over
  every test `W` of the double overlap, `localPoints` along `snd` applied to
  `φ.toFun (firstPoint) (secondPoint) z` equals `localPoints` along `fst`
  applied to `z`. The proof writes `z` as `iteratedPoints` of a point `v`
  along `fst` (surjectivity) and sets `u = v ≫ fst^*(ψ⁻¹)`. Evaluating the
  compatibility square at `u` gives
  `v ≫ overlapIso φ = (u ≫ canonicalOverlap) ≫ snd^*ψ`. The result then follows
  from `iteratedPoints_overlapPoints`, `iteratedPoints_map` and
  `iteratedPoints_canonicalOverlap`.
- `solutionLocalIso ψ : LocalGroupIso G H (cover p)` sends a point
  `b : Z ⟶ cover p` to `localPoints ψ (Over.mk b.left) Z.hom (Over.w b)`.
  Its naturality is `localPoints_naturality`.
- `solutionLocalIso_overlap` says that, under the same compatibility hypothesis,
  `e_c (φ.toFun b c g) = e_b g` for `e = solutionLocalIso ψ`. The proof applies
  `localPoints_overlap` to the test `W = Over.mk (pullback.lift b.left c.left _)`.
  Its two coordinates are `b` and `c`, and `localPoints_congr` identifies
  the two lifts `W.hom ≫ snd = c.left` and `W.hom ≫ fst = b.left`.

### Main theorem

`finiteGaloisTwistExistence` introduces `K L`, the instances, `A`, `G`, the
affineness hypothesis `hG`, `a` and `ξ`, and sets
`p = Spec.map (CommRingCat.ofHom (algebraMap K L))`, so that `cover p` is
literally the cover `U` of the statement. Then:

1. `φ : PointOverlap p G` has `toFun b c = a.pointAut _ (ξ.toFun c b)`.
   Naturality follows from `ξ.naturality` and `a.naturality`. The cocycle law
   `a.act (ξ(d,c)) (a.act (ξ(c,b)) g) = a.act (ξ(d,b)) g` follows from
   `ξ.cocycle d c b` and `a.act_mul_left`.
2. `IsAffineHom (p^*G).X.hom` holds because it is the base change
   `pullback.snd G.X.hom p` of an affine morphism (instance search).
3. `affineGroupSchemeFiniteGaloisObjectDescent K L (p^*G) _ (pointDatum φ)`
   gives a `Descent.Solution s` with `IsAffineHom s.obj.X.hom`.
4. The witnesses are `H = s.obj` and `e = solutionLocalIso s.iso`, with the
   affineness from step 3. For `HasDiscrepancy`, given `b c g`,
   `solutionLocalIso_overlap φ s.iso s.compatible c b g` reads
   `e_b (a.act (ξ.toFun b c) g) = e_c g`, which is the required identity.

## Relation to the sources

The construction is the Čech form of Milne's twisting (Theorem 3.43 via the
descent equivalence 3.36/3.37). The cocycle `ξ` acting through `a` defines a
new descent datum on `G_L`. Its effective descent is the twisted form `H`, and
the identification `ψ⁻¹ : G_L ≅ H_L` read on points is the family `e`. The
Galois-indexed bookkeeping of the sources is replaced by natural point-level
data on all tests over `Spec L ×_K Spec L`, which is the form of the statement.

## What is not proved

- Uniqueness of `H`, or its dependence only on the class of `ξ`, is not proved
  (it is not part of the statement).
- The auxiliary `PointDescent` declarations work over an arbitrary morphism
  `p`, but the module proves effectivity only through the published
  finite-Galois descent theorem; no general fpqc effectivity is claimed.
