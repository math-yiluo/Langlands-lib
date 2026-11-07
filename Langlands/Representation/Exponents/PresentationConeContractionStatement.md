# Uniform contraction of compact subsets of `N(F)` by `C_A^+(ε)`

Authors: Workers 1754 and 1291.

Module: `Langlands.Representation.Exponents.PresentationConeContractionStatement`.
Declaration:
`Langlands.Aubert.General.RepresentedParabolic.PresentationConeContractionStatement.{u}`.
This is a proposition-valued definition. It states a derived formulation of the
`N` compact-containment clause of Renard V.5.2(iii); no proof is supplied.

## Quantifiers and hypotheses

The field universe `u` is arbitrary. The statement quantifies over `k : Type u`
with `[Field k] [ValuativeRel k] [TopologicalSpace k]`
`[IsNonarchimedeanLocalField k] [T2Space k]`. Both characteristics are allowed.
For every group scheme `G` over `Spec k` and `hG : IsConnectedReductive G`,
it installs `hG.isAffineHom` and the topology
`RationalPointFamily.pointTopology` on `rationalPoints G`. It then quantifies
over instances `[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]` for that topology, exactly as in
`LeviJacquetOppositePairingStatement`.

The actual supplied triple consists of group schemes `P`, `M`, `N` over
`Spec k` and maps `p : P ⟶ G`, `m : M ⟶ P`, `n : N ⟶ P`, with precisely
the four triple predicates:

- `IsParabolicSubgroup p`;
- `IsRationalLeviSubgroup m`;
- `LeviSubgroup.IsGeometricUnipotentRadical n`;
- `IsIso (subgroupMultiplication m n)`.

Thus the maps represent `P = MN`, with its rational Levi and geometric
unipotent radical, and the actual multiplication is an isomorphism. These
four proofs are universal hypothesis binders; they do not assert that a triple
has been constructed.

Next come an arbitrary commutative group scheme `A` over `Spec k`, a map
`a : A.toGrp ⟶ M`, and `pres : ParabolicRootPresentation p m a`.
The published compatibility predicate in `pres` includes `IsSplitComponent a`,
a maximal split torus `i : T.toGrp ⟶ G`, a generic cocharacter `ν`,
`J ⊆ simpleRelativeRoots i ν`, and a factor `f : A ⟶ T`. It identifies the
all-test images of `p` and `m ≫ p` with the corresponding standard parabolic
and Levi, records a minimal dynamic parabolic contained in `P`, and supplies
a standard cocharacter realizing both images. Its factor equation is
`CommGroupScheme.groupHom f ≫ i = a ≫ m ≫ p`.

The character set used in the statement is exactly

```text
Δ = (fun α => pres.data.f ≫ α) ''
      (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J).
```

This is a set in `characterLattice A`, the restrictions of the simple roots
outside `J`, with exactly the encoding in
`LeviJacquetOppositePairingStatement`.

## Conclusion and cone convention

For every `C : Set (rationalPoints G)` with `IsCompact C` and
`C ⊆ pointImage (n ≫ p)`, and every `L ∈ nhds (1 : rationalPoints G)`,
there is a real `ε > 0` such that for every
`t ∈ CocharacterUniformizer.CAepsilon k A Δ ε` and every `c ∈ C`,

```text
rationalPoints.map (a ≫ m ≫ p) t * c *
  (rationalPoints.map (a ≫ m ≫ p) t)⁻¹ ∈ L.
```

In particular, `ε` may depend on the geometric data, the presentation, `C`
and `L`, but works simultaneously for all these `t` and `c`. The compact
set need not be a subgroup, and the neighbourhood need not be open or compact.
The displayed conjugation direction is `t c t⁻¹`.

The published `CocharacterUniformizer.CA k A` is the image of the actual
cocharacter lattice evaluated at the Library's fixed field uniformizer.
`CAepsilon k A Δ ε` consists of the elements of this image with
`characterNorm k A α t < ε` for every `α ∈ Δ`. The norm is the published
normalized rational-character norm `|α(t)|_k`. There is no additional
norm-at-most-one condition. No new uniformizer or coordinates are supplied
as hypotheses. Empty `Δ`, rank zero, and `P = G` are not excluded.

## Source and derived provenance

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
V.5.2, Théorème (citing [24], 2.1), printed p.123 / PDF p.129,
fixes `P_∅`, `A_∅`, `K_0` and supplies a neighbourhood basis of compact
open subgroups `K` with simultaneous Iwahori decompositions for standard
parabolics. Its part (iii) says that for each compact `Γ ⊆ N` there is
`ε > 0` such that

```text
Γ ⊆ m⁻¹ K_N m   for every m ∈ C_A^+(ε),   where K_N = K ∩ N.
```

V.3.22–V.3.23, printed p.117 / PDF p.123, define
`A^+(ε) = {a ∈ A_M | |α(a)|_F < ε for every α ∈ Δ(P)}`
and `C_A^+(ε) = C_A ∩ A^+(ε)`. These are the cone inequalities used here.

The provenance is **derived**, for two reasons:

- For a prescribed ambient neighbourhood `L`, choose a subgroup `K` of the
  source's basis with `K ⊆ L`. The source inclusion is equivalent to
  `m Γ m⁻¹ ⊆ K_N`, hence implies containment in `L`. Conversely, apply
  the neighbourhood formulation to the ambient neighbourhood `L = K`.
  The image of `A` lies in `M`, which normalizes `N`, so the resulting
  conjugates are in `N` as well as `K`, and therefore in `K_N`. This
  explains equivalence with the compact-containment clause for each
  standard parabolic and its split component. `K_N` itself is not used
  as an ambient neighbourhood.
- The supplied `p`, `m`, `n` are arbitrary actual maps. Instead of requiring
  them to belong to one previously fixed standard family, the compatible
  presentation records the standard parabolic and Levi images for its own
  torus and root data. Its restricted roots supply `Δ(P)`. This organizes
  the source's choice of standard coordinates around the specified maps.
  It neither asserts that every specified triple has a presentation nor
  proves independence between presentations.

The structural comparison of the presentation's relative-root conventions
with the source, identification of the supplied radical in that presentation,
and the uniform contraction argument remain obligations for a proof. The
documentation explains the intended mathematical reformulation; it is not a
Lean proof of those comparisons or of the defined proposition.

VI.9.1, Remark 3 and its proof, printed pp.197–198 / PDF pp.203–204,
explicitly invoke V.5.2 for uniform compact containment (there written for
`t ∈ A^+(ε)`). This is the geometric input needed by the later
`C_A^+(ε)` pairing formula (VI.9.6.5). The present statement retains only
the published `CAepsilon` range.

Only the `N` compact-containment clause of V.5.2(iii) is stated here.
The opposite radical, exhaustion by powers, the simultaneous basis and
cofinality clauses, and all stabilization and representation-theoretic
conclusions retain their separate statement and proof obligations.
