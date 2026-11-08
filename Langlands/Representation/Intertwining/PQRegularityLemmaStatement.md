# The `PQ`-regularity lemma for represented parabolics (Renard VII.3.3)

Author: Worker 6. Module `Langlands.Representation.Intertwining.PQRegularityLemmaStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. The module contains one **statement**: the closed `Prop`-valued definition `PQRegularityLemmaStatement` (universe parameters `u, v`), a conjunction of three parts. It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated **9 July 2026**:

- VII.3.3, the ideals `I_σ`, `I^{PQ}_σ`, `I^{Q,w̄}_σ`, the Lemma and its proof, printed pp.233–235 / PDF pp.239–241;
- VII.3.1–VII.3.2, the Bruhat order, the support subspaces and the reformulated geometric lemma, printed pp.232–233 / PDF pp.238–239;
- VI.5.1, the geometric lemma, from printed p.161 / PDF p.167.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Worker 6 read PDF pages 238–241.

The setting is two parabolic subgroups `P` and `Q` of `G` with the same Levi factor `M`, and a smooth representation `(σ, E)` of `M`. Renard restricts `σ` to the split component `A_M` and extends it to the group algebra `ℂ[A_M]`. He then defines

- `I_σ = ker σ|_{ℂ[A_M]}`,
- `I^{PQ}_σ = ker [(r_Q^G ∘ i_P^G / F^{<1̄}_{PQ})(E)]|_{ℂ[A_M]}`,
- `I^{Q,w̄}_σ = ker [w ∘ r^M_{M∩w·Q}(E)]|_{ℂ[A_M]}` for `w̄ ∈ W_M \ W_G / W_M`.

The Lemma reads: "Les propriétés suivantes sont équivalentes : (i) `I_σ + I^{PQ}_σ = ℂ[A_M]` ; (ii) `I_σ + ⋂_{w̄<1̄} I^{Q,w̄}_σ = ℂ[A_M]`. De plus, (i) ou (ii) impliquent : (iii) `∀ w̄ < 1̄, Exp(A_M, σ) ∩ Exp(A_M, w ∘ r^M_{M∩w·Q}(σ)) = ∅`. Réciproquement, (iii) implique (i) et (ii) si `(σ, E)` est de longueur finie." Renard then calls `σ` `PQ`-regular when one of the first two conditions holds.

## Published objects used

From [PQRegularity](PQRegularity.md) (module `Langlands.Representation.Intertwining.PQRegularity`):

- `Geometric.BruhatLT (pointImage p) (pointImage q) w w'`, the strict Bruhat relation on actual double cosets: `P w Q ⊆ closure (P w' Q)` and `w ≠ w'`;
- `parabolicDoubleCosets p q`, the actual double cosets `P(F) \ G(F) / Q(F)`, and `identityParabolicDoubleCoset p q`, Renard's `1̄`;
- `splitComponentKernel l hl a σ`, Renard's `I_σ`;
- `IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ`, condition (i): `I_σ ⊔ I^{PQ}_σ = ⊤`, where `I^{PQ}_σ` is the published `pqRegularityKernel`;
- `pieceSplitComponentKernel a D σ`, the kernel of the `A(F)` action on the full graded piece `D.pieceFunctor.obj σ` of an intersection datum `D`.

From [RepresentedGeometricLemmaStatement](../Geometric/RepresentedGeometricLemmaStatement.md): `GeometricLemmaIntersectionDatum p l r … q lQ rQ … z`, the intersection data at a point `z` of `G(F)`, and its `pieceFunctor`. With `L = M` this is the graded piece `i^M_{Q'} ∘ ι ∘ r^M_{P'}`, Renard's `i^M_{M∩w⁻¹·P} ∘ w ∘ r^M_{M∩w·Q}`, valued in representations of `M(F)`.

From [ArbitraryParabolicInduction](../Exponents/ArbitraryParabolicInduction.md): `groupExponents ha σ`, Renard's `Exp(A_M, σ)`, applied with the group `M` and its split component `a`. From [SplitComponentWeights](../Exponents/SplitComponentWeights.md): `IsGeneralizedWeight π ι χ hι`, which holds when `χ` has open kernel and the generalized weight space of `χ` in `π` is nonzero. `groupExponents ha σ` is by definition the set of `χ` with `IsGeneralizedWeight σ.representation (rationalPoints.map a) χ _`.

From [Basic](../Category/Basic.md): `SmoothRep.HasFiniteLength`, finite composition length over the group algebra.

## Lean statement

`PQRegularityLemmaStatement` quantifies over:

- a nonarchimedean local field `k : Type u` (`[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`) and a connected reductive `G` over `Spec k`, with the canonical topology on `G(F)`, and `[LocallyCompactSpace (rationalPoints G)]`, `[NonarchimedeanGroup (rationalPoints G)]`;
- represented parabolics `P = MN` (`p`, `l`, `r` with `hp`, `hl`, `hr`, `hmul`) and `Q = MU` (`q`, `lQ`, `rQ` with `hq`, `hlQ`, `hrQ`, `hmulQ`) that share the Levi scheme `M`;
- a proof of `l ≫ p = lQ ≫ q`: the two Levi embeddings of `M` in `G` agree, so `M` is a common Levi factor of `P` and `Q`, as in Renard;
- a commutative group scheme `A` with `a : A.toGrp ⟶ M` and `ha : IsSplitComponent a`, so `A` is Renard's `A_M`. The topology on `M(F)` is the published `leviPointTopology l hl`, and the topology on `A(F)` is `RationalPointFamily.splitComponentPointTopology ha`;
- a smooth representation `σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)`;
- representatives `z : parabolicDoubleCosets p q → rationalPoints G`, with `DoubleCoset.mk (pointImage p) (pointImage q) (z w) = w` for every `w`;
- a family `D` that assigns, to every double coset `w` with `h : BruhatLT … w 1̄`, an intersection datum `D w h` at `z w`.

The conclusion is the conjunction of three parts. Write `w < 1̄` for `Geometric.BruhatLT (pointImage p) (pointImage q) w (identityParabolicDoubleCoset p q)` and `Exp(D w h)` for the set `{χ | IsGeneralizedWeight ((D w h).pieceFunctor.obj σ).ρ (rationalPoints.map a) χ _}`.

1. **(i) ⟺ (ii).** `IsPQRegular … a σ` holds if and only if `splitComponentKernel l hl a σ ⊔ ⨅ (w) (h : w < 1̄), pieceSplitComponentKernel a (D w h) σ = ⊤`.
2. **(i) ⟹ (iii).** If `IsPQRegular … a σ`, then for every `w` and every `h : w < 1̄`, `Disjoint (groupExponents ha σ) (Exp(D w h))`.
3. **(iii) ⟹ (i) in finite length.** If `σ.HasFiniteLength` and the disjointness of part 2 holds for every `w < 1̄`, then `IsPQRegular … a σ`.

The ideals live in `MonoidAlgebra ℂ (rationalPoints A.toGrp)`, Renard's `ℂ[A_M]`. Supremum and infimum of ideals of a commutative ring are their sum and intersection, so `⊔` is Renard's `+`, `⨅` is his `⋂`, and `= ⊤` is `= ℂ[A_M]`. Disjointness of two sets is the empty intersection of (iii).

## Provenance and departures from the source

The provenance is derived. The statement follows the Lemma clause by clause, with these differences.

- **Which conditions are stated.** Renard states (i) ⟺ (ii), "(i) or (ii) implies (iii)" and "(iii) implies (i) and (ii) in finite length". Since `IsPQRegular` is (i), part 1 together with parts 2 and 3 gives all of these.
- **Double cosets.** Renard indexes the double cosets by `W_M \ W_G / W_M` and writes `w̄ < 1̄` for the Bruhat order on that set. The statement works with the actual double cosets `P(F) \ G(F) / Q(F)` and the closure relation of [PQRegularity](PQRegularity.md), as the definitions do. The identification through V.4.5/V.4.7 is not formalized.
- **Full graded pieces.** Renard defines `I^{Q,w̄}_σ` and the exponent sets in (iii) on `w ∘ r^M_{M∩w·Q}(σ)`, with no outer induction. The statement uses the full graded piece `i^M_{M∩w⁻¹·P} ∘ w ∘ r^M_{M∩w·Q}(σ)` of the intersection datum. That piece is a representation of `M(F)`, so `A(F)` acts on it through `rationalPoints.map a`; the published intersection datum does not record that `A_M` lies in `M ∩ w⁻¹·M`. For the kernels, Renard's proof (printed p.234 / PDF p.240) identifies the two because parabolic induction is faithful. For the exponents, `A_M` is central in `M`, so it acts on an induced function pointwise through the inducing representation (the modulus character is trivial on `A_M`). Hence the generalized weight spaces of the full piece are nonzero for exactly the same characters. Neither identification is formalized.
- **Representatives and intersection data.** Renard's objects depend only on `w̄`. The statement holds for every choice of representatives `z` and every choice of intersection data `D` at them. If some `w < 1̄` has no intersection datum at `z w`, the quantification over `D` is empty and the statement says nothing for that `z`. The published [RepresentedGeometricLemmaStatement](../Geometric/RepresentedGeometricLemmaStatement.md) asserts as a conclusion that representatives with intersection data exist, so the statement is not vacuous once that lemma is proved. This module does not use that conclusion.
- **Standard Levi.** Renard assumes `M` standard and `P`, `Q` semi-standard, and says that this restriction is "aucunement essentielle, mais de pure commodité". The statement does not assume it.
- **Finite length.** Finite length is assumed only in part 3, as in the source. Renard notes that the inclusions used for (i) ⟹ (iii) do not need it.

The Lemma's definition of `PQ`-regularity as "(i) or (ii)" is the published `IsPQRegular` (condition (i)); part 1 is the equivalence that makes the two readings agree.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Intertwining.PQRegularity` | `Geometric.BruhatLT`, `parabolicDoubleCosets`, `identityParabolicDoubleCoset`, `splitComponentKernel`, `IsPQRegular`, `pieceSplitComponentKernel`; through it, `GeometricLemmaIntersectionDatum` and `pieceFunctor` |
| `Langlands.Representation.Exponents.ArbitraryParabolicInduction` | `groupExponents`; through it, `IsGeneralizedWeight` and `IsSplitComponent` |
| `Langlands.Representation.Category.Basic` | `SmoothRep`, `SmoothRep.HasFiniteLength` |
