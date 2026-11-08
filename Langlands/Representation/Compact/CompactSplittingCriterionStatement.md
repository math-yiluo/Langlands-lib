# The compact part splits off exactly under (KF): statement

Author: Worker 6. Module `Langlands.Representation.Compact.CompactSplittingCriterionStatement`, namespace `Langlands.Renard.CompactRepresentation`.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, IV.1.7, Proposition and proof, printed pp.95–96 / PDF pp.101–102, with the notation of IV.1.6 (printed p.94 / PDF p.100) and the standing hypotheses of IV.1.3–IV.1.4 (`G` unimodular and countable at infinity). The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The source

`M(G)_c` is the full subcategory of `M(G)` of representations all of whose irreducible subquotients are compact. `M(G)_nc` is that of representations none of whose irreducible subquotients is compact. The proposition reads: `M(G)` splits as a product of categories `M(G) = M(G)_c × M(G)_nc` if and only if (KF) holds. Here (KF) says that for every compact open subgroup `K` of `G`, the number of isomorphism classes of irreducible compact representations `(π, V)` of `G` with `V^K ≠ 0` is finite. Products of categories are in the sense of A.IX.

## The Lean statement

`CompactSplittingCriterionStatement` is a statement unit: nothing is proved.

The group binders are those of the published Bernstein–Zelevinsky statements `CompactCoefficientSplittingStatement` and `CompactCoefficientProjectorStatement`. `G : Type u` is a Hausdorff, locally compact, totally disconnected topological group that is `SigmaCompactSpace` (countable at infinity). It has its Borel structure and a regular Haar measure `μ` that is also right invariant, which expresses unimodularity. The measure does not occur in the body.

Smooth representations are `SmoothRep.{0, u, v} ℂ G`. "Compact" is the published `HasCompactSmoothDualCoefficients` (compact support of all smooth matrix coefficients), which is Renard's notion by the IV.1.3 Theorem. Inside the statement:

- `compactPart V` holds when every irreducible `π` that is an actual subquotient of `V` (published `SmoothRep.IsSubquotient`) has compact coefficients. This is `M(G)_c`.
- `noncompactPart V` holds when no irreducible subquotient of `V` has compact coefficients. This is `M(G)_nc`.

The conclusion is

`Renard.IsCategoryDecomposition (fun b : Bool => if b then compactPart else noncompactPart) ↔ ∀ K : OpenSubgroup G, IsCompact (K : Set G) → {c : CompactCoefficientClass G | c.HasFixedVector K}.Finite`.

The published `Renard.IsCategoryDecomposition` is the A.IX notion `𝓜 = ∏ᵢ 𝓜ᵢ`: every object is the vertex of a coproduct cofan of objects of the components, and all morphisms between objects of distinct components are zero. The published `CompactCoefficientClass G` is the type of isomorphism classes of irreducible smooth representations with compact coefficients. `HasFixedVector K` says that a representative has a nonzero `K`-fixed vector. So the right side is exactly (KF).

## Remarks

- The statement is posed at a single carrier universe `v`. This loses nothing. For `G` countable at infinity, irreducible smooth representations and the compactly induced representation `ind_K^G 1` used in Renard's proof have countable dimension, so they have isomorphic copies at every carrier universe. This remark is not formalized.
- The more elementary decompositions displayed before the proposition (`M(G) = M(G)_τ × [M(G) \ τ]` for one or finitely many irreducible compact `τ`, and `M(G)_c = ∏_τ M(G)_τ`) are related to the published `CompactCoefficientSplittingStatement` and `CompactCoefficientProjectorStatement`. They are not restated here.
- The proof (the projector `ρ(e_c) = ∑_τ ρ(e_τ)` under (KF), and conversely the finite length of the compact part of `ind_K^G 1`) is not formalized here.
