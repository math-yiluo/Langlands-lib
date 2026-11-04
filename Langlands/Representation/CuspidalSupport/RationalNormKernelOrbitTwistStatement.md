# Renard VI.3.2(i) and (iii) on the actual norm kernel

This module states two clauses of Proposition VI.3.2 ("Restriction à ⁰G") in David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, printed pp.143–144 / PDF pp.149–150. The registered source is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The conjugation convention comes from VI.3.1 ("Action de G sur Irr(⁰G)", printed pp.142–143 / PDF pp.148–149). That section refers to the notation of Example III.2.1, and the proof of Lemma VI.3.1(ii) uses it explicitly: `σ^g(h) = σ(g⁻¹ h g)`.

The module contains two closed proposition definitions:

- `Langlands.CuspidalSupport.RationalNormKernelOrbitStatement` (part (i)), with universe parameters `u` and `uV`;
- `Langlands.CuspidalSupport.RationalNormKernelTwistEquivalenceStatement` (part (iii)), with universe parameters `u`, `uV` and `uW`.

Neither proposition is proved here. Each one is a separate target for a later proof.

## Common inputs

Both propositions quantify over every field `F : Type u` with `ValuativeRel F`, `TopologicalSpace F` and `IsNonarchimedeanLocalField F`. Both characteristics are allowed. They also quantify over every group scheme `G` over `Spec (CommRingCat.of F)` and every certificate `hG : GroupScheme.IsConnectedReductive G`. The affineness of `G.X.left` and its local finite type are derived from `hG` exactly as in the published `RationalInertiaDecompositionStatement`: the affine structure map comes from `hG.isAffineHom`, and local finite type comes from the smoothness in `hG.smooth`. The point group `GroupScheme.rationalPoints G` carries exactly the canonical topology `rationalPointTopology F G.X`.

For the inverse conjugation in part (i), the topological-group structure is the proved instance `rationalPoint_isTopologicalGroup F G`. Part (iii) does not need it. There are no locally-compact, nonarchimedean-group, Hausdorff, split, quasi-split, `GL_n`, finite-index, admissibility or dimension premises.

The source's `⁰G` is `Plancherel.rationalCommonNormKernel G`, the intersection over all rational algebraic characters `χ` of the kernels of the normalized norms `g ↦ |χ(g)|_F`. Renard defines this subgroup in V.2.3 (printed pp.105–106 / PDF pp.111–112), and `RationalCharacterValuation.md` documents the correspondence. Its normality is the published instance `rationalCommonNormKernel_normal`, so it is not a hypothesis. For an ambient smooth representation `π`, the restriction is `π.representation.comp (Plancherel.rationalCommonNormKernel G).subtype`. This is the actual restricted action on the original carrier of `π`, not a replacement object.

The only representation-theoretic premise is the irreducibility of `π` (or of `π₁` and `π₂`) as a `SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints G)` (for `π₂`, `SmoothRep.{0, u, uW}`). `SmoothRep.IsIrreducible` is Mathlib's `Representation.IsIrreducible`, which is simplicity of the lattice of subrepresentations. It excludes the zero representation and imposes no admissibility or finite length.

## Part (i): `RationalNormKernelOrbitStatement`

Source: "Les éléments de Irr(⁰G) apparaissant dans la restriction de (π, V) à ⁰G forment une seule G-orbite." For every irreducible `π`, with `ρH` the actual restriction above, the proposition has three conclusions:

1. **Nonempty occurrence.** There is `W : Subrepresentation ρH` with `W.toRepresentation.IsIrreducible`.
2. **Stability under the action.** For every irreducible `W : Subrepresentation ρH` and every point `g`, there is an irreducible `W' : Subrepresentation ρH` and an equivalence `(W.toRepresentation.comp (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom).Equiv W'.toRepresentation`. Here `H = Plancherel.rationalCommonNormKernel G`.
3. **One orbit.** For all irreducible `W₁ W₂ : Subrepresentation ρH` there are a point `g` and an equivalence `(W₁.toRepresentation.comp (SmoothRep.normalSubgroupInverseConjugation H g).toMonoidHom).Equiv W₂.toRepresentation`. Each such equivalence is wrapped in `Nonempty`.

`SmoothRep.normalSubgroupInverseConjugation H g : H ≃ₜ* H` is the published map `h ↦ g⁻¹ * h * g` from `CompactCoefficient.AmbientProjector`. It needs only normality and the topological-group structure, not compactness. So `W.toRepresentation.comp (…).toMonoidHom` is the representation `h ↦ σ(g⁻¹ h g)`, which is Renard's `σ^g` for `σ` the action on `W`. Conclusion 3 says that the type of `W₂` is `σ₁^g`. Conclusion 2 says that `σ^g` occurs whenever `σ` occurs. Together, the three conclusions say that the set of isomorphism classes of irreducible subrepresentations of the restriction is nonempty, stable under `G`, and contained in a single `G`-orbit. That is, the set is exactly one orbit of the action `(g, σ) ↦ σ^g` of VI.3.1.

Conclusion 2 is the easy direction: `π(g)` maps `W` onto an `H`-stable subspace isomorphic to `σ^g`, as in Lemma VI.3.1(ii). The contract lists conclusions 1 and 3. Conclusion 2 is included so that "forment une seule G-orbite" is stated literally, not only containment in one orbit. It adds no premise.

**Occurrence and the role of part (ii).** The source's "elements of Irr(⁰G) appearing in the restriction" are the `σ` whose isotypic component `V(σ)` is nonzero, in the source's decomposition `Res π = ⊕ V(σ)`. That decomposition uses part (ii): the restriction is semisimple of finite length. Here the occurring types are represented by actual irreducible subrepresentations of `ρH`, and the group action by equivalence of pulled-back representations, not by equality of subspaces. Without semisimplicity, an irreducible subquotient type need not be a subrepresentation type. The separate part (ii) task `376b73e5-5e3a-4785-bbdc-dc851977643a` supplies the identification of subquotient types with subrepresentation types (and of both with the source's `V(σ) ≠ 0`). Neither semisimplicity nor finite length is assumed here or claimed by this proposition. The orbit is finite by Lemma VI.3.1(i), which is not part of this statement.

## Part (iii): `RationalNormKernelTwistEquivalenceStatement`

Source: for irreducible `(π₁, V₁)` and `(π₂, V₂)`, the following are equivalent: a) `Res π₁ = Res π₂`; b) there is `χ ∈ X(G)` with `π₂ = π₁ ⊗ χ`; c) `Hom_{⁰G}(Res π₁, Res π₂) ≠ 0`. The printed equal signs mean isomorphism of representations.

The representation `π₁` is a `SmoothRep.{0, u, uV}` and `π₂` a `SmoothRep.{0, u, uW}`, so their carriers live in independent universes. Both are assumed irreducible. Let `ρ₁H` and `ρ₂H` be their actual restrictions to `H`, with

`XG := Plancherel.unramifiedCharacters (fun χ => (Plancherel.rationalNormCharacters G χ).toMul)`.

The three conditions are:

- `A := Nonempty (Representation.Equiv ρ₁H ρ₂H)`;
- `B := ∃ χ : XG, Nonempty (Representation.Equiv (Langlands.twist χ.val.toMonoidHom π₁.representation) π₂.representation)`;
- `C := ∃ f : Representation.IntertwiningMap ρ₁H ρ₂H, f ≠ 0`.

The conclusion is packaged as `(A ↔ B) ∧ (A ↔ C)`. `Representation.Equiv` is Mathlib's equivariant linear equivalence, which allows carriers in different universes. The zero in `C` is Mathlib's zero intertwiner.

`XG` is the published subgroup of continuous characters `G →ₜ* ℂˣ` whose kernel contains the common kernel of the same normalized norm characters, i.e. contains `H`. Renard's `X(G)` (VI.3.2, recalled from V.2.3) is the group of characters of `G` trivial on `⁰G`. These agree: `H` is open (`isOpen_rationalCommonNormKernel`), so every character trivial on `H` is locally constant and hence continuous. The complex torus structure on `X(G)` is not used. `Langlands.twist χ ρ` is the published scalar twist on the same carrier, with action `g ↦ χ(g) • ρ(g)`. This is the source's `π₁ ⊗ χ`, with the line `ℂ` absorbed. No abstract tensor functor is used.

No finite-dimensional ambient representation, finite-dimensional Hom space, preselected eigenvector, common constituent, central character, scalar central action, semisimplicity, finite length or decomposition witness is assumed.

## Source-to-Lean correspondence

| Source (printed pp.143–144) | Lean |
| --- | --- |
| `G`, the `F`-points of a connected reductive group | `GroupScheme.rationalPoints G` with `rationalPointTopology F G.X`, `hG : IsConnectedReductive G` |
| `⁰G` | `Plancherel.rationalCommonNormKernel G` |
| `(π, V)` irreducible | `π : SmoothRep.{0, u, uV} ℂ _`, `π.IsIrreducible` |
| `Res^G_{⁰G}(π, V)` | `π.representation.comp (rationalCommonNormKernel G).subtype` |
| `σ ∈ Irr(⁰G)` occurring in the restriction | irreducible `W : Subrepresentation ρH` (with part (ii)) |
| `σ^g(h) = σ(g⁻¹ h g)` (VI.3.1) | `W.toRepresentation.comp (normalSubgroupInverseConjugation H g).toMonoidHom` |
| "form one `G`-orbit" | conclusions 1–3 of part (i) |
| `X(G)` | `Plancherel.unramifiedCharacters (fun χ => (rationalNormCharacters G χ).toMul)` |
| `π₁ ⊗ χ` | `Langlands.twist χ.val.toMonoidHom π₁.representation` |
| `=` between representations | `Nonempty (Representation.Equiv _ _)` |
| `Hom_{⁰G}(Res π₁, Res π₂) ≠ 0` | `∃ f : Representation.IntertwiningMap ρ₁H ρ₂H, f ≠ 0` |

## Proof route (not formalized here)

Renard's proof of (i) uses part (ii) to decompose `Res π` into isotypic components. It uses the covariance `π(g)·V(σ) = V(σ^g)` of Lemma VI.3.1(ii), and the irreducibility of `π`: the sum of the components in one orbit is `G`-stable and nonzero, so it is everything. For (iii), (b) ⇒ (a) holds because an unramified character is trivial on `⁰G`, and (a) ⇒ (c) is immediate. For (c) ⇒ (b), the proof uses part (ii) and Schur's lemma to make `Hom_{⁰G}(V₁, V₂)` finite-dimensional and nonzero. The action `g·f = π₂(g) ∘ f ∘ π₁(g)⁻¹` factors through the commutative quotient `G/⁰G`, so a common eigenvector gives a nonzero `f` and a character `χ` of `G/⁰G` with `f ∈ Hom_G(π₁ ⊗ χ, π₂)`. Irreducibility then makes `f` an isomorphism. In the Lean setting, the continuity of that eigencharacter follows from the discreteness of `G/H` (`rationalNormKernelQuotientDiscrete`). These steps are obligations of the later proofs, not hypotheses of the propositions.

Related published interfaces: `CuspidalSupport.RationalInertia` defines a `SmoothRep`-level unramified twist and inertia relation. Part (iii) uses the `Representation`-level `Langlands.twist`, as the task requires. The conditional compact-type `CompactCoefficient.SelectedConjugation` (which needs a supplied finite spanning family) and the finite-dimensional `Langlands.FiniteDimensionalNormalRestrictionSemisimplicity` do not prove these unrestricted statements.
