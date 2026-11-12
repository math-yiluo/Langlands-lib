# Proof of the centralizer part of parahoric subgroups (KP Lemma 7.4.3)

Author: Worker 4599 (task `c2202322-8550-47ad-99d4-b17191c493f9`).

```lean
theorem Langlands.Geometry.Building.ParahoricBuildingData.centralizerParahoricIntersection
    (P : ParahoricBuildingData G) : P.CentralizerParahoricIntersectionStatement
```

This proves the published proposition
`Langlands.Geometry.Building.ParahoricBuildingData.CentralizerParahoricIntersectionStatement`
(module `Langlands.Geometry.Building.CentralizerParahoricStatement`) exactly, at
arbitrary universe `u`. Let `F : Type u` be a nonarchimedean local field of either
characteristic, `G` a group scheme over `Spec F` with affine structure morphism, and
`P : ParahoricBuildingData G` actual parahoric building data. Assume the actual fixed
apartment satisfies the corrected Chapter 7 apartment axioms,
`P.apartment.SatisfiesApartmentAxioms P.centralizer` (including AS 5). Then for every
non-empty `Ω ⊆ A(S)`,

```
centralizerPoints P.i ⊓ P.parahoric Ω =
  P.centralizerZero.map (rationalPoints.map P.centralizer.j)
```

So the points of `G(F)` that centralize `S` and lie in `P_Ω = Z(F)^0 · G(F)^♯_Ω` are
exactly the image of the actual `Z(F)^0` of `P.zeroDatum` under the actual centralizer
inclusion `j`. The theorem takes only the data `P`. The apartment premise is the
antecedent of the statement itself. No boundedness, decomposition or zero/norm-one
equality is assumed.

## Implemented proof

The proof is the single term

```lean
fun hax =>
  P.centralizerParahoricAssembly (P.rootGroup_le_simplyConnectedImage hax)
    P.toValuationBuildingData.sharpFixerBoundedness
    (P.zeroDatum.coverImageCentralizerNormKernel_of_intersection
      P.zeroDatum.minimalLeviZeroComparison.2) hax
```

`ParahoricBuildingData.centralizerParahoricAssembly` (module
`Langlands.Geometry.Building.KPCentralizerParahoricAssembly`) proves that three
statements about the actual data imply `P.CentralizerParahoricIntersectionStatement`.
Each is supplied by a published Library proof:

| Assembly input | Supplied by (module) |
| --- | --- |
| `P.zeroDatum.RootGroupLeSimplyConnectedImageStatement` | `ParahoricBuildingData.rootGroup_le_simplyConnectedImage hax` (`Langlands.Geometry.Building.ApartmentRootCover`), using the apartment premise `hax` |
| `P.toValuationBuildingData.SharpFixerBoundednessStatement` | `ValuationBuildingData.sharpFixerBoundedness` (`Langlands.Geometry.Building.SharpFixerBoundednessProof`) |
| `P.zeroDatum.CoverImageCentralizerNormKernelStatement` | `ZeroSubgroupDatum.coverImageCentralizerNormKernel_of_intersection` (`Langlands.Geometry.Building.KPMinimalLeviZeroStatement`), applied to the second conjunct of `ZeroSubgroupDatum.minimalLeviZeroComparison` (`Langlands.Geometry.Building.KPMinimalLeviZeroComparisonProof`) |

Root lifting needs the apartment premise, so the term first introduces `hax` and then
passes `hax` again as the antecedent of the assembled statement. This module adds no
other declaration.

## How the inputs give the equality

This summarizes the published reductions that the term applies. They are not proved
again here.

- *Reduction to singleton sharp fixers.* `centralizerParahoricReduction` (module
  `CentralizerParahoricReduction`) shows that the target is equivalent to the
  inclusion `centralizerPoints P.i ⊓ P.sharpFixer {x} ≤ j(Z(F)^0)` for every
  apartment point `x`, under the same apartment premise. The inclusion `⊇` of the
  target follows directly from the definition of `P.parahoric`. For `⊆`, an element of
  `P_Ω` is `j(z) · h` with `z ∈ Z(F)^0` and `h ∈ G(F)^♯_Ω` (`mem_parahoric_iff`). If the
  product centralizes `S`, then so does `h`. Since `Ω` is non-empty, `G(F)^♯_Ω` lies in
  `G(F)^♯_x` for some `x ∈ Ω`.
- *Lifting to the actual centralizer.* An element `g` of the singleton intersection
  centralizes `S`. So it is `j(z)` for an actual point `z` of the represented
  centralizer `Z`.
- *Simply connected image.* By `rootGroup_le_simplyConnectedImage`, every rational
  point of each actual relative root subgroup lifts through the supplied simply
  connected derived cover `G_sc → D → G`. So `sharpFixer_le_simplyConnectedImage_of_rootGroups`
  puts `G(F)^♯_x` in the image of `G_sc(F)`. This is the passage to the simply
  connected cover in the source proof: `G(k)^♯_x` lies in `G(k)^♮`.
- *Norm-one subgroup.* Boundedness of `G(F)^♯_x` (KP Corollary 7.3.14) and the adapter
  `comap_sharpFixer_le_centralizerNormKernel` put `z` in `Z(F)^1`, the rational-character
  norm kernel of the actual centralizer.
- *Zero subgroup.* The cover-image comparison says that a point of `Z(F)^1` whose image
  lies in the simply connected image belongs to `Z(F)^0`. Its proof derives it from the
  intersection equality `G(F)^0 ∩ Z(F)^1 = Z(F)^0` of KP Corollary 2.6.28, proved for
  every actual zero datum by `minimalLeviZeroComparison`. Hence `z ∈ Z(F)^0` and
  `g = j(z) ∈ j(Z(F)^0)`.

The actual `Z(F)^0 = P.centralizerZero`, the actual `j`, the actual sharp fixers and
the actual simply connected cover of `P.zeroDatum` are used throughout. `Z(F)^0` is
never replaced by `Z(F)^1` or by another bounded subgroup. Boundedness alone gives only
`Z(F)^1`. The comparison with the simply connected image supplies the remaining step
to `Z(F)^0`.

## Source and provenance

The source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732` (PDF page = printed
page + 31).

- Lemma 7.4.3 (printed p. 255 / PDF p. 286) states `Z(k) ∩ G(k)^0_Ω = Z(k)^0`, with
  `G(k)^0_Ω = Z(k)^0 · G(k)^♯_Ω` from Definition 7.4.1(2),(4) on the same page. Its
  proof is "a special case of Lemma 7.3.16".
- Lemma 7.3.16 (printed p. 252 / PDF p. 283) for `f = 0` is the source route. It
  reduces to `G(k)^♯_{x,f} ∩ Z(k) ⊆ Z(k)_{f(0)}`. Since `G(k)^♯_{x,f}` lies in
  `G(k)^♮`, it passes to `G` simply connected. Corollary 7.3.14 (printed pp. 251–252 /
  PDF pp. 282–283) then puts the intersection in `Z(k)^1`, and Lemma 2.6.27 (printed
  p. 105 / PDF p. 136) gives `Z(k)^1 = Z(k)^0`.
- The Lean proof follows this route with one change. KP reduces to a simply connected
  `G` and uses Lemma 2.6.27 there. The Lean proof instead stays in the actual `G`. It
  combines the simply connected image containment with the intersection assertion of
  Corollary 2.6.28 (printed pp. 105–106 / PDF pp. 136–137), which KP proves from
  Lemma 2.6.27 through the simply connected cover.
- The corrections of 1 November 2024, `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF p. 33, add
  AS 5 to the Chapter 7 hypotheses. The target keeps the corrected apartment axioms as
  its premise, and they are passed unchanged to root lifting and to boundedness.

The statement is for non-empty `Ω`. KP fix a non-empty `Ω` at the start of §7.4. For
`Ω = ∅` the sharp fixer is generated by all root subgroups, as the target's Markdown
explains.

This proof is an assembly of published Library proofs. It adds no new definition,
statement or premise, and it leaves the target Lean/Markdown pair and every pair it
imports unchanged.
