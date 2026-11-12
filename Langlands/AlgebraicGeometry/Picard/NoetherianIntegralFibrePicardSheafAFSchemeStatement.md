# The Picard sheaf of a pointed projective flat family with geometrically integral fibres is an AF scheme

Authors: Worker 227.

Worker 227 wrote the Lean file, read the cited pages of Kleiman's survey and
the cited Stacks Project results, and wrote this description and the
derivation below, for task `6db3b992-b6f6-49fc-adcc-33c09c47782e`
(Task 5656). The module also serves as the general input of
`AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeIntegralFibreReduction`.

## Statement

`Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u}`
is a proposition with the single universe parameter `u`. Its body is

```lean
∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (X : Scheme.{u})
  (f : X ⟶ Spec (CommRingCat.of R)),
  IsProper f → Flat f → GeometricallyIntegral f →
  (∃ σ : Spec (CommRingCat.of R) ⟶ X, σ ≫ f = 𝟙 _) →
  (∃ L : LineBundle X, L.IsAmple) →
    ∃ P : Over (Spec (CommRingCat.of R)),
      PointTopology.HasFiniteAffineNeighborhoods P.left ∧
        Nonempty ((RelativePicard.classSheafPresheaf f).RepresentableBy P)
```

Write `S` for `Spec (CommRingCat.of R)` and
`F = RelativePicard.classSheafPresheaf f`. The proposition quantifies over every
noetherian commutative ring `R : Type u` and every morphism of schemes
`f : X ⟶ S` such that

1. `f` is proper (Mathlib's `IsProper`: separated, universally closed and
   locally of finite type);
2. `f` is flat (Mathlib's `Flat`);
3. `f` is geometrically integral (Mathlib's `GeometricallyIntegral`: for every
   field `K` and every morphism `Spec K ⟶ S`, the fibre product
   `X ×_S Spec K` is an integral scheme; in particular every geometric fibre is
   integral);
4. `f` has a section: some `σ : S ⟶ X` with `σ ≫ f = 𝟙 S`;
5. the scheme `X` carries an ample line bundle (`LineBundle.IsAmple`, from
   `Langlands.AlgebraicGeometry.Picard.Ample`: `X` is quasi-compact and every
   point lies in an affine generation locus `X_s` of a section `s` of some
   positive tensor power of the bundle, as in EGA II 4.5.2).

Under these hypotheses it asserts that there is an object `P` of `Over S` such
that

1. every finite set of points of the scheme `P.left` is contained in one
   affine open subscheme
   (`Langlands.AlgebraicGeometry.PointTopology.HasFiniteAffineNeighborhoods`,
   that is `∀ s : Set X, s.Finite → ∃ U : X.affineOpens, s ⊆ U.val`), and
2. `F` is represented by `P` in the sense of Mathlib's
   `Functor.RepresentableBy`: bijections `(T ⟶ P) ≃ F.obj (op T)` for every
   `T : Over S`, natural in `T`.

`F` is the underlying presheaf of the Library sheaf
`RelativePicard.classSheaf f`: Mathlib's sheafification, for
`Scheme.fppfTopology.over S` and in `Type (u+1)`, of the presheaf of
isomorphism classes of actual line bundles on `T ×_S X`. Test objects range
over the whole slice `Over S`, including non-noetherian, non-quasi-compact and
non-separated `S`-schemes. Apart from conjunct 1, nothing is required of
`P`: no group structure, universal bundle, separatedness, finiteness
condition or decomposition into quasi-projective pieces is asserted. The
proposition proves nothing; it is a statement definition only.

## Provenance

The proposition is derived content. Its geometric core is Grothendieck's
existence theorem for the Picard scheme as stated and proved in

S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1 (2005), Chapter 9 of
*Fundamental Algebraic Geometry: Grothendieck's FGA Explained*, registered
source `kleiman-2005-picard-scheme-arxiv-math0504020v1`, SHA-256
`cc14e62f0ebebb8617777651bbcd08bb7548cb9fe955f3a25bb6491c5f3beeaa`. Its PDF
page numbers equal its printed page numbers.

Kleiman's theorem covers only locally noetherian test schemes. The Lean
proposition asserts representability on every object of `Over S`. The step from
the first to the second is not in Kleiman; it is derived below (Steps 3 to 6).

### What the source states, and its scope

- Conventions, p.15: "Throughout these notes, we work only with locally
  Noetherian schemes, just as Grothendieck did in [FGA]." Kleiman adds that
  the restriction can be removed by "a limiting process that reduces the
  general case to the Noetherian case", and does not carry the process out.
- Definition 2.1, p.16: the absolute Picard functor is a functor "from the
  category of (locally Noetherian) `S`-schemes `T`". The relative functor
  `Pic_{X/S}`, `T ↦ Pic(X_T)/Pic(T)`, and its Zariski, étale and fppf
  sheafifications `Pic(X/S)(zar)`, `Pic(X/S)(ét)`, `Pic(X/S)(fppf)` are
  therefore functors on locally noetherian `S`-schemes, and the sheafifications
  are formed in that category.
- Theorem 4.8 (Main), pp.27–28: "Assume `f : X → S` is projective Zariski
  locally over `S`, and is flat with integral geometric fibers. (1) Then
  `Pic_{X/S}` exists, is separated and locally of finite type over `S`, and
  represents `Pic(X/S)(ét)`. (2) If also `S` is Noetherian and `X/S` is
  projective, then `Pic_{X/S}` is a disjoint union of open subschemes, each an
  increasing union of open quasi-projective `S`-schemes." In the proof
  (p.28 onwards) the pieces are indexed by Hilbert polynomials `φ ∈ ℚ[n]` and
  the increasing unions by integers `m`.
- Theorem 2.5 (Comparison), p.18: if `O_S → f_*O_X` is an isomorphism
  universally, then the natural maps
  `Pic_{X/S} → Pic(X/S)(zar) → Pic(X/S)(ét) → Pic(X/S)(fppf)` are injective, and
  all three are isomorphisms if also `f` has a section.
- Lemma 2.9, p.19: if `f` has a section `g`, then for every `S`-scheme `T`,
  forgetting the rigidification maps the group of isomorphism classes of pairs
  `(L, u)`, with `L` invertible on `X_T` and `u : O_T ≅ g_T^*L` a
  `g`-rigidification (Definition 2.8, p.19), isomorphically onto
  `Pic_{X/S}(T)`. The inverse sends `M` to `M ⊗ f_T^*(g_T^*M)⁻¹`.
- Exercise 3.11, p.25: if `f` is proper and flat and its geometric fibres are
  reduced and connected, then `O_S → f_*O_X` is an isomorphism universally.

Thus Kleiman's `Pic_{X/S}` is a scheme `P` whose functor of points agrees with
`Pic(X/S)(ét)` on locally noetherian `S`-schemes. Kleiman says nothing about
non-noetherian test schemes.

The other registered sources are:

- `stacks-fibre-ampleness-affine-neighbourhood-2026-11-02` (SHA-256
  `7a654789470ca2c545023588c4949fa09b3559b6801d9ff2f7c74b826eadc3a3`, file
  `01VK.html`, Lemma 29.38.5);
- `stacks-projective-space-twists-morphisms-2026-10-26` (SHA-256
  `e21fdf382a193a228965d8a018149e752c04561e3a229faae7ead34fda0d85c5`, file
  `01W7.html`, Section 29.44, Lemma 29.44.13);
- `stacks-properties-chapter-2026-10-28` (SHA-256
  `2f5b9ba41e07dd3a888da40496e07afae6caedd550597d96313ab16db4380316`, PDF p.50,
  Lemma 30.5 of the chapter = Lemma 28.30.5, tag 01ZY);
- `stacks-limits-of-schemes-a04446e5` (SHA-256
  `2f8053f028d2ef75bb776f1863aedfba4ce578ae6999eaa60f88cd93100cf453`, file
  `limits.tex` at Stacks commit `a04446e5`, Chapter 32 "Limits of Schemes":
  Proposition 32.6.1, tag 01ZC, which is EGA IV 8.14.2; Lemmas 32.10.2, tag
  01ZR, and 32.10.3, tag 0B8W).

### Derivation

Fix `R`, `f`, a section `σ` and an ample `L` as in the hypotheses. Write
`Rig` for the Library presheaf
`RigidifiedLineBundle.classPresheaf RigidifiedModule.pullbackCoherence f σ _`
(in `Langlands.AlgebraicGeometry.Picard.RigidifiedClassPresheaf`, values in
`Type (u+1)`) of isomorphism classes of actual `σ`-rigidified line bundles on `T ×_S X`, for
`T : Over S`. Its classes are Kleiman's pairs `(L, u)` of Lemma 2.9.

**Step 1 (Kleiman's hypotheses).** `S = Spec R` with `R` noetherian is the
noetherian affine base of Theorem 4.8(2). Over the affine base `S`, an
invertible sheaf on `X` is ample if and only if it is ample relative to `f`
(Stacks Lemma 29.38.5, tag 01VK, which is EGA II 4.6.6). So the proper
morphism `f`, which is of finite type, is quasi-projective (Stacks Definition
29.40.1). Since `S` is quasi-compact and quasi-separated, a proper
quasi-projective morphism is projective, that is, `X` is a closed subscheme of
a projective bundle `P(E)` with `E` of finite type on `S` (Stacks Lemma
29.44.13, in Section 29.44, tag 01W7). Hypotheses 2 and 3 give flatness and
integral geometric fibres. So Theorem 4.8(1) and (2) apply. Let `P` be
Kleiman's `Pic_{X/S}`. It is locally of finite type over the noetherian `S`,
hence locally of finite presentation.

**Step 2 (noetherian test schemes; inside the source's scope).** Hypothesis 3
makes the geometric fibres reduced and connected, so by Exercise 3.11
`O_S → f_*O_X` is an isomorphism universally. For every locally noetherian
`S`-scheme `T` we get bijections, natural in `T`:

```
Hom_S(T, P) ≅ Pic(X/S)(ét)(T)    (Theorem 4.8(1))
            ≅ Pic_{X/S}(T)       (Theorem 2.5(2), with the section σ)
            ≅ Rig(T)             (Lemma 2.9, inverse M ↦ M ⊗ f_T^*(σ_T^*M)⁻¹).
```

Only noetherian affine `T` are used below.

**Step 3 (comparison with the Library sheaf on all test objects).** The
Library theorem `Langlands.AlgebraicGeometry.Picard.rigidifiedFppfComparison`
proves `RigidifiedFppfComparisonStatement`: if `f` is quasi-compact and
quasi-separated, `σ` is a section, and the canonical structure-sheaf map of
every base change of `f` is an isomorphism on every open, then
`RigidifiedLineBundle.toPicardSheaf f σ _` is an isomorphism. Its Library
Markdown gives Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
paragraph (6.2), as source. This
comparison holds for every `T : Over S`, with no noetherian condition. Every
hypothesis holds here:

- a proper `f` is quasi-compact and quasi-separated;
- every base change `T ×_S X → T` is proper and flat, locally of finite
  presentation (because `f` is, `R` being noetherian), and geometrically
  reduced and geometrically connected (because `f` is geometrically integral);
- so the Library theorem
  `AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected`,
  which holds over an arbitrary base scheme, shows that its comorphism is
  bijective on every open. This is the needed structure-sheaf condition, once
  `(relativeProjection f).app T` is identified with that base change.

Composing with the Library's group/set comparison
`RelativePicard.forgetSheafIso`, which gives
`RigidifiedLineBundle.toPicardSheaf_forgetSheafIso_hom`, the canonical map
`RigidifiedLineBundle.toClassPicardSheaf f σ _ : Rig ⟶ F` is an isomorphism of
presheaves on all of `Over S`. On a representative `(L, u)` it is the
sheafification class of `L`. This step replaces Theorem 2.5(2) and
Exercise 3.11 outside the locally noetherian range, and it identifies `F` with
`Rig` exactly, not just up to some unnamed isomorphism.

**Step 4 (affine test objects, by noetherian approximation).** Let
`T = Spec A` be affine over `S`. Write `A` as the directed union of its
finitely generated `R`-subalgebras `A_λ`. Each `A_λ` is noetherian by the
Hilbert basis theorem and lies in `Type u`. Set `T_λ = Spec A_λ`. Then
`T = lim T_λ`, a limit of affine `S`-schemes with affine transition maps.

- Since `P → S` is locally of finite presentation, Stacks Proposition 32.6.1
  (tag 01ZC, EGA IV 8.14.2), (1) ⇒ (2), gives
  `Hom_S(T, P) = colim_λ Hom_S(T_λ, P)`.
- `X_T = lim X_{T_λ}` with affine transition maps, and each `X_{T_λ}` is
  quasi-compact and quasi-separated (it is proper over an affine scheme).
  - Every invertible module on `X_T` comes from some `X_{T_λ}` (Stacks
    Lemma 32.10.3(2), tag 0B8W).
  - Morphisms between finitely presented modules descend to a finite stage, and
    two morphisms that agree over the limit agree at a finite stage (Stacks
    Lemma 32.10.2(2),(3), tag 01ZR). Apply this on the system `X_{T_λ}` to
    isomorphisms of line bundles. Apply it on the system `T_λ` to
    rigidifications `u : O_T ≅ σ_T^*L` and to their compatibility with
    isomorphisms; here `σ_{T_λ}^*L_λ` pulls back to `σ_T^*L`.

  Together these give `Rig(T) = colim_λ Rig(T_λ)`. Surjectivity: every pair
  `(L, u)` descends, `u` becoming invertible at a later stage. Injectivity:
  an isomorphism of pulled-back pairs descends, and its compatibility with the
  rigidifications holds at a later stage.
- Define `θ_T : Hom_S(T, P) ≅ Rig(T)` as the colimit of the Step 2 bijections
  for the `T_λ`. These bijections are natural, and an `R`-algebra map `A → B`
  sends each `A_λ` into a finitely generated `R`-subalgebra of `B`. Hence `θ`
  is natural for all morphisms between affine objects of `Over S`.

With Step 3, this gives a natural bijection `Hom_S(T, P) ≅ F(T)` for every
affine `T : Over S`.

**Step 5 (all test objects, by Zariski gluing).** The functor of points
`Hom_S(−, P)` is a Zariski sheaf on `Over S`, because morphisms of schemes glue
along open covers. `F` is a Zariski sheaf because it is a sheaf for
`Scheme.fppfTopology.over S`, whose coverings include open covers. A natural
isomorphism between the restrictions of two Zariski sheaves to the affine
objects extends uniquely to a natural isomorphism of the sheaves, as follows.
Let `T : Over S` be arbitrary, possibly non-quasi-compact or non-separated.
Choose an affine open cover `(U_i)` of `T` and affine open covers `(W_{ijk})`
of the overlaps `U_i ∩ U_j`. Then `F(T)` and `Hom_S(T, P)` are the equalizers
of `∏ F(U_i) ⇉ ∏ F(W_{ijk})` and of the corresponding diagram for `P`, and
the affine bijections commute with both maps by naturality. The induced
bijection does not depend on the covers (compare through a common affine
refinement) and is natural in `T` (pull covers back along `T' → T` and refine
them by affine opens). So `F` is represented by `P` on all of `Over S`, which
is conjunct 2. The bijection is the transport of Kleiman's identification
through the canonical maps of Steps 2 to 4.

**Step 6 (universes).** `F` takes values in `Type (u+1)`. The hom-sets of
`Over S` lie in `Type u`. Mathlib's `Functor.RepresentableBy` allows `F` to
take values in any universe: its `homEquiv` is an equivalence between
`(T ⟶ P)` and `F.obj (op T)`, which may lie in different universes. So `F`
needs no universe transport. `rigidifiedFppfComparison` relates presheaves
that both have class universe `u+1`. Kleiman's `P` must be realized as an
object of `Over S` in `Scheme.{u}`. In the proof of Theorem 4.8(2), `P` is
the disjoint union of countably many pieces `P^φ` (`φ ∈ ℚ[n]`). Each piece is
a countable increasing union of quasi-projective, hence quasi-compact, opens
`P^φ_m` (`m ∈ ℤ`). So `P` is glued from countably many affine opens, each the
spectrum of a finitely generated `R`-algebra, and an isomorphic copy exists in
`Scheme.{u}`. The approximating algebras `A_λ` of Step 4 lie in `Type u`.

**Step 7 (conjunct 1).** Conjunct 1 is not stated verbatim by Kleiman. It
follows from the structure in Theorem 4.8(2). A finite set of points of `P`
meets only finitely many of the disjoint open pieces. In each piece its points
lie in one member of the increasing union. That member is quasi-projective
over the affine noetherian base, so every finite set of its points lies in an
affine open (Stacks Lemma 28.30.5, tag 01ZY, for a scheme with an ample
invertible sheaf; an `S`-ample sheaf on a scheme quasi-projective over the
affine `S` is ample by Lemma 29.38.5). Finally, a finite disjoint union of
affine opens of different pieces is an affine open of `P`.

### Comparison with the source

Compared with Kleiman's Theorem 4.8, the proposition is weaker in its geometric
assumptions and conclusions:

- it requires a section and a noetherian affine base;
- it asserts only conjunct 1 about the geometry of `P` (it omits separatedness,
  local finite type and the decomposition).

It is stronger in its test category: it asserts representability of the fppf
sheaf on all `S`-schemes, which Steps 3 to 6 derive from Kleiman's
locally-noetherian statement. No source-specific errata note was found in the
Library's `notes/errata/` directory.

## Future proof obligations

A proof must construct, for every such `R`, `f`, section and ample bundle, an
actual `P : Over S` in `Scheme.{u}` with the finite-set property, and a natural
bijection with the exact Library presheaf `F` on all test objects. Following
the derivation above, it needs:

1. Kleiman's existence theorem on noetherian test schemes (Step 2). Following
   Kleiman's proof of Theorem 4.8, this needs the Hilbert scheme of `X/S`
   (Grothendieck; Nitsure, *Construction of Hilbert and Quot schemes*, FGA
   Explained Chapter 5), the openness of relative effective divisors in it
   (Kleiman Theorem 3.7), linear systems as projective bundles (Kleiman
   Theorem 3.13), and the quotient construction of Kleiman Lemma 4.9. Kleiman's
   Lemma 2.9 relates rigidified pairs to `Pic_{X/S}`.
2. The comparison of Step 3 for `f`. This is the Library theorem
   `rigidifiedFppfComparison`, applied with the structure-sheaf condition
   obtained from
   `bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected`
   for the base changes of `f`.
3. The extension to arbitrary affine test objects (Step 4): local finite
   presentation of `P`, Stacks Proposition 32.6.1 for `P`, and Lemmas 32.10.2
   and 32.10.3 for rigidified line bundles. A proof may be able to use
   existing Library limit tools for line bundles (for example the modules
   `Langlands.AlgebraicGeometry.Picard.LineBundleLimitSpreading` and
   `Langlands.AlgebraicGeometry.Picard.AffineIsomColimit`) where they apply.
4. The Zariski gluing from affine to arbitrary test objects (Step 5),
   including non-quasi-compact ones, and the naturality of the result.
5. The realization of `P` in `Scheme.{u}` (Step 6) and the finite-set property
   (Step 7).

None of these is a premise of the proposition, and neither this proposition nor
the target `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement` has been
proved.

## Use

`Langlands.AlgebraicGeometry.Picard.ampleNormalFiniteTypeAbelianPicardSheafAFScheme_of_noetherianIntegralFibre`,
in `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeIntegralFibreReduction`,
derives `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement` from this
proposition.
