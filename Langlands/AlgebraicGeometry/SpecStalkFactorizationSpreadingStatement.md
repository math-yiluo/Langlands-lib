# Statement: spreading out a factorization from the local scheme at a point

Worker 738.

`Langlands.AlgebraicGeometry.SpecStalkFactorizationSpreadingStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports only Mathlib: the morphism properties
`QuasiCompact`, `QuasiSeparated` and `LocallyOfFinitePresentation`, and the canonical
morphism `Scheme.fromSpecStalk`.

## Objects used

- `S X K : Scheme.{u}`, a morphism `p : X ⟶ S` and a morphism `k : K ⟶ X`.
- `s : S` is a point, `S.presheaf.stalk s` is the local ring `𝒪_{S,s}`, and
  `S.fromSpecStalk s : Spec 𝒪_{S,s} ⟶ S` is the canonical morphism.
- `pullback p (S.fromSpecStalk s)` is `X ×_S Spec 𝒪_{S,s}`, and
  `pullback.fst p (S.fromSpecStalk s)` is its projection to `X`.
- For an open `U : S.Opens`, `U.ι : U ⟶ S` is the open immersion, so `pullback p U.ι` is
  `X ×_S U`, the open subscheme `p⁻¹(U)` of `X`, and `pullback.fst p U.ι` is its projection
  to `X`.
- "The projection `T ⟶ X` factors through `k`" means that there is a morphism
  `y : T ⟶ K` with `y ≫ k` equal to the projection.

## Statement and quantifiers

For all schemes `S X K` in universe `u`, every quasi-compact and quasi-separated
morphism `p : X ⟶ S`, every morphism `k : K ⟶ X` locally of finite presentation and
every point `s ∈ S`: if the projection `X ×_S Spec 𝒪_{S,s} ⟶ X` factors through `k`,
then there are an open `U ⊆ S` with `s ∈ U` and a morphism `y : X ×_S U ⟶ K` with
`y ≫ k` equal to the projection `X ×_S U ⟶ X`.

## Sources

1. A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique IV*, troisième
   partie, Publ. Math. IHÉS 28 (1966). It is registered as
   `ega-iv3-grothendieck-dieudonne-1966`, file
   `Grothendieck and Dieudonne - Elements de geometrie algebrique IV, Troisieme partie (1966).pdf`
   (SHA-256 `f365212b38f20608ba34c21ae3ee40bbae1b42d9d3dff01a85356f9cc819c23e`). In (8.8.1),
   printed p.28 (page 27 of the PDF), `S = lim S_λ` is the limit of a projective system of
   schemes with affine transition morphisms (the setting of (8.2.2)), `X_α` and `Y_α` are
   `S_α`-schemes, `X = X_α ×_{S_α} S` and `Y = Y_α ×_{S_α} S`, and (8.8.1.1) is the canonical map
   `lim_λ Hom_{S_λ}(X_λ, Y_λ) → Hom_S(X, Y)`. Théorème (8.8.2) (i), same page: "Supposons
   X_α quasi-compact (resp. quasi-compact et quasi-séparé), et Y_α localement de type
   fini (resp. localement de présentation finie) sur S_α. Alors l'application (8.8.1.1)
   est injective (resp. bijective)."
2. The Stacks Project, Chapter 32 *Limits of Schemes*, `limits.tex` at commit
   `a04446e57ec1fbc252a871afcec7752fb2807b14`. It is registered as the folder
   `stacks-limits-of-schemes-a04446e5` (content SHA-256
   `2f8053f028d2ef75bb776f1863aedfba4ce578ae6999eaa60f88cd93100cf453`).
   - The proposition with tag 01ZC (label
     `proposition-characterize-locally-finite-presentation`, lines 1284–1309 of
     `limits.tex`): for a morphism `f : X → S`, "(1) The morphism f is locally of finite
     presentation" is equivalent to "(3) For any directed set I, and any inverse system
     (T_i, f_{ii'}) of S-schemes over I with each f_{ii'} affine and every T_i
     quasi-compact and quasi-separated as a scheme, we have
     Mor_S(lim_i T_i, X) = colim_i Mor_S(T_i, X)".
   - The proof of the lemma with tag 0EY3 (label `lemma-glueing-near-point-properties`),
     lines 5203–5204 of `limits.tex`: "Recall that Spec(𝒪_{S, s}) is the limit of the
     affine open neighbourhoods of s in S."
3. A. Grothendieck, SGA 3, Exposé IX, Gille–Polo recomposed edition of 8 November 2009,
   registered as `sga3-expose-ix-gille-polo-2009` (SHA-256
   `7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`). The proof of
   Théorème 5.1 a), recomposed p.49 (page 19 of the PDF), uses exactly this statement for
   the kernel `K` of the pair `u, v`: "Donc K est de type fini sur S, donc de présentation
   finie sur S, puisque S est localement noethérien. Par conséquent, d'après EGA IV₃,
   8.8.2.4, pour montrer qu'il existe un voisinage ouvert U de s tel que K_U = H_U, il
   suffit de montrer que K_{S′} = H_{S′}, où S′ est le spectre de A = 𝒪_{S,s}."

## Derivation from the sources

This is the special case of EGA IV₃ (8.8.2) (i) (bijectivity), or of Stacks 01ZC (3),
for the following system. Choose an affine open `U₀ ∋ s`. The affine opens `U ⊆ U₀`
containing `s`, ordered by reverse inclusion, form a directed system, since every two
contain a basic open of `U₀` containing `s`. Its transition maps are open immersions
between affine schemes, hence affine, and by source 2 (0EY3) its limit is
`Spec 𝒪_{S,s}`. Base change along `p` preserves these limits, so `X ×_S Spec 𝒪_{S,s}` is
the limit of the schemes `T_U = X ×_S U`. Each transition map `T_U ⟶ T_{U'}` is a base
change of the affine morphism `U ⟶ U'`, so it is affine. Each `T_U` is quasi-compact and
quasi-separated, because `p` is quasi-compact and quasi-separated and `U` is affine.

Apply Stacks 01ZC (3) over the base `X`, to the morphism `k` (locally of finite
presentation) and to this system of `X`-schemes `T_U`, each with its projection to `X`.
A factorization of the projection `X ×_S Spec 𝒪_{S,s} ⟶ X` through `k` is an element of
`Mor_X(lim T_U, K)`. It therefore comes from an element of `Mor_X(T_U, K)` for some `U`,
which is a factorization of `X ×_S U ⟶ X` through `k`. In the notation of EGA (8.8.1),
take `S_α = X_α = X ×_S U₀` and `Y_α = K ×_X X_α`. Then `Hom_{S_λ}(X_λ, Y_λ)` is the set of
sections of `Y_λ ⟶ X_λ`, that is, of factorizations of `T_U ⟶ X` through `k`.

The statement asks only for existence, the surjectivity half of the cited bijection. It
does not assert that the factorization over `U` is unique or compatible with the given one
over `Spec 𝒪_{S,s}`.

## Scope

All schemes are in universe `u`. The statement imposes no hypothesis on `S` or on `K`
beyond the stated properties of `p` and `k`. It is not stated for general cofiltered
limits, only for the limit `Spec 𝒪_{S,s}` of the open neighbourhoods of `s`. It is meant
for the proof of SGA 3, IX, Théorème 5.1 a) (Library statement
`Langlands.GroupScheme.MultiplicativeTypeCentralRigidityStatement`), where `p` is the
structure morphism of `H` and `k` is the kernel `K ⟶ H` of a pair of homomorphisms.
