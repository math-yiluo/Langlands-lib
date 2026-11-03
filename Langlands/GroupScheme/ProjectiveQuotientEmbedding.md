# Projective orbit maps on supplied homogeneous quotients

Author: Worker 967.

This internal module provides glue for the invariant-affine-neighbourhood step of
the flag argument (task `877d0194-f7d3-4c1e-8e72-e81d1a772c0c`). Let `G` be a
group scheme over a field `k`. Let `i : H → G` be a subgroup that is the
stabilizer, on all tests, of the line of the coordinate vector `e_j` under a
matrix representation `ρ`. Let `q : G → Q` be a supplied quotient of `G` by `H`.
The module descends the orbit map `g ↦ [ρ(g) e_j]` of `Pⁿ` through `q`. The
descended map `Q → Pⁿ` is equivariant for every action of `G` on `Q` that is
compatible with left multiplication. It is a monomorphism when `G` is smooth and
affine and `H` is a smooth closed subgroup. It is a closed immersion when, in
addition, `Q` is proper. This is the projective embedding `G/B → P(V)` used at the
start of the proof of Milne, *Algebraic Groups* (2017), Theorem 17.65, here built
on the supplied model `Q` rather than on a constructed quotient. Combined with
the chart lemma of `Langlands.GroupScheme.ProjectiveDualLineChart`, it turns
linear forms whose lines are fixed by a subgroup into invariant affine opens of
`Q`. The module uses no structure theory of algebraic groups. In particular it
does not prove that `Q` is proper; that is an explicit hypothesis of the last
theorem.

Every declaration is derived from existing Library APIs: projective orbit maps
and their sections (`ProjectiveOrbit`), the fibre description of the orbit map of
a line stabilizer (`ProjectiveLineStabilizerQuotient`), descent through
effective epimorphisms and comparison of quotient models
(`HomogeneousQuotientComparison`), the effective epimorphism `G × q`
(`Dynamic.FlagQuotientAction`), and the scheme quotient with a monomorphism to a
given map (`exists_scheme_quotient_of_map_kernel`). The closed-immersion step
uses Mathlib's characterization of closed immersions as proper monomorphisms.

All declarations are in namespace `Langlands.GroupScheme.ProjectiveOrbit`.

## Sections of test points

Here `R` is a commutative ring, `ambient n R` is projective space `Pⁿ` over
`Spec R`, and `pointSection y` is the section `Z → Pⁿ_Z` of a test point
`y : Z → ambient n R` (from `ProjectiveDualLineChart`).

- `pointSection_naturality`: for a test morphism `c : Z' → Z`, the composite of
  the underlying map of `c` with `pointSection y` equals `pointSection (c ≫ y)`
  followed by the base-change map `Pⁿ_{Z'} → Pⁿ_Z`. The proof checks both
  components of maps into relative projective space.
- `pointSection_matrixAction_naturality`: for a matrix representation `ρ` of a
  group `H`, a test point `h : Z → H` and `c : Z' → Z`, the right-hand side of
  matrix equivariance is natural in the test. That is, `c` followed by
  `pointSection y`, `matrixAction n (ρ.pointMatrix Z h)` and the base-change map
  to `Pⁿ_{Spec R}` equals `pointSection (c ≫ y)`, followed by
  `matrixAction n (ρ.pointMatrix Z' (c ≫ h))` and the base-change map. The proof
  combines the previous lemma, the Library's base-change law for `matrixAction`,
  and naturality of `ρ.pointMatrix`.
- `isMatrixEquivariant_of_universal`: let `a` be an action of `H` on `X` and
  `φ : X → ambient n R`. To prove `IsMatrixEquivariant a ρ φ` it suffices to
  check the defining equality for the universal test `Z = H × X`, `h = fst`,
  `x = snd`. In that case `a.act fst snd` is the action morphism. The proof
  pulls the universal equality back along `lift h x : Z → H × X` with the
  previous lemma.
- `pointSection_orbitMap`: for a representation `ρ` of `G`, a section
  `p : Spec R → Pⁿ_{Spec R}` and a test point `g : Z → G`, the section of the
  test point `g ≫ orbitMap n ρ p` is the Library's orbit section
  `orbitSection n ρ p Z g`, the matrix translate of the pulled-back point. The
  proof uses the Library's uniqueness of sections with a given composite to the
  base and its composite formula `comp_orbitMap`.

## The descended orbit map

From here on `k` is a field and `G, H` are group schemes over `Spec k`. The data
are a homomorphism `i : H → G`, an index `j`, and a representation `ρ` of `G` on
`k^{n+1}`. The hypothesis `hρ` says that for every test `T` a point
`x : T → G` lies in the range of `i` iff `ρ(x) e_j = c • e_j` for some unit `c`
of `Γ(T, ⊤)`. This is exactly the conclusion of
`Chevalley.exists_line_stabilizer`. The quotient data are `q : G → Q` over
`Spec k` with flat, surjective and quasi-compact underlying map. The hypothesis
`hfib` says that, on every test, `g ≫ q = h ≫ q` iff `g⁻¹ h` lies in the range
of `i`. These are the corresponding hypotheses of
`FlagInvariantAffineOpenCoverStatement`, with `H = B`.

- `lineOrbitMap n j ρ` abbreviates the Library's orbit map `G → ambient n k`
  of the coordinate point `e_j` (`RelativeProjectiveSpace.basisSection`); on
  points it is `g ↦ [ρ(g) e_j]`.
- `quotientOrbitMap n i j ρ hρ q hfib : Q → ambient n k` is the descent of
  `lineOrbitMap` through `q` (`HomogeneousQuotientComparison.desc`, which needs
  `q` to be an effective epimorphism; this follows from flat, surjective and
  quasi-compact). Its compatibility hypothesis holds because two points with
  the same image under `q` differ by a point of `H` (`hfib`). By the Library
  lemma `basisSection_orbitMap_fibers` such points have the same image under
  the orbit map.
- `fac_quotientOrbitMap`: `q ≫ quotientOrbitMap … = lineOrbitMap n j ρ`.
- `isMatrixEquivariant_quotientOrbitMap`: let `a` be an action of `G` on `Q`
  such that `a.act g (h ≫ q) = (g * h) ≫ q` on every test. Then
  `quotientOrbitMap` is matrix equivariant for `a` and `ρ`. By
  `isMatrixEquivariant_of_universal` it suffices to check the universal test
  `G × Q`. Both sides are maps out of `(G × Q).left`, and `G × q` is an effective
  epimorphism, so it suffices to compare them after composing with `G × q`.
  After that composition the left side becomes `(g * h) ≫ q ≫ quotientOrbitMap`
  for the two projections `g, h` of `G × G`. That is the orbit map at `g * h`,
  that is `ρ(g * h) = ρ(g) ρ(h)` applied to `e_j`. The right side becomes, by
  `pointSection_matrixAction_naturality`, the matrix action of `ρ(g)` on the
  section of `h ≫ q ≫ quotientOrbitMap`, which is the orbit section at `h`. The
  two agree by multiplicativity of `ρ.pointMatrix` and the composition law of
  `matrixAction`.
- `mono_quotientOrbitMap`: assume `G` is smooth and affine over `k`, `i` is a
  closed subgroup and `H` is smooth. Then the underlying scheme map of
  `quotientOrbitMap` is a monomorphism. The proof applies
  `exists_scheme_quotient_of_map_kernel` to the equivalence relation of right
  translation by `H` (`HomogeneousQuotientFromEmbedding`) and to the orbit map.
  The kernel hypothesis holds by `basisSection_orbitMap_fibers`. This gives a
  quotient `q' : G → Q'` and a map `e : Q' → ambient n k` with `q' ≫ e` equal to
  the orbit map and `e` a monomorphism on underlying schemes. Here `q'` is
  smooth and surjective. `Q'` is separated over `k`, since `e` is a
  monomorphism to the separated projective space. So `q'` is quasi-compact,
  because its composite with the separated map `Q' → Spec k` is the
  quasi-compact structure map of the affine `G`. The
  maps `q` and `q'` have the same fibres on every test. So
  `HomogeneousQuotientComparison.iso` gives an isomorphism `c : Q ≅ Q'`
  compatible with the projections. Uniqueness of descent gives
  `quotientOrbitMap = c.hom ≫ e`. This is an isomorphism followed by a
  monomorphism.
- `isClosedImmersion_quotientOrbitMap`: under the hypotheses of the previous
  lemma, assume also that `Q` is proper over `k` (`IsProper Q.hom`). Then the
  underlying map of `quotientOrbitMap` is a closed immersion. It is proper,
  since its composite with the separated structure map of projective space is
  the proper map `Q → Spec k`. A proper monomorphism is a closed immersion
  (Mathlib, `IsClosedImmersion.iff_isProper_and_mono`).

A closed immersion is an affine morphism, so `isClosedImmersion_quotientOrbitMap`
supplies the hypothesis `IsAffineHom φ.left` of
`ProjectiveOrbit.isAffineOpen_isInvariantOpen_preimage_translatedChart`.
Properness of a quotient by a Borel subgroup is not proved here.
