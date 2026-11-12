# Multiplicity one for the cuspidal spectrum of `GL_n`

Module `Langlands.Automorphic.GeneralLinearCuspidalMultiplicityOneStatement`
states `Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearCuspidalMultiplicityOneStatement`
as a proposition definition. It supplies no proof. The two local instances
supply `IsAffine` and `Smooth` for the general linear group scheme from the
published `isAffine_groupScheme` and `smoothStatement`.

## Sources

- J. Getz and H. Hahn, *An introduction to automorphic representations*
  (2024), registered as `getz-hahn-2024-automorphic-representations`:
  - Theorem 11.4.3, p.303 (PDF page 314): "An irreducible admissible
    representation of `GL_n(𝔸_F)` occurs with multiplicity at most one in
    `L²_cusp([GL_n])`." The proof on the same page takes two realizations
    `V_1, V_2 ≤ L²_cusp([GL_n])` of a cuspidal automorphic representation
    `(π, V)` with equivariant maps `L_i : V → V_i`. It compares the Whittaker
    functionals `φ ↦ W^{L_i(φ)}_ψ(I_n)`, which are nonzero by Theorem 11.3.6
    and proportional by Theorem 11.3.4 and Proposition 11.4.2. The Whittaker
    expansion (11.8) then gives `L_1 = c L_2`, so `V_1 ∩ V_2 ≠ 0` and
    `V_1 = V_2`.
  - Theorem 11.3.4, p.295 (PDF page 306): local uniqueness of Whittaker
    functionals. Proposition 11.4.2, p.302 (PDF page 313): factorization of
    the global Whittaker model.
  - §9.1, p.241 (PDF page 253): `φ ∈ L²([G])` is cuspidal if
    `∫_{[N]} φ(ng) dn = 0` for almost every `g ∈ A_G \ G(𝔸_F)` and every
    proper parabolic `P` with unipotent radical `N` (recalled from (6.20)).
    `L²_cusp([G])` is the subspace of cuspidal `φ`. Corollary 9.1.3 on the
    same page: it is a Hilbert direct sum of irreducible representations,
    each with finite multiplicity.
- J. A. Shalika, *The multiplicity one theorem for GL_n*, Ann. of Math. 100
  (1974), registered as `shalika-1974-multiplicity-one` (PDF page = printed
  page − 169), §5, p.187 (PDF page 18): the space of cusp forms with central
  character `ρ`, defined by (5.1)–(5.4), and Theorem 5.5: "Each irreducible
  unitary representation of `G_A` occurs with multiplicity at most one in
  `𝒞_ρ`."

## Statement

The data are a number field `F : Type u` and `n : ℕ`, with
`G = GL_n = GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)`:

- `hPD : ParabolicDynamicStatement`, the standing structural hypothesis of
  the Library's cuspidal `L²` spaces (it supplies the actual proper rational
  parabolics and their radicals);
- a commutative group scheme `T` with `i : T → GL_n` central (`IsCentral i`),
  `e : T ≅` a split torus on a finite type `I`, injective character restriction
  `characterRestrict i` with finite-index image. For `T = G_m`, the centre of
  `GL_n`, these hold;
- right invariance of Haar measure on the norm-one subgroup `GL_n(𝔸)^1`,
  which is the premise of the Library's right action.

The connected reductivity of `GL_n` is not a hypothesis. It is supplied by
the published `GroupScheme.isConnectedReductive_generalLinear`. Let
`S = fullAEL2CuspidalSubmodule F GL_n hPD hG T i hi I e hc` and
`πc = fullAEL2CuspidalBoundedRightAction` (module
`Langlands.Automorphic.GroupSchemeFullAEL2Integrated`). The statement says:
let `P` and `Q` be submodules of `S`, each nonzero, closed, invariant under
`πc a` for every `a ∈ GL_n(𝔸)`, and minimal (every closed invariant
submodule of it is `0` or all of it). Suppose there is a complex-linear
isometric equivalence `U : P ≃ Q` with `U(πc a x) = πc a (U x)` for all
`a` and `x ∈ P`. Then `P = Q`.

## Correspondence with the sources

- The space. `S` is the Library's full almost-everywhere cuspidal subspace
  of `L²` of the positive-central rational quotient `PositiveRationalQuotient
  F GL_n T i`, with the norm-one transported Haar measure (Markdown of
  `Langlands.Automorphic.GroupSchemeFullAEL2`). Its elements are the classes
  whose period along the unipotent radical of every proper rational
  parabolic converges and vanishes almost everywhere. This is Getz–Hahn's
  cuspidality condition (6.20), recalled on p.241. The quotient is by the
  rational points and the positive image of `T`: the points of `T(𝔸)` all
  of whose characters take values in the positive reals embedded diagonally
  at the archimedean places (Mœglin–Waldspurger I.2.1; Markdown of
  `Langlands.Global.PositiveRealTorusIntrinsic`). For the centre `G_m` of
  `GL_n` this image is `A_{GL_n}`, so the quotient is Getz–Hahn's
  `[GL_n] = A_{GL_n} GL_n(F) \ GL_n(𝔸_F)`. For every admissible datum the
  quotient is homeomorphic to `GL_n(F) \ GL_n(𝔸)^1`
  (`positiveQuotientHomeomorph`, Markdown of
  `Langlands.Global.AdelicSplitCenterQuotient`). The action `πc` is right
  translation.
- "Occurs with multiplicity at most one". Getz–Hahn's proof compares two
  realizations `V_1, V_2` of one representation. Here they are two minimal
  nonzero closed invariant subspaces `P`, `Q`, the irreducible
  subrepresentations, and "realization of the same representation" is an
  intertwining isometric equivalence. Getz–Hahn's Corollary 9.1.3 states the
  multiplicities in the same sense. The Library's
  `GroupSchemeFullAEL2CuspidalDecompositionStatement` and
  `CompactApproximationMultiplicityStatement` use the same notion, so the
  present statement says that each multiplicity in that decomposition is
  one. Two distinct irreducible closed invariant subspaces meet in `0`.
  Hence, if multiplicity two occurred, it would give such `P ≠ Q`.
  Conversely, the statement excludes this. For irreducible unitary
  representations, a bounded intertwining bijection gives an isometric one
  (polar decomposition and Schur's lemma). By Harish-Chandra, an algebraic
  isomorphism of the `K`-finite vectors does the same, so formulations with
  weaker equivalences are equivalent to this one. This is classical and not
  proved here. Irreducibility of `Q` follows from that of `P` and `U`, but it
  is stated for symmetry.
- Central characters. Shalika fixes a unitary central character `ρ` and
  works in the cusp forms `𝒞_ρ`. Getz–Hahn, like the present statement, work
  in `L²_cusp([GL_n])` without fixing it. An irreducible subspace has a
  central character, by Schur's lemma, and equivalent subspaces have the
  same one. So the two forms are equivalent. Getz–Hahn's representations are
  representations of `A_{GL_n} \ GL_n(𝔸_F)`. `A_{GL_n}` acts trivially on
  `[GL_n]`, so the invariant subspaces for `GL_n(𝔸_F)` and for
  `A_{GL_n} \ GL_n(𝔸_F)` are the same.
- Admissibility. Getz–Hahn speak of an irreducible admissible
  representation. Admissibility of the irreducible subrepresentations of
  `L²_cusp` is a separate theorem and plays no role in the formulation.
- Generality. The statement is for every `n`. For `n = 0` the space is
  one-dimensional. For `n = 1` there is no proper parabolic, so `S` is all
  of `L²`, and the statement is multiplicity one for `L²` of the compact
  abelian group `A_{GL_1} F^× \ 𝔸^×` (its characters are pairwise
  orthogonal). It quantifies over every central split torus
  datum `(T, i, e)` with injective finite-index character restriction, not
  only the centre. `hPD` and the norm-one invariance premise are the
  hypotheses of the Library's construction of `S` and `πc`.

## Proof route (not part of the statement)

Getz–Hahn's proof uses the Whittaker expansion. The expansion is the staged
`WhittakerExpansionStatement` (module
`Langlands.Global.GeneralLinearWhittakerExpansionStatement`), on smooth
functions on `GL_n(F) \ GL_n(𝔸)`. Applying it requires smooth vectors of `P`
and `Q` that are smooth functions of uniform moderate growth. The proof also
uses local uniqueness of Whittaker functionals at every place (Getz–Hahn
11.3.4; the Library proves the `p`-adic case as `Langlands.Whittaker.multiplicityOne`),
the archimedean case and the factorization of Proposition 11.4.2.

## Scope

Only multiplicity one is stated. The statement does not assert
that the irreducible subspaces of `S` are generic, the decomposition of
Corollary 9.1.3, strong multiplicity one (Getz–Hahn 11.7.2) or the
closedness of `S` in `L²`.
