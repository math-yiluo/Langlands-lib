# Twisted character values at σ-regular elements

`twistedCharacterRegularValues` proves the Library's
`TwistedCharacterRegularValuesStatement` with its three universe parameters free.
Let `F` be a nonarchimedean local field of characteristic zero, `E` a cyclic
`F`-algebra for `σ` of order `l` with its module topology, `τ` an irreducible
admissible representation of `GL_n(E)`, `A` an isomorphism of `τ` onto `τ^σ` and
`δ` a σ-regular element. Then the twisted character `φ ↦ trace(τ(φ) ∘ A)` has a
value at `δ` in the sense of `HasTwistedCharacterValue`. This is the local
constancy part of Arthur–Clozel (1989), Chapter 1, Proposition 2.2 (printed
p. 11), for the cyclic algebras of Henniart–Lemaire (2011), II.2.8 (printed
pp. 67–69).

The proof is one line: `twistedCharacterRegularValues_of_compactSubmersion`
(module `Langlands.BaseChange.TwistedCharacterRegularValuesGeometry`) applied to
`Langlands.HarmonicAnalysis.compactSubmersionPushforward`. The route is
Harish-Chandra's compact averaging argument in *A submersion principle and its
applications* (1981), §§2–4 (printed pp. 96–100), applied to twisted
conjugation; it does not use the local character expansion or local
integrability.

1. `GeneralLinear.finiteAlgebraUpperTriangularCartan` gives a compact open
   subgroup `K` of `GL_n(E)` and representatives `M` with `GL_n(E) = K M K`, and
   for every open subgroup `U` a compact open subgroup `L` of the upper
   triangular group with `m⁻¹ L m ⊆ U` for all `m ∈ M`.
2. At a σ-regular `δ`, `twistedConjugationMatrixSubmersion` shows that the twisted
   product `(y, k, p) ↦ k y σ(k)⁻¹ σ(p)` in matrix coordinates has a joint strict
   derivative at `(δ, k, p)` that is onto in the source directions `(k, p)`, for
   every invertible `k` and invertible upper triangular `p`. The characteristic
   zero hypothesis and `σ^l = 1` enter here.
3. `compactSubmersionPushforward` (Harish-Chandra's submersion principle in
   additive coordinates, with its locally constant dependence on the parameter,
   §3, Lemma 1) then gives one pushforward measure of `K × L` for all parameters
   near `δ`. The Haar chart of
   `Langlands.BaseChange.TwistedCharacter.MatrixHaarChart` transfers this to the
   product of the normalized Haar measures of `K` and `L`.
4. `twistedCharacterRegularValuesReduction` turns these data into the value. The
   averaged operators `∫_K τ(k) τ(y) A τ(k)⁻¹ dk = ∫_K τ(k y σ(k)⁻¹) dk ∘ A`
   (`conjugationAverage`) are equal for all `y` near `δ`; these are the twisted
   analogues of Harish-Chandra's operators `T_x` of §4, Theorem 2.
   The equality is first proved on the vectors `τ(m) τ(j) v` (`m ∈ M`, `j ∈ K`,
   `v ≠ 0`), which `L` fixes after contraction, by integrating against the
   pushforward measures; equivariance under `K` and the Cartan covering extend
   it to the orbit `τ(GL_n(E)) v`, which spans by irreducibility. Admissibility
   makes the operator of finite rank, and smearing identifies its trace with
   the local value for every Haar measure (the twisted form of §4, Corollary).

`ordinaryRegularSemisimpleCharacterValues_charZero` is the degree-one case: for a
nonarchimedean local field `F` of characteristic zero it proves
`JacquetLanglands.HasRegularSemisimpleCharacterValues F n`, that every
irreducible admissible representation of `GL_n(F)` has a character value at
every regular semisimple element. It applies
`SigmaLiftCharacterIdentity.ordinary_regular_values`, which takes `E = F`,
`σ = 1`, `l = 1` and the identity intertwiner, to
`twistedCharacterRegularValues.{u, u, uW}`. This is Harish-Chandra's theorem that
characters are locally constant on the regular set (1981, §4, Corollary, printed
pp. 99–100), here in characteristic zero.

Sources: Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of
the Trace Formula* (1989), source `arthur-clozel-1989-base-change`;
Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle* (2011), source
`provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`;
Harish-Chandra, *A submersion principle and its applications*, Proc. Indian
Acad. Sci. (Math. Sci.) 90 (1981), 95–102, source
`harish-chandra-1981-submersion-principle`.
