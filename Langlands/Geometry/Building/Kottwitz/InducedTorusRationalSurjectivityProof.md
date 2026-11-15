# Proof of KP Corollary 11.1.9: the rational Kottwitz map of an induced torus is surjective

`inducedTorusKottwitzRationalSurjectivity` proves the unchanged published
proposition `InducedTorusKottwitzRationalSurjectivityStatement`
(module `Langlands.Geometry.Building.Kottwitz.InducedTorusRationalSurjectivityStatement`),
with no premises. The statement: for every nonarchimedean local field `F` and
every induced torus `T` over `F` (`hT : IsInducedTorus T`), the constructed map
`torusKottwitzRational F T hT.isTorus : T(F) → X_*(T)_I^Γ` is surjective. The
source is Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023),
Corollary 11.1.9, printed p. 425 / PDF p. 456. The statement's Markdown
describes it in full.

## Route

KP prove the corollary through restriction of scalars (Lemma 11.1.8), reducing
to `𝔾_m`. This proof avoids Lemma 11.1.8 and the Weil-restriction decomposition.
It works directly with a Galois-permuted cocharacter basis and the norm law of
KP Proposition 11.1.1, as proved in the Library (`torusKottwitzExistence`,
`torusKottwitzDescent`). Notation: `K = UnramifiedClosure F`,
`Ω = SeparableClosure F`, `H = relativeInertia F K Ω` (KP's `I`), `κ` the
constructed `K`-point map `torusKottwitz F F T`.

1. **Fields.** `exists_finiteGaloisSplittingField_inside` gives a finite Galois
   intermediate field `E` of `Ω/F` splitting `T`.
   `IsInducedTorus.exists_permuted_basis` gives a character basis `b` of `T_E`,
   indexed by a finite `J`, permuted by `Gal(E/F)`.
   `exists_galois_splitting_containing` (proved here) gives a finite Galois
   extension `L = K(a)` of `K` inside `Ω` that contains `E` and splits `T`. Here
   `a` is a primitive element of `E/F`; the construction is that of the Library's
   `exists_normal_splitting`.
2. **Bases and action.** `Gal(Ω/F)` acts on `J` through `Gal(E/F)`
   (`MulAction.compHom` with `InducedCocharacterBasis.galoisIndexHom`), and it
   permutes the geometric cocharacter basis `geometricBasis` dual to `b`
   (`InducedCocharacterBasis` and `galoisRepresentation_geometricBasis_smul`).
3. **Target class.** Let `c ∈ X_*(T)_I^Γ`. Choose `ν ∈ X_*(T)` with
   `proj ν = c` (`Representation.Coinvariants.mk_surjective`). Let
   `n j = orbitSum ν j` be the `H`-orbit sums of the coordinates of `ν`.
   `orbitSum_galois_invariant` (proved here) shows `n` is `Gal(Ω/F)`-invariant.
   Proof: `c` is fixed by every `σ|_K`. By `inertiaGammaRepresentation_restrict`
   this says `proj (σ ν) = proj ν`, and then apply
   `PermutationCoinvariants.orbitSum_smul_of_mk_eq`.
4. **Rational point.** `UniformizerFamily.exists_family` gives a
   `Gal(E/F)`-equivariant family `u : J → Eˣ` whose `L`-orders have every
   `H`-orbit sum equal to `[L : K]`. `zpow_family_equivariant` (proved here) shows
   that `x j = u j ^ n j` is still equivariant, since `n` is invariant. Then
   `InducedCocharacterBasis.exists_rationalPoint` gives `t ∈ T(F)` whose extension
   to `E` is `∏ⱼ (dualBasis j)(x j)`.
5. **Kottwitz value.** `InducedCocharacterBasis.torusKottwitz_eq_of_family`
   gives `κ(t) = proj ν = c`. It applies the norm law at `L`, which yields
   `[L : K] • κ(t) = proj (∑ⱼ n j · ord_L(u j) • e_j)`. The orbit-sum condition
   identifies the right side with `proj ([L : K] • ν)`. The inertia coinvariants
   are torsion free (`PermutationCoinvariants.zsmul_cancel`), which removes the
   factor `[L : K]`.
6. **Restriction.** The restriction law of `torusKottwitzDescent` says that the
   inclusion of `torusKottwitzRational F T hT.isTorus t` into `X_*(T)_I` is
   `κ(t)`. The inclusion is a subtype map, so `torusKottwitzRational … t = c`.

`torusKottwitzRational_surjective_of_basis` carries out steps 3–6 for given
`E`, `b`, `L` and action data. The final theorem obtains these data in steps 1–2
and applies it.

## Supporting modules

All are new internal modules of this contribution:

* `Kottwitz.CompositumUniformizer`: for a finite extension `E'` of `F` in `Ω`,
  every absolute value on `K ⊔ E'` is attained on `E'`. Hence a finite extension
  of `K` inside `K ⊔ E'` that contains `E'` has a uniformizer in `E'`.
* `Kottwitz.PermutationCoinvariants`: orbit sums on coinvariants of permutation
  lattices; injectivity and torsion freeness.
* `Kottwitz.InducedCocharacterBasis`: dual and geometric permuted cocharacter
  bases, and descent of equivariant unit families to rational points.
* `Kottwitz.InducedTorusNormValue`: the norm-law computation and the
  cancellation of `[L : K]`.
* `Kottwitz.InducedTorusUniformizerFamily`: the equivariant uniformizer family
  and the count of inertia orbits.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
