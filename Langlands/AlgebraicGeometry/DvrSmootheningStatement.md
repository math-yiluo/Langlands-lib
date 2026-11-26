# Smoothenings over a discrete valuation ring

The module `Langlands.AlgebraicGeometry.DvrSmootheningStatement` states the existence of
smoothenings of schemes of finite type over a discrete valuation ring, in the form that
lifts points with values in extensions of ramification index one. It contains a
definition and a proposition and proves nothing.

## Source

Siegfried Bosch, Werner Lütkebohmert and Michel Raynaud, *Néron Models*, Ergebnisse der
Mathematik und ihrer Grenzgebiete (3) 21, Springer, 1990 (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`):

- §3.1, Definition 1 and Theorem 3 (smoothening process), printed pp. 60–61;
- §3.6, Definition 1 (ramification index 1), printed p. 78;
- §3.6, Lemma 5, printed p. 79: for a smoothening `X' → X` and an extension `R'/R` of
  ramification index 1, every `R'`-valued point of `X` lifts to an `R'`-valued point of
  `X'` which factors through the smooth locus of `X'`.

## `IsRamificationIndexOne`

For local rings `R`, `R'` and a local homomorphism `R → R'`,
`IsRamificationIndexOne R R'` asserts:

1. `(maximalIdeal R).map (algebraMap R R') = maximalIdeal R'`, and
2. `Algebra.IsGeometricallyReduced (ResidueField R) (ResidueField R')`.

BLR 3.6/1 calls a flat local extension `R → R'` of discrete valuation rings of
ramification index 1 if a uniformizing element of `R` induces a uniformizing element of
`R'` and the residue field extension `k'/k` is separable; BLR recall that `k'/k` is
separable if and only if `k' ⊗_k l` is reduced for all field extensions `l/k`.

- For discrete valuation rings, condition 1 is equivalent to the image of a uniformizer
  of `R` being a uniformizer of `R'`, since both maximal ideals are principal.
- Mathlib's `Algebra.IsGeometricallyReduced k k'` for fields says that
  `AlgebraicClosure k ⊗_k k'` is reduced. For a field extension this is separability in
  the sense used by BLR. Given a field extension `l/k`, choose an algebraically closed
  extension `l'` of `l`; it contains a copy `k̄` of `AlgebraicClosure k`. The ring
  `k' ⊗_k l` embeds in `k' ⊗_k l' = (k' ⊗_k k̄) ⊗_k̄ l'`, and a reduced algebra over the
  algebraically closed field `k̄` stays reduced after the field extension `l'/k̄`. So
  `k' ⊗_k l` is reduced for every `l` once it is for `AlgebraicClosure k`; the converse
  is the case `l = AlgebraicClosure k`.
- Flatness is not listed. Between discrete valuation rings, condition 1 forces the
  homomorphism to be injective: its kernel is a prime ideal of `R` and is not the
  maximal ideal, whose image generates the nonzero maximal ideal of `R'`. An injective
  homomorphism from a discrete valuation ring makes `R'` torsion-free, hence flat.

## `DvrSmootheningStatement`

The proposition quantifies over a universe `u`, a discrete valuation ring `R` with
fraction field `K`, a scheme `X` and a morphism `f : X ⟶ Spec R` which is locally of
finite type and quasi-compact (so of finite type, BLR's hypothesis), and whose generic
fibre `pullback.snd f (Spec K ⟶ Spec R)` is smooth. It asserts a scheme `X'` and a
morphism `g : X' ⟶ X` such that

- `g` is proper;
- `g` is an isomorphism on generic fibres: the induced morphism
  `pullback.map … g (𝟙 _) (𝟙 _)` from `X' ×_R K` to `X ×_R K` is an isomorphism;
- for every discrete valuation ring `R'` in the same universe with a local homomorphism
  `R → R'` of ramification index one, and every `R'`-valued point
  `a : Spec R' ⟶ X` over `Spec R`, there are an open `U` of `X'` which is smooth over
  `R` (the morphism `U.ι ≫ g ≫ f` is smooth) and `a' : Spec R' ⟶ U` with
  `a' ≫ U.ι ≫ g = a`.

The last clause says that `a` lifts to an `R'`-valued point of `X'` factoring through the
smooth locus of `X'` over `R`: an open subscheme smooth over `R` lies in the smooth locus,
and the smooth locus is such an open.

### Correspondence with the source

BLR 3.1/1 defines a smoothening as a proper morphism `f : X' → X`, an isomorphism on
generic fibres, such that `X'_smooth(R') → X(R')` is bijective for every étale
`R`-algebra `R'`. BLR 3.1/3 asserts that every `R`-scheme of finite type with smooth
generic fibre admits one, and BLR 3.6/5 shows that a smoothening also lifts `R'`-valued
points for every extension `R'/R` of ramification index 1. The proposition is the
conjunction of these two results for extensions `R'` that are discrete valuation rings
in the universe of `R`. Local étale extensions of `R` are such extensions (BLR 3.1, after
Definition 1, and 3.6, after Definition 1), so the proposition gives the étale lifting
property of BLR 3.1/1 for local étale `R`-algebras. For an arbitrary étale `R`-algebra
`R'` and an `R'`-valued point `a` of `X`, it follows by localization, as in BLR 3.1
after Definition 1:

- at a prime of `R'` over the closed point of `Spec R`, the local ring of `R'` is a local
  étale extension of `R`, hence of ramification index one, and the restriction of `a`
  lifts to a point of the smooth locus of `X'`;
- over the generic point of `Spec R`, the restriction of `a` lifts through the
  isomorphism of generic fibres, and the generic fibre of `X'` lies in the smooth locus
  of `X'` because it is isomorphic to the smooth generic fibre of `X` and is open in `X'`;
- since `X'` is locally of finite presentation over the noetherian ring `R`, each of
  these local lifts extends to a morphism from an open neighbourhood of the prime in
  `Spec R'`; after shrinking the neighbourhood it still lies over `a`, because `X` is of
  finite type over `R`, and it still lands in the smooth locus, which is open;
- two lifts of `a` agree on the overlap of their domains: they agree on the generic
  fibre, where `g` is an isomorphism, the generic fibre of the flat `R`-scheme `Spec R'`
  is schematically dense, and `g` is separated.

The local lifts therefore glue to a lift of `a` through the smooth locus of `X'`.

Uniqueness of the lift is not stated. It holds automatically: an `R'`-valued point of
`X'` over `a` restricts over the fraction field of `R'` to a point of the generic fibre,
where `g` is an isomorphism, and two such lifts agree by the valuative criterion of
separatedness for the proper morphism `g`.

The proposition omits the additional information of BLR 3.1/3 that the smoothening can
be built as a finite sequence of blowing-ups with centres in the special fibres, and that
it is quasi-projective when `X` is.

## Use

For a proper flat model of an abelian variety, the smooth locus of a smoothening is a
smooth model in which every point over an extension of ramification index one extends.
Local rings of smooth `R`-schemes at the generic points of their special fibres are such
extensions (BLR 3.6, after Definition 1), which gives the weak Néron mapping property of
BLR 3.5/3 used in the construction of Néron models (BLR §1.3, printed pp. 16–18).
