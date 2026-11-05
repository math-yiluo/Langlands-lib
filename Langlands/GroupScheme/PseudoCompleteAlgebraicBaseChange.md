# Descent of the DVR lifting property along algebraic field extensions

Author: Worker 254.

This module proves the descent of the published DVR lifting property
`PseudoComplete.HasDVRLifting` from `Langlands.GroupScheme.PseudoComplete`,
the valuative half of pseudo-completeness, along algebraic field extensions.

## Results

`PseudoComplete.hasDVRLifting_of_baseChange`: let `k L : Type u` be fields with
`[Algebra k L]` and `[Algebra.IsAlgebraic k L]`, and let
`X : Over (Spec (CommRingCat.of k))`. Write `b` for
`Spec.map (CommRingCat.ofHom (algebraMap k L))`. If the base change
`(Over.pullback b).obj X` has `HasDVRLifting` over `L`, then `X` has
`HasDVRLifting` over `k`.

No hypothesis on `X` is needed: it need not be separated or of finite type.
The theorem gives only the descent direction. It says nothing about properness
or about the converse.

## Provenance

Conrad–Gabber–Prasad, *Pseudo-reductive groups*, second edition (2015),
Proposition C.1.2(2), printed pp.582–583 (PDF pp.608–609), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`. The first assertion of C.1.2(2)
is that, for any field extension `k'/k`, a `k`-scheme `X` is pseudo-complete
over `k` if `X_{k'}` is pseudo-complete over `k'`. The proof of Proposition C.1.6
(printed p.586, PDF p.612) uses this to pass to a separable closure `k_s`
("it is harmless to make a separable extension on `k`, so we can assume
that `k = k_s`").

The source handles an arbitrary extension `k'/k`. This module treats only
algebraic `L/k`, which covers the separable closure. Pseudo-completeness in the
Library is the structure `Langlands.GroupScheme.IsPseudoComplete`, whose fields
are `isSeparated`, `locallyOfFiniteType`, `quasiCompact` and `dvrLifting`
(`PseudoComplete.HasDVRLifting`). This module proves only the descent of the
last field. The source's argument in this direction is the one formalized here:
pass from `R` to a DVR `R'` over `L` with geometrically reduced residue field,
lift the generic point there, and descend the lift by the domination property
`X(R) = X(R') ∩ X(K)` from the proof of C.1.2(3).

## Implemented proof

Let `R` be a DVR over `k` with geometrically reduced residue field, and let
`x : algebraSpec k (FractionRing R) ⟶ X`.

1. Choose a uniformizer `ϖ` of `R`
   (`IsDiscreteValuationRing.exists_irreducible`) and, by
   `DVRAlgebraicBaseChange.exists_isPrime_tmul_mem`, a prime `m` of
   `L ⊗[k] R` containing `1 ⊗ ϖ`. Set `R' = Localization.AtPrime m`. By
   `isDomain_localization`, `isDiscreteValuationRing_localization` and
   `isGeometricallyReduced_residueField` in
   `Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange`, `R'` is a DVR whose
   residue field is geometrically reduced over `L`. The map
   `f = toLocalization k L R m : R → R'` is injective and local.
2. Let `a` be the restriction of `x.left` along `fractionRingMap f hf`, from
   `Spec (FractionRing R')` to `X.left`. Its composite with `X.hom` equals the
   spectrum of `L → FractionRing R'` followed by `b`. This follows from
   `Over.w x`, the scalar towers `k → R → FractionRing R` and
   `L → R' → FractionRing R'`, `fractionRingMap_algebraMap`, and the fact that
   `toLocalization` is a `k`-algebra map. So `pullback.lift` gives a morphism
   into the fibre product, and `Over.homMk` makes it a relative morphism
   `xL : algebraSpec L (FractionRing R') ⟶ (Over.pullback b).obj X`.
3. The hypothesis, applied to `R'` and `xL`, gives `yL` with
   `genericPoint R' ≫ yL = xL`. Take the underlying morphisms and compose with
   `pullback.fst`. Then `y = yL.left ≫ pullback.fst X.hom b`, a morphism from
   `Spec R'` to `X.left`, restricts on `Spec (FractionRing R')` to `a`.
4. `PseudoComplete.exists_comp_eq_of_dominates` from
   `Langlands.GroupScheme.PseudoCompleteDomination` gives
   `z : Spec R ⟶ X.left` restricting to `x.left`. This is the domination step,
   and needs `R` a valuation ring and `f` injective and local.
   `PseudoComplete.exists_extension_of_comp_eq` turns `z` into the required
   relative morphism `xR : algebraSpec k R ⟶ X` with
   `genericPoint R ≫ xR = x`.
