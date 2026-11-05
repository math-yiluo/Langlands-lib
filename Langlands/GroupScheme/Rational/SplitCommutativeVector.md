# Commutative split groups of exponent `char k` are vector groups

Module: `Langlands.GroupScheme.Rational.SplitCommutativeVector`.

This helper module serves the proof of
`Langlands.GroupScheme.RelativeRoot.SplitUnipotentStableVectorSubgroupStatement`
(task 6b07dcd2-af39-4c69-8ade-d0faa997a49f). Its main result is
`isVectorGroup_of_isSplitUnipotent_of_exponent`. Let `W` be a group scheme over a field
`k`, affine over `Spec k`, whose points commute. Assume `W` is split unipotent (it has a
Library `HasSplitSeries`), and that every point `x` of `W`, on every scheme over `Spec k`,
satisfies `x ^ ringChar k = 1`. Then `W` is a vector group. In characteristic `0` the exponent
condition is `x ^ 0 = 1`, which always holds. So the theorem then says that every commutative
affine split unipotent group is a vector group.

In characteristic `p` this is a special case of classical results on smooth connected
commutative `p`-torsion unipotent groups (Conrad–Gabber–Prasad, *Pseudo-reductive groups*,
2nd ed., Appendix B, Theorem B.2.5 and Corollary B.2.6). The proof here does not follow that
route; it was worked out for this formalization. It is an induction along the split series.
Each step is an extension `K ⟶ W ⟶ V` with `V` a one-dimensional vector group. A section
`s` of `W ⟶ V` is a morphism of schemes, in general not a homomorphism; its failure to be
multiplicative is a polynomial 2-cocycle with values in `K`. The polynomial
cocycle lemma `Langlands.Algebra.PolynomialCocycle.exists_coboundary` shows that this
cocycle is a polynomial coboundary. Correcting `s` by that coboundary gives a homomorphic
section, so `W ≅ K × V` as groups.

Throughout, `k : Type u` is a field. Group schemes are Library `GroupScheme (Spec
(CommRingCat.of k))`. A *point* of a group scheme `G` is a morphism `T ⟶ G.X` in
`Over (Spec (CommRingCat.of k))`; points form a group. An *affine point* over a commutative
`k`-algebra `A : Type u` is a point on `Spec A` (the Library `Lie.AffinePoints G A`). For a
vector group with coordinates `e`, `vectorAffineCoordinates e A` is the Library
identification of its affine points over `A` with `Multiplicative (Fin d → A)`.
*Coordinates* `e` of `V` below are families of group isomorphisms
`e T : (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))`. They are *natural* when they
satisfy the Library `IsNaturalVectorCoordinates e`; this is what `IsVectorGroupOfDimension`
provides.

Everything below is in the namespace `Langlands.GroupScheme.RelativeRoot`. The helper
lemmas are in its sub-namespace `SplitCommutativeVector`.

## Identities in commutative groups

For a commutative group `G` and elements of `G`:

- `cocycle_identity a b c d e f`:
  `a b c⁻¹ · (c d e⁻¹) = b d f⁻¹ · (a f e⁻¹)`.
- `torsion_identity a b c d e f h`: if `a e = b d`, then `a (e c f⁻¹) f = b c d`.
- `section_identity a b c d e`: `e (a b e⁻¹ c d) = a c (b d)`.
- `kernel_identity a b c d`: `a b (c d)⁻¹ = a c⁻¹ (b d⁻¹)`.

All are proved in `Additive G` by `abel`.

## Coordinates on a one-dimensional vector group

Let `V` and `Z` be group schemes over `Spec k`, with coordinates `eV` of dimension `1` on `V`
and `eZ` of dimension `m` on `Z`. Let `A`, `B` be commutative `k`-algebras in `Type u`.

- `linePoint eV A a`: the affine point of `V` over `A` whose coordinate under
  `vectorAffineCoordinates eV A` is `a ∈ A`.
- `lineCoord eV x`: the coordinate in `A` of an affine point `x` of `V` over `A`.
- `lineCoord_linePoint` and `eq_linePoint`: `lineCoord (linePoint a) = a` and
  `x = linePoint (lineCoord x)`.
- `linePoint_mul`: `linePoint a * linePoint b = linePoint (a + b)`.
- `linePoint_pow`: `linePoint a ^ i = linePoint (i * a)` for `i : ℕ`.
- `linePoint_zero`: `linePoint 0 = 1`.
- `linePoint_pow_ringChar`: `linePoint a ^ ringChar k = 1`, because `ringChar k` is `0`
  in the `k`-algebra `A`.
- `affineMap_linePoint heV f a`: if `eV` is natural, then for a `k`-algebra map
  `f : A →ₐ[k] B` the Library base change `Lie.affineMap V f` sends `linePoint a` to
  `linePoint (f a)`.
- `exists_bivariate heV heZ F`: let `eV` and `eZ` be natural and `F : V.X ⊗ V.X ⟶ Z.X` a
  morphism. Then there are bivariate polynomials `c : Fin m → k[X][X]` such that for every
  `A` and `a, b ∈ A`, the `i`-th coordinate of `lift (linePoint a) (linePoint b) ≫ F` under
  `vectorAffineCoordinates eZ A` is `aevalAeval a b (c i)`. Here `aevalAeval a b`
  substitutes `a` for the inner and `b` for the outer variable (Mathlib's
  `Polynomial.Bivariate`). The polynomials are the coordinates of `F` at the universal pair
  `(C X, X)` over `k[X][X]`; the general case follows by naturality along
  `aevalAeval a b : k[X][X] →ₐ[k] A`.

Now assume also that `V` is affine over `Spec k` (`[IsAffineHom V.X.hom]`).

- `universalAlgebra V`: the coordinate algebra `Γ(V)` of `V`, as an object of
  `CommAlgCat (CommRingCat.of k)`.
- `universalPoint V`: the affine point of `V` over `universalAlgebra V` corresponding to
  the identity of `V.X` (via the Library `Lie.affinizationFactor`).
- `polyMap eV eZ g`: for `g : Fin m → k[X]`, the morphism of schemes `V.X ⟶ Z.X` given in
  coordinates by `t ↦ (g i (t))_i`. It is the unit `V.X ⟶ Spec Γ(V)` of the
  `algΓ`–`algSpec` adjunction followed by the affine point of `Z` over `Γ(V)` with
  coordinates `aeval (lineCoord (universalPoint V)) (g i)`.
- `polyMap_coord heV heZ g A a i`: for natural `eV` and `eZ`, the `i`-th coordinate of
  `linePoint a ≫ polyMap eV eZ g` is `aeval a (g i)`.
- `comp_mul_of_affine f hf x y`: let `f : V.X ⟶ Z.X` satisfy
  `(x * y) ≫ f = (x ≫ f) * (y ≫ f)` for all affine points `x`, `y` of `V` over every `A`.
  Then the same holds for all points `x`, `y : T ⟶ V.X` on every scheme `T` over `Spec k`.
  Since `V` is affine, every point on `T` factors through the unit `T ⟶ Spec Γ(T)` of the
  adjunction, as an affine point over `Γ(T)` (Library `Lie.unit_affinizationFactor`).

## The cocycle of a section

Let `j : K ⟶ W` and `q : W ⟶ V` be homomorphisms of group schemes over `Spec k`. Suppose the
Library scheme kernel of `q` and `j` have the same range,
`hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j`. Let `s : V.X ⟶ W.X` be
a morphism with `hs : s ≫ q = 𝟙`.

- `pointsCommGroup hcomm T`: the commutative group structure on `T ⟶ W.X` with the existing
  multiplication, given `hcomm`: all points of `W` commute.
- `kerLift hjq x hx` and `kerLift_comp`: a point `x` of `W` with `x ≫ q = 1` factors
  through `j`. `kerLift` chooses such a factorization (by the Library
  `SplitUnipotentAffineTorsor.exists_comp_eq_of_comp_eq_one`).
- `cocycleMap_aux s hs`: the point
  `(fst ≫ s) (snd ≫ s) ((fst * snd) ≫ s)⁻¹` of `W` on `V.X ⊗ V.X` maps to `1` under `q`.
- `cocycleMap hjq s hs : V.X ⊗ V.X ⟶ K.X`: its factorization through `j`.
- `cocycleMap_comp`: for points `x`, `y` of `V` on any `T`,
  `(lift x y ≫ cocycleMap) ≫ j = (x ≫ s) (y ≫ s) ((x * y) ≫ s)⁻¹`.

Now assume that `j` is a monomorphism, that `hcomm` holds, and that `K` has coordinates `eK`
of dimension `n`. Let `eV` be coordinates of dimension `1` on `V`. Let `c : Fin n → k[X][X]`
satisfy `hc`: for all `A`, `a, b ∈ A` and `l`, the `l`-th coordinate of
`lift (linePoint a) (linePoint b) ≫ cocycleMap` under `vectorAffineCoordinates eK A` is
`aevalAeval a b (c l)`. The lemmas below quantify over all commutative `k`-algebras
`R : Type u` and give the three hypotheses of `exists_coboundary`. Write `c_l(a, b)` for
`aevalAeval a b (c l)`.

- `cocycle_symm hjq hcomm hc hV l R a b`: if all points of `V` commute (`hV`), then
  `c_l(a, b) = c_l(b, a)`.
- `cocycle_add hjq hcomm hc l R a b d`:
  `c_l(a, b) + c_l(a + b, d) = c_l(b, d) + c_l(a, b + d)`.
  It is `cocycle_identity` in the commutative group of points of `W`, after cancelling
  `j`.
- `cocycle_tors hjq hcomm hc hq l R a`: if every point of `W` satisfies
  `x ^ ringChar k = 1` (`hq : HasUniformPowerExponent W (ringChar k)`), then
  `∑_{i < ringChar k} c_l(i a, a) = 0`. By induction on `m`, there is a point `κ` of `K` over
  `R` such that `j(κ) · s(t^m) = s(t)^m · s(1)` and the `l`-th coordinate of `κ` is
  `∑_{i < m} c_l(i a, a)`; here `t = linePoint a`. The induction step uses
  `torsion_identity`. For `m = ringChar k`, `t^m = 1` and `s(t)^m = 1`, so `j(κ) = 1` and
  `κ = 1`.
- `exists_coboundaries hjq hcomm hc hV hq`: under the hypotheses of the three previous
  lemmas, there is `G : Fin n → k[X]` with
  `c_l(a, b) = G_l(a + b) - G_l(a) - G_l(b)` for all `R`, `a`, `b` and `l`. This is
  `exists_coboundary` applied to each `c l`.

## Correcting the section

Assume also that `V` is affine over `Spec k`. Let `eV` and `eK` be coordinates as above.

- `correctedSection j s eV eK G := s * (polyMap eV eK G ≫ j)`, for `G : Fin n → k[X]`.
- `correctedSection_comp hjq hs G`: `correctedSection ≫ q = 𝟙`, because points of `K` map
  to `1` under `j ≫ q` (Library `SplitUnipotentAffineTorsor.comp_comp_eq_one`).
- `correctedSection_affine hjq hcomm hs heV heK hc hG A x y`: let `eV` and `eK` be natural,
  let `hc` hold for `c`, and let `G` satisfy the coboundary equation of
  `exists_coboundaries` (`hG`). Then the corrected section is multiplicative on affine
  points of `V` over `A`. On coordinates, the polynomial map `P = polyMap eV eK G` satisfies
  `P(ab) = c(a, b) · P(a) · P(b)` (written multiplicatively in `K`); the claim then follows
  from `section_identity`.

## A split commutative extension of vector groups

Assume that `j` is a monomorphism, that `hjq` holds, and that all points of `W` commute.

- `kerMap hjq s hs : W.X ⟶ K.X`: the factorization through `j` of the point
  `w ↦ w · s(q(w))⁻¹`.
- `isVectorGroupOfDimension_of_section hjq hcomm s hs hmul hK hV`: suppose `s` is a section
  of `q` that is multiplicative on all points (`hmul`). Suppose `K` is a vector group of
  dimension `n` and `V` a vector group of dimension `m`. Then `W` is a vector group of
  dimension `n + m`. The coordinates of a point `w` are the coordinates of `kerMap w`
  followed by those of `q(w)` (`Fin.append`). The inverse sends `(u, v)` to `j(u) · s(v)`.
  The forward map is a homomorphism because `q` is and `kerMap` is (by `kernel_identity`
  and `hmul`); it is natural because `eK` and `eV` are.

## The induction

- `isVectorGroupOfDimension_succ j q hjq hcomm hq s hs hK hV`: let `j` be a monomorphism,
  let `hjq` hold, and let all points of `W` commute. Assume every point of `W` satisfies
  `x ^ ringChar k = 1`. Let `s` be a section of `q` (a morphism of schemes with
  `s ≫ q = 𝟙`). If `K` is a vector group of dimension `n` and `V` of dimension `1`, then `W`
  is a vector group of dimension `n + 1`. Affineness of `V` comes from the Library
  `IsVectorGroupOfDimension.isAffineHom_overRing`. The cocycle polynomials come from
  `exists_bivariate` applied to `cocycleMap`. `exists_coboundaries` gives `G`. The section
  `correctedSection j s eV eK G` is multiplicative by `correctedSection_affine` and
  `comp_mul_of_affine`. Then `isVectorGroupOfDimension_of_section` applies.
- `isVectorGroupOfDimension_of_hasSplitSeries_of_exponent W hcomm hq hW`: let `W` be affine
  over `Spec k`, with commuting points, every point killed by `ringChar k`, and with a
  Library `HasSplitSeries n W`. Then `W` is a vector group of dimension `n`. The proof is by
  induction on `n`, generalizing `W`. For `n = 0`, use the Library
  `HasSplitSeries.isVectorGroupOfDimension_zero`. For `n + 1`, the series gives a closed
  subgroup `j : K ⟶ W`, an fppf quotient `q : W ⟶ V` by its range with `V` of dimension
  `1`, and `HasSplitSeries n K`. Then `j` is a monomorphism and `K` is affine over `Spec k`.
  The points of `K` commute, and are killed by `ringChar k` (Library
  `HasUniformPowerExponent.of_mono`). The induction hypothesis makes `K` a vector group of
  dimension `n`. A section of `q` exists by
  `Langlands.GroupScheme.SplitSeriesDecomposition.exists_section_isIso_mul`. Then
  `isVectorGroupOfDimension_succ` applies.
- `isVectorGroup_of_isSplitUnipotent_of_exponent W hW hq`: let `W` be affine over `Spec k`,
  with `W.X` a commutative monoid object (`[IsCommMonObj W.X]`), split unipotent
  (`IsSplitUnipotent W`), and with every point killed by `ringChar k`. Then
  `IsVectorGroup W`. The points of `W` commute by Mathlib's `Hom.commMonoid`.
