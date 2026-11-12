# Generic cocharacters of maximal split tori define minimal rational parabolics: proof

Workers 3874 and 3784. Worker 3784 proposed this route and wrote the published helper
module [`GenericParabolicCocharacterConjugacy`](GenericParabolicCocharacterConjugacy.md).
Worker 3874 wrote this module, following Worker 3784's draft of it. An earlier carried
draft of this task by Workers 1298 and 1307 of the previous project instance also needed
`SmoothMaximalSplitTorusConjugacyStatement`. This route avoids it.

`Langlands.GroupScheme.genericMinimalParabolic` proves exactly the published
proposition `Langlands.GroupScheme.GenericMinimalParabolicStatement.{u}` of
`Langlands.GroupScheme.Rational.MinimalParabolicStatement`, at its universe `u`
and with no added premise. Write `S = Spec (CommRingCat.of k)`. Take any field
`k : Type u`, any group scheme `G` over `S` with `hG : IsConnectedReductive G`,
any commutative group scheme `T` over `S` with a maximal split torus
`i : T.toGrp ⟶ G` (`IsMaximalSplitTorus i`), and any cocharacter
`ν : cocharacterLattice T` that is generic for `i` (`IsGenericCocharacter i ν`:
its lattice pairing with every actual relative root of `i` is nonzero; the
affine instance is taken from `hG`). The theorem proves

`IsMinimalParabolicFunctor (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i))`.

By the published definition this has two parts. First, the dynamic parabolic
functor is the all-test range of an actual closed subgroup `j : P ⟶ G` with
`IsParabolicSubgroup j`: `P` is smooth and some Borel subgroup of the base
change of `G` to `AlgebraicClosure k` factors through the base change of `j`.
Second, every subgroup functor `F'` that is the all-test range of an actual
parabolic subgroup over `k` and satisfies `F' ≤ Dynamic.parabolic (ν ≫ i)` is
equal to it. The order and the equality are those of subgroup functors on
every test scheme over `S`. The field is arbitrary: any characteristic,
perfect or not, finite or infinite. `G` need not be split. The only axioms used
are `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

Both declarations are in namespace `Langlands.GroupScheme`.

- `genericMinimalParabolic_of_parabolicDynamic hPD`: for
  `hPD : ParabolicDynamicStatement.{u}`, a proof of
  `GenericMinimalParabolicStatement.{u}`.
- `genericMinimalParabolic : GenericMinimalParabolicStatement.{u}`: the exact
  target, obtained by applying the first theorem to the published proof
  `parabolicDynamic` (module `Absolute.ParabolicDynamicProof`).

So `ParabolicDynamicStatement` is discharged by a published theorem and is not
a hypothesis of `genericMinimalParabolic`.

## Proof of `genericMinimalParabolic_of_parabolicDynamic`

Fix `k`, `G`, `hG`, `T`, `i`, `hi`, `ν` and a genericity proof `hν`. Write
`P(χ)` for `Dynamic.parabolic χ` and `χν = CommGroupScheme.groupHom ν ≫ i`.

1. *Reduction to dynamic competitors.* The published
   `isMinimalParabolicFunctor_dynamic_iff_of_parabolicDynamic` (module
   `Rational.ParabolicFunctorCocharacter`) uses `hPD` in both directions. Every
   rational parabolic functor is a dynamic parabolic `P(χ)` of a cocharacter
   `χ : 𝔾_m ⟶ G` over `k`, and every dynamic parabolic is a rational parabolic
   functor. This covers the representability and geometric parabolicity of
   `P(χν)`. So `P(χν)` is a minimal parabolic functor as soon as every
   `P(χ) ≤ P(χν)` equals `P(χν)`. Fix such a `χ` and `hle : P(χ) ≤ P(χν)`.
2. *Conjugating `χ` into the torus.* The published `genericCentralizer` (module
   `Rational.GenericCentralizerProof`) gives
   `Dynamic.centralizer χν = torusCentralizer i`, since `ν` is generic. The
   published `Dynamic.range_le_parabolic` (module
   `Rational.ParabolicCocharacterConjugacy`) gives `range χ ≤ P(χ)`, so
   `range χ ≤ P(χν)` by `hle`. The helper `exists_parabolic_conj_into_torus`
   (module `Rational.GenericParabolicCocharacterConjugacy`) then gives a rational
   point `g ∈ P(χν)(k)` and a homomorphism `ρ : 𝔾_m ⟶ T` with
   `χ ≫ inn(g) = ρ ≫ i`. Here `inn(g)` is the inner automorphism `G.innerIso g`.
3. *Transport by `g`.* Since `g` lies in `P(χν)`, the published
   `SubgroupFunctor.comap_innerIso_hom_eq_of_mem` (module
   `Rational.StandardLeviLiftIndependence`) gives `inn(g)^* P(χν) = P(χν)`. The
   published `Dynamic.parabolic_eq_comap_of_iso` (module `Dynamic.Functoriality`),
   rewritten with step 2, gives `P(χ) = inn(g)^* P(ρ ≫ i)`. Pulling back along an
   isomorphism preserves and reflects the order
   (`SubgroupFunctor.comap_iso_le_comap_iso_iff`, module
   `Rational.ParabolicConjugacyTransport`). Hence `hle` gives
   `P(ρ ≫ i) ≤ P(χν)`.
4. *Equality on the torus.* `ρ` is the cocharacter `Additive.ofMul ρ` of `T`. The
   published `generic_dynamicParabolic_eq_of_le` (module
   `Rational.GenericMinimalParabolicReduction`), applied to the published proofs
   `relativeRootSignInclusions` (`Rational.RelativeRootSignInclusionsProof`) and
   `relativeRootNegation` (`Rational.RelativeRootNegationProof`), gives
   `P(ρ ≫ i) = P(χν)`. As that module's Markdown explains, the inclusion makes
   the nonnegative relative-root support of `ρ` contained in that of `ν`.
   Genericity of `ν` and stability of the relative roots under negation then
   force the reverse inclusion.
5. *Conclusion.* Rewriting step 3 with step 4 gives
   `P(χ) = inn(g)^* P(χν) = P(χν)`.

## Provenance

This is an internal composition of published Library theorems. It adds no new assertion
from the literature. The proved proposition is the dynamic formulation, recorded in the
statement's Markdown, of Borel and Tits, *Groupes réductifs* (1965), 4.15(a) and 4.16,
printed pp.90–92 (PDF pp.37–39), source `borel-tits-1965-groupes-reductifs`. The implemented route
differs from the source. It identifies rational parabolics with dynamic
parabolics through `ParabolicDynamicStatement`. It conjugates a smaller dynamic
parabolic's cocharacter into the maximal split torus by a rational point of the
generic parabolic, and it compares relative-root signs.
