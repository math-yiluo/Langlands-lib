# Central subgroups and finiteness of rational points

Authors: Worker 1428 (Lean proof and Markdown) and Worker 1499 (Markdown
revision and submission).

This internal helper module of the proof of
`Langlands.GroupScheme.CentralQuotientReductiveStatement` proves the
finiteness results used by `CentralQuotientCore`. It is derived content: the
statements are chosen for this proof and are not items of the cited
literature. Everything is in the namespace
`Langlands.GroupScheme.CentralQuotient`.

Notation: `K` is a field, algebraically closed unless stated otherwise, and
all group schemes are over `Spec K`. `rationalPoints G` is the group of
`K`-points of `G`, and `rationalPoints.map f` is the induced group
homomorphism. `center G` is the Library centre subgroup functor
(`Rational/Characters`), and `IsCentral m` means that every point of the
source of `m` maps into `center G`. "Trivial unipotent radical" is the
Library predicate `HasTrivialUnipotentRadical`.

## Trivial groups and finite index

- `id_eq_one_of_finite_rationalPoints`: a smooth, connected affine group `Z`
  with finitely many rational points is trivial, meaning `𝟙 Z.X = 1`. The
  space of `Z` is Jacobson because `Z` is locally of finite type over a field.
  Every closed point is the image of a rational point (Mathlib's
  `pointOfClosedPoint`), so there are finitely many closed points. Mathlib's
  `JacobsonSpace.discreteTopology` then makes the space discrete; being
  connected, it is a subsingleton. `Z` is reduced because it is smooth over a
  field, so two rational points with the same underlying point are equal
  (`rationalPoint_ext`). Rational points separate morphisms out of the
  reduced `Z` (`hom_ext_rationalPoints`). Hence `𝟙` and `1` agree.
- `finite_range_of_finite_map` (pure group theory): let `φ : G →* H` be a
  group homomorphism and `Γ` a subgroup of finite index. If `φ(Γ)` is finite,
  then the range of `φ` is finite. The image of `Γ` in the range has finite
  index there (`Subgroup.index_map_dvd`), and it is finite.

## Rational points of the reduced identity component

- `finiteIndex_map_rationalIdentitySubgroup` (**Lemma F**): let `S` be affine
  and locally of finite type, and let `S_red` be its reduced subgroup (Library
  `reducedSubgroup`, smooth over the algebraically closed field). The image in
  `S(K)` of the rational points of the identity component of `S_red` has
  finite index in `S(K)`. In `S_red(K)` these points have finite index by
  `IdentityComponent.finite_rationalComponentQuotient`. The inclusion
  `S_red(K) → S(K)` is surjective, because rational points of the reduced
  scheme `Spec K` lift (`ReducedSubgroup.liftOver`). Surjective maps preserve
  finite index.
- `isCentral_of_rationalPoints` (**Lemma C**): let `M` and `G` be smooth,
  `G` affine, and `m : M ⟶ G` a homomorphism. If every rational point of `M`
  maps into `center G`, then `m` is central. The commutator morphism
  `commutatorMap m (𝟙 G)` (`ImageGenerationCommutator`) is a morphism out of
  the smooth, hence reduced, product `M × G`. It is trivial on rational
  points, so it is trivial (`hom_ext_rationalPoints`). Evaluating it on any
  pair of points (`commutatorMap_lift`) gives centrality on every test
  scheme.

## Lemma D: homomorphisms from central subgroups to unipotent groups

Throughout, `G` is smooth and affine with trivial unipotent radical, `m : M ⟶ G`
is a monomorphism with `IsCentral m`, `Z` is affine with `IsUnipotent Z`, and
`π : M ⟶ Z` is a homomorphism.

- `map_eq_one_of_isCentral_charZero` (characteristic zero, `K` any field of
  characteristic zero): if `M` is smooth, affine and connected, then
  `π` is trivial on rational points. `M` is commutative because `m` is a
  central monomorphism (`IsCentral.commGroupScheme`). The published
  `characteristicZeroPointFactors` (`Rational/CharacteristicZeroPointFactors`)
  writes every rational point `x` of `M` as `i(t) · φ(1)`, with `i : T ⟶ M` a
  torus and `φ : 𝔾_a ⟶ M`. The composite `φ ≫ m` is a central homomorphism
  from the smooth connected unipotent `𝔾_a` (`VectorGroup.isUnipotent`), so
  it is trivial by the published `CenterQuotient.hom_eq_one_of_isCentral`.
  Since `m` is a monomorphism, `φ` is trivial. The composite `i ≫ π` from a
  torus to a unipotent group is zero (`IsTorus.hom_eq_zero_of_isUnipotent`,
  `Unipotent/TorusHom`). Hence `π(x) = 1`.

- `hom_eq_one_of_pow_eq_one`: let `M` be affine and `j : E ⟶ M` a
  monomorphism from a smooth, affine, connected group, and let `n ≠ 0` with
  `j(y)^n = 1` for all points `y` of `E`. Then `j` is trivial. `E` is
  commutative because `j ≫ m` is central. Every homomorphism `φ : 𝔾_m ⟶ E` is
  zero: multiplication by `n` on `𝔾_m` is surjective
  (`IsTorus.flat_and_surjective_multiplication`, `Torus/Multiplication`), so
  every rational point of `𝔾_m` is an `n`-th power of a rational point
  (`HomogeneousClosedImmersion.exists_rational_lift`). Hence `φ ≫ j` is
  trivial on the rational points of the reduced `𝔾_m`, so it is trivial, and
  `φ` is trivial because `j` is a monomorphism. By the published
  `AbsoluteNoCocharacter.isUnipotent_of_gm_hom_eq_zero`
  (`Absolute/CharacterCocharacter`; `E` is solvable because it is
  commutative), `E` is unipotent. Then `j ≫ m` is a central homomorphism from
  a smooth connected unipotent group, so it is trivial
  (`hom_eq_one_of_isCentral`), and so is `j`.
- `finite_rationalPoints_of_pow_eq_one`: the same with `E` only affine and
  locally of finite type and `e : E ⟶ M` a monomorphism killed by `n`. Then
  `E` has finitely many rational points. Apply the previous lemma to the
  identity component of `E_red`, mapped into `M`. Its rational points then
  have trivial image in `E(K)`, and that image has finite index by Lemma F.
  So `E(K)` is finite.
- `finite_torsion_of_isCentral` (**torsion lemma**): if `M` is commutative,
  affine and locally of finite type, then for `n ≠ 0` the set of rational
  points `x` of `M` with `x^n = 1` is finite. These are the rational points of
  the kernel of multiplication by `n` (`multiplication M n`, with
  `PowerImage.points_multiplication_nat`). That kernel satisfies the
  hypotheses of the previous lemma.

- `finite_range_of_isCentral_charP` (characteristic `p > 0`): if `M` is
  smooth, affine and connected, then `π(M(K))` is finite. `M` is commutative,
  hence nilpotent (`isNilpotentGroupScheme_of_isCommMonObj`). The published
  `IsNilpotentGroupScheme.centralTorusQuotient` (`Nilpotent/CentralQuotient`)
  gives a maximal torus `D_T` of `M` with inclusion `D_T ⟶ M` and an fppf
  quotient `M ⟶ D_Q` with kernel `D_T`. The quotient `D_Q` is smooth,
  connected and contains no torus, so it is unipotent
  (`IsNilpotentGroupScheme.isUnipotent_of_no_torus`). The published
  `exists_hasUniformPowerExponent_of_isUnipotent`
  (`Rational/UnipotentPointsExponent`) gives `r` with `y^(p^r) = 1` for all
  points `y` of `D_Q`. Put `n = p^r`. For a rational point `x` of `M`, `x^n`
  lies in `D_T`. Multiplication by `n` on the torus `D_T` is surjective, so
  `x^n = s^n` for a rational point `s` of `D_T`. Then `x s⁻¹` is `n`-torsion
  and `π(x s⁻¹) = π(x)`, since `D_T ⟶ M ⟶ Z` goes from a torus to a
  unipotent group and is zero. So `π(M(K))` is the image of the finite set of
  `n`-torsion points.

- `finite_range_of_isCentral` (**Lemma D**): if `M` is smooth, affine and
  connected, then `π(M(K))` is finite. Split on the characteristic
  (`CharP.exists'`). In characteristic zero the image is `{1}`; in
  characteristic `p` use the previous lemma.

## Provenance

These lemmas replace steps 2–3 of the suggested argument in the statement's
Markdown, which uses the structure of connected nilpotent groups (Milne,
*Algebraic Groups*, 2017, source `milne-2017-algebraic-groups`, Corollary
16.48, printed p.341). The implemented route avoids that splitting. It uses
only Library results: the point factorization of smooth connected
commutative groups in characteristic zero, the central torus quotient of
nilpotent groups, uniform `p`-power exponents of unipotent groups in
characteristic `p`, and the triviality of central unipotent homomorphisms
into groups with trivial unipotent radical (Library
`CenterQuotient.hom_eq_one_of_isCentral`). The finiteness statements are
internal to this proof.
