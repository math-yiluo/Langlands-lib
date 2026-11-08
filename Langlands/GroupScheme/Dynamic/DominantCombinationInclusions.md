# Dynamic inclusions for a dominant combination of commuting cocharacters

Author: Worker 1068.

## Main result

`Langlands.GroupScheme.Dynamic.exists_dominant_inclusions` takes the
following data:

- a field `k` in an arbitrary universe `u`;
- a group scheme `G` over `Spec k` whose structure morphism is affine
  (`IsAffineHom G.X.hom`) and locally of finite type;
- two cocharacters `χ, tau : 𝔾_m ⟶ G` such that `tau` centralizes `χ`. This
  is stated as `SubgroupFunctor.range tau ≤ Dynamic.centralizer χ`.

The theorem gives a natural number `N` depending only on `χ` and `tau` with
this property. For every integer `n ≥ N`, let `ψ : 𝔾_m ⟶ G` be any
cocharacter whose points satisfy `ψ(t) = χ(tⁿ) · tau(t)`. In Lean this reads:
for every test `T` over `Spec k` and every `t : T ⟶ 𝔾_m`,
`t ≫ ψ.hom.hom = ((t ^ n) ≫ χ.hom.hom) * (t ≫ tau.hom.hom)`. Then

- `Dynamic.parabolic ψ ≤ Dynamic.parabolic χ`,
- `Dynamic.unipotent χ ≤ Dynamic.unipotent ψ`,
- `Dynamic.centralizer ψ ≤ Dynamic.centralizer χ`.

All three are inclusions of subgroup functors, so they hold on every test
scheme over `Spec k`, including nonaffine and nonreduced ones. The theorem
does not construct `ψ`; it applies to any `ψ` with the stated point formula.
It assumes no reductivity, smoothness or connectedness.

The model-level version `Corepresented.exists_dominant_inclusions` proves the
same conclusion, with `N` explicit, for any commutative base ring `R`. It
applies to the group scheme `Corepresented.groupScheme F e` corepresented by
an `R`-algebra `B` of finite type, assuming that `χ(s)` and `tau(t)` commute
for all points `s, t`.

## Provenance

This is an internal helper for the proof of
`Langlands.GroupScheme.DynamicLeviCocharacterRealizationStatement`. It is the
"dominant combination" step of the dynamic method: if `tau` commutes with `χ`
and `n ≫ 0`, then `χⁿ tau` has a parabolic inside that of `χ`, a centralizer
inside that of `χ`, and a unipotent radical containing that of `χ`. The
statement and proof are written for this project's subgroup functors and do
not transcribe any particular literature statement.

## Auxiliary definitions

- `AffineLine.laurentEval A u : A[X, X⁻¹] ⟶ A` is evaluation at a unit `u`.
  The published `Gm.laurentC A : A ⟶ A[X, X⁻¹]` is the inclusion of constants.
- `AffineLine.unitPoint f u` is the point of `𝔾_m` over `Spec A` (with
  structure map `f`) given by a unit `u` of `A`.
- `AffineLine.laurentAt f u` is the point `X = u` of the Library's
  `laurentScheme f`, the spectrum of `A[X, X⁻¹]`.
- `AffineLine.innerUnit D` is the variable `X` of `D[X, X⁻¹]`, viewed as a
  constant unit of `D[X, X⁻¹][Y, Y⁻¹]`.
- `Corepresented.ringPoint e φ` is the point of `Spec B` over `Spec A` given
  by a ring map `φ : B ⟶ A`. By `pointRing_ringPoint` its classifying ring
  map is `φ`.

## Proof as implemented

Throughout, `c_χ : B ⟶ B[X, X⁻¹]` is the Library coaction
`Corepresented.coaction χ`. A function `z` has `χ`-weight `a` when
`c_χ z = single a z`, that is, `z X^a`.

1. **Conjugation formula** (`pointRing_conj`). Let `x` be a point over
   `Spec A` and `u` a unit of `A`. The classifying ring map of
   `χ(u) x χ(u)⁻¹` is `c_χ`, followed by `pointRing x` on coefficients,
   followed by evaluation at `X = u`. The proof combines
   `Dynamic.lift_comp_orbit` (the orbit map at `v` is conjugation by `χ(v)`),
   `laurentAt_comp_laurentPoint`, and the Library lemma
   `laurentPoint_comp_orbit_left`.

2. **Coaction of `ψ`** (`coaction_eq_of_points`). Apply (1) to the point
   `ringPoint e (Gm.laurentC B)` over `Spec B[X, X⁻¹]` and the unit `X`.
   Together with the point formula for `ψ`, this shows that `c_ψ` is `c_χ`,
   then `c_tau` on coefficients, then evaluation at `Xⁿ`. Consequently, by
   `coaction_eq_single_of_points`, a function of `χ`-weight `a` and
   `tau`-weight `j` has `ψ`-weight `j + n a`.

3. **Commuting gradings** (`coeff_coaction_comm`). Work over the two-variable
   ring `B[X, X⁻¹][Y, Y⁻¹]` with the units `Y` and `innerUnit B = X`. Apply (1)
   four times to `χ(Y) tau(X) x tau(X)⁻¹ χ(Y)⁻¹`, written in both orders,
   using the commutation hypothesis. This gives an identity of ring maps
   `B ⟶ B[X, X⁻¹][Y, Y⁻¹]`. Comparing coefficients with
   `coeff_coeff_laurentEval_laurentCoeffMap` shows that the `tau`-weight-`j`
   part of the `χ`-weight-`a` part of `b` equals the `χ`-weight-`a` part of
   its `tau`-weight-`j` part. No bound on `n` is used here.

4. **Generators of bounded `tau`-weight** (`exists_bound`). Fix a finite set
   `s` of `R`-algebra generators of `B`. Let `M` be the largest `|j|` over
   `y ∈ s`, `a` in the `χ`-support of `y`, and `j` in the `tau`-support of
   the `χ`-weight-`a` part of `y`. Each generator is the sum of these pieces
   (Library `sum_coeff_coaction`, applied twice). By
   `coaction_coeff_coaction` and (3), each piece is homogeneous for both `χ`
   and `tau`, with `tau`-weight at most `M` in absolute value. Induction over
   `Algebra.adjoin` then gives the following principle. Let `Q` be a predicate
   on `B` that holds on `algebraMap R B`, is closed under `+` and `·`, and
   holds on every element of `χ`-weight `a` and `tau`-weight `j` with
   `|j| ≤ M`. Then `Q` holds on all of `B`. Take `N = M + 1`. Let `n > M` and
   `|j| ≤ M`. If `a ≠ 0`, then `j + n a` is nonzero and has the sign of `a`:
   `weight_lt_zero` covers `a < 0`, `weight_pos` covers `a > 0`, and
   `weight_ne_zero` covers `a ≠ 0`. If `a = 0`, then `j + n a = j`, which may
   have any sign; the tests in (6) treat this case separately.

5. **Counit facts.** `mem_centralizer_iff'` restates the Library's
   `mem_centralizer_iff` for a point with classifying map `g` as
   `laurentCoeffMap g (c_χ b) = C (g b)` for all `b`. `counit_algebraMap`
   says the counit is the identity on `R` (Library
   `algebraMap_comp_pointRing` at the identity point). `counit_eq_zero` says
   a function of nonzero weight vanishes at the identity: the identity point
   lies in the centralizer, so `mem_centralizer_iff'` applies.

6. **Affine tests.** By `Dynamic.parabolic_le_of_affine_tests`,
   `Dynamic.unipotent_le_of_affine_tests` and
   `Dynamic.centralizer_le_of_affine_tests` from
   `Dynamic.AffineInclusionCriterion`, it suffices to check points over
   `Spec A` for arbitrary commutative rings `A`. Such a point is a ring map
   `g : B ⟶ A`, read through the Library criteria `mem_parabolic_iff` and
   `mem_unipotent_iff` and through `mem_centralizer_iff'`. Each test applies
   (4) to a suitable predicate. In each, `z` is a function of `χ`-weight `a`
   and `tau`-weight `j` with `|j| ≤ M`; its `ψ`-weight is `j + n a`.
   - `parabolic_test` assumes that `g` kills all negative `ψ`-coefficients.
     The predicate is: `laurentCoeffMap g (c_χ b)` is the image of a
     polynomial in `A[X]`. If `a < 0`, the `ψ`-weight of `z` is negative, so
     `g z = 0`. If `a ≥ 0`, the image is `g(z) X^a`. Hence the negative
     `χ`-coefficients of every `b` are killed by `g`.
   - `centralizer_test` assumes that `g` lies in `Z(ψ)`. The predicate is
     `laurentCoeffMap g (c_χ b) = C (g b)`. If `a = 0`, both sides equal
     `C (g z)`. If `a ≠ 0`, the `ψ`-weight of `z` is nonzero, so `g z = 0`.
   - `unipotent_test` assumes that `g` lies in `U(χ)`. The predicate is: some
     polynomial `p` maps to `laurentCoeffMap g (c_ψ b)` and satisfies
     `p(0) = g(counit b)`. Write `w = j + n a`. If `w ≠ 0`, then
     `counit z = 0` by (5). If `w < 0`, then `g z = 0`: for `a < 0` this is
     the first `U(χ)` condition; otherwise `a = 0`, and it is the second
     condition. If `w = 0`, then `a = 0`, and the second condition gives
     `g z = g(counit z)`. In each case `exists_toLaurent_eq_single` produces
     `p`. Hence `g` lies in `U(ψ)`.

7. **Model theorem** (`Corepresented.exists_dominant_inclusions`). This
   combines (4) and (6) with `N = M + 1`. Here `IsAffine` of the model is a
   local instance.

8. **Transport** (`Dynamic.exists_dominant_inclusions`). The Library
   isomorphism `E = AffineCoordinates.groupSchemeIso G` identifies `G` with
   the group scheme corepresented by its coordinate algebra. The published
   lemma `finiteType_coordinateAlgebra` (in
   `Rational.SplitComponentProof`) shows that this algebra is of finite type
   over `k`. The commutation hypothesis comes from
   `range tau ≤ centralizer χ` through `Dynamic.mem_centralizer`,
   `lift_comp_orbit` and `mul_inv_eq_iff_eq_mul`. It and the point formula
   for `ψ` transport to `χ ≫ E.inv`, `tau ≫ E.inv` and `ψ ≫ E.inv`. The
   three inclusions return to `G` by `parabolic_eq_comap_of_iso`,
   `unipotent_eq_comap_of_iso`, `centralizer_eq_comap_of_iso` (applied to
   `E.symm`) and `SubgroupFunctor.comap_mono`.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
