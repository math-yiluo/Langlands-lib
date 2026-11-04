# The geometric core of the centre-quotient theorem

Author: Worker 1499.

This internal helper module of the proof of
`Langlands.GroupScheme.CenterQuotientReductiveStatement` proves the
unipotent-radical part of the theorem over an algebraically closed field. It is
derived content: the statements are chosen for this proof and are not items of
the cited literature. Everything is in the namespace
`Langlands.GroupScheme.CenterQuotient`.

Notation: for points `x, y` of a group scheme on a test scheme `T`, products,
inverses and `1` are the Library pointwise group structure. `range f` is the
Library subgroup functor `SubgroupFunctor.range f` of a homomorphism `f`, and
`⊥` is the trivial subgroup functor. `center G` is the Library centre subgroup
functor (`Rational/Characters`).

## Trivial ranges

Over any base scheme `S`:

- `id_eq_one_of_range_id_eq_bot`: if `range (𝟙 U) = ⊥`, then the identity
  morphism of `U.X` equals the constant morphism `1`. The identity of `U.X`
  is a point of `range (𝟙 U)` on the test object `U.X`.
- `range_eq_bot_of_id_eq_one`: if `𝟙 U.X = 1`, then `range j = ⊥` for every
  homomorphism `j : U ⟶ Q`. Every point `y` of `U` equals `y ≫ 𝟙 U.X = 1`, so
  `y ≫ j = 1`.

## Main result

- `hasTrivialUnipotentRadical_of_isFppfQuotient_center`: let `K` be an
  algebraically closed field and `q : G ⟶ Q` a homomorphism of group schemes
  over `Spec K`. Assume:
  - `G.X.hom` is smooth and affine, `G.X.left` is connected, and
    `HasTrivialUnipotentRadical G` holds;
  - `Q.X.hom` is affine and locally of finite type;
  - `RelativeRoot.IsFppfQuotient (center G) q` holds.

  Then `HasTrivialUnipotentRadical Q` holds. The hypotheses are exactly those
  of `CenterQuotientGeometricCoreStatement` (module
  `CenterQuotientReduction`).

  Proof. Let `j : U ⟶ Q` be a closed subgroup with `U` smooth, connected and
  unipotent and with normal range. We must show `range j = ⊥`; suppose not.
  1. A central subgroup. Conjugation by `Q` preserves `range j`, so it
     restricts to an action `b` of `Q` on `U`
     (`AutomorphicAction.onRepresentedSubgroup`). By
     `range_eq_bot_of_id_eq_one` and `id_eq_one_of_range_id_eq_bot`,
     `range (𝟙 U) ≠ ⊥`. The Library theorem
     `hasNontrivialSmoothStableCentralSubgroup_of_isUnipotent`
     (`Rational/UnipotentSmoothCenter`) gives a closed subgroup `z : Z ⟶ U`
     with `Z` smooth and affine, `z` central in `U`, `range z` stable under
     `b`, and `range z ≠ ⊥`.
  2. Normality. The composite `z ≫ j` is a closed subgroup of `Q`, and its
     range is normal in `Q`: if `v ≫ z` is a point of `range z`, then
     stability gives a point `w` of `Z` with `w ≫ z = b g (v ≫ z)`, so
     `g (v ≫ z ≫ j) g⁻¹ = w ≫ z ≫ j`.
  3. The preimage. Let `a : A ⟶ G` be the inclusion of the preimage of
     `z ≫ j` under `q` (`SubgroupPreimage.inclusion`, the fibre product of
     `q` and `z ≫ j`), with projection `π : A ⟶ Z`. By the Library lemmas
     `SubgroupPreimage.isClosedSubgroup` and `SubgroupPreimage.isNormal`, `a`
     is a closed subgroup with normal range. For every rational point `x` of
     `A`, `q (x ≫ a) = j (z (π x))`, and `z (π x)` lies in `center U`.
     Hence `commute_of_lift` (`CenterQuotientCommutator`) shows that the
     images in `G` of any two rational points of `A` commute.
  4. Central rational points. By `mem_center_of_isNormal_of_commute`
     (`CenterQuotientEnvelope`), `x ≫ a` lies in `center G` for every rational
     point `x` of `A`.
  5. Rational points of `Z` are trivial. Let `w` be a rational point of `Z`.
     Since `q` is surjective, the rational point `w ≫ z ≫ j` of `Q` has a
     rational lift `g` to `G` (the Library lemma
     `HomogeneousClosedImmersion.exists_rational_lift`). The pair `(g, w)` is a
     rational point of `A`, so `g` lies in `center G` by step 4. The actual
     kernel of `q` has range `center G` (part of `IsFppfQuotient`), so
     `g ≫ q = 1` (`mem_range_kernelι_iff`). Hence `w ≫ z ≫ j = 1`, and
     `w = 1` because `z ≫ j` is a monomorphism.
  6. Conclusion. `Z.X` is reduced (smooth over a field) and locally of finite
     type, so by the Library lemma `hom_ext_rationalPoints` the identity of
     `Z.X` equals `1`, as both agree on rational points. Then
     `range_eq_bot_of_id_eq_one` gives `range z = ⊥`, contradicting step 1.

The classical statement is that the quotient of a reductive group by its
centre is an adjoint group (J. S. Milne, *Algebraic Groups*, 2017, Corollary
17.62(e) and the paragraph after Remark 17.63, printed p. 373, PDF p. 389). The
Lean proof does not follow that route: it uses neither the multiplicative-type
structure of the centre nor Jordan decompositions in `G`, only the rational-point
argument above.
