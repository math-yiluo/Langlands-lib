# Weight tangent vectors and maximality of weight subgroups

Let `σ : TorusAction F I` be a split-torus action on a corepresented group functor
`F` with representing algebra `B` (`e : (F ⋙ forget GrpCat).CorepresentableBy B`,
`Rational.TorusGrading`), and let `U_P = weightSubgroup e σ P` be the weight subgroups
of `Rational.TorusWeightSubgroups`. This module has three parts. It characterizes
tangent vectors of weight `χ` by the support of their infinitesimal coordinates. It
shows that `U_P` has no tangent vectors of weights outside `P`. And it proves a
maximality criterion: a torus-stable closed subgroup with noetherian, connected
coordinate ring and no tangent vectors of weights outside `P` (with `0 ∉ P`) lies in
`U_P`. All declarations are in namespace `Langlands.GroupScheme.Corepresented`;
`counit` is `AffineLinearEmbedding.counit`.

## Statements

Tangent vectors. For an `R`-algebra `A`, `dualReduction A : A[ε] ⟶ A` is the reduction
`TrivSqZeroExt.fstHom`.

- `coord_eq_of_reduction`: if `X` over `A[ε]` reduces to the identity, then
  `coord e X f = counit e f + (coord e X f).snd ε`.
- `eq_one_of_snd_eq_zero`: such an `X` whose infinitesimal coordinates
  `(coord e X f).snd` all vanish is the identity.
- `algHom_ext_comp`: algebra maps out of `B` agree when they agree on all weight
  components `comp e σ m f`.

Weight tangent vectors. `IsWeightTangent σ χ X`, for `X` over `R[ε]`, says that for
every `R`-algebra `A` and every `t : I → Aˣ`, acting by `t` (viewed in `A[ε]` through
`inl`) on the coefficient extension of `X` to `A[ε]` equals scaling `ε` by the value
`χ(t)` (`splitTorus.exponentValue`). The extension and the scaling are
`GeneralLinear.DualNumber.coefficientAlgMap (Algebra.ofId R A)` and
`GeneralLinear.DualNumber.epsilonScaleAlg`, the maps used by the Library's
`lieKernelMap` and `lieKernelScale`.

- `epsilonScaleAlg_fst`, `epsilonScaleAlg_snd`, `coefficientAlgMap_fst`,
  `coefficientAlgMap_snd` and `units_map_inlAlgHom` compute these maps.
- `coord_act_coefficient` and `coord_scale_coefficient` compute the coordinates of both
  sides of the defining equation at a homogeneous function of weight `m`: they are
  `X_A(h) · m(t)` and `ε ↦ χ(t) ε` applied to `X_A(h)`.
- `isWeightTangent_of_snd_comp`: if `X` reduces to the identity and
  `(coord e X (comp e σ m f)).snd = 0` for all `f` and `m ≠ χ`, then `X` is a tangent
  vector of weight `χ`.
- `snd_comp_eq_zero_of_isWeightTangent`: conversely, the infinitesimal coordinates of a
  tangent vector of weight `χ` vanish on weight components of weight `m ≠ χ`.
- `eq_one_of_mem_weightSubgroup_of_snd_comp`: if `X ∈ U_P(A[ε])` reduces to the
  identity and its infinitesimal coordinates are supported on a single weight `χ ∉ P`,
  then `X = 1`.

Maximality, over a field `k` (with `R = CommRingCat.of k`):

- `le_weightSubgroup`: let `H` be a family of subgroups cut out by an ideal `J`
  (`IsCutOutBy e H J`) and stable under the torus. Assume:
  - `B ⧸ J` is noetherian;
  - `B ⧸ J` has no idempotents other than `0` and `1`;
  - `0 ∉ P`;
  - every tangent vector `X` of `H` (a point of `cutFunctor hJ` over `k[ε]` reducing to
    the identity) whose infinitesimal coordinates, for the restricted action, are
    supported on a single weight `χ ∉ P` is trivial.

  Then every point of `H` lies in `U_P`.

## Proofs

`isWeightTangent_of_snd_comp`: by `algHom_ext_comp` it suffices to compare
coordinates at a weight component `h = comp e σ m f`. The first parts agree because
`counit e h = 0` for `m ≠ 0` (`counit_comp`) and `m(t) = 1` for `m = 0`. The
`ε`-parts are `D(h) m(t)` and `χ(t) D(h)`. They agree for `m = χ`, and for `m ≠ χ`
because `D(h) = 0`.

`snd_comp_eq_zero_of_isWeightTangent`: apply the definition over the group algebra
`R[I → ℤ]` at the universal units, whose character values are the monomials `X^m`
(`exponentValue_universalUnits`). The `ε`-parts at `h = comp e σ m f` give
`D(h) X^m = X^χ D(h)` in `R[I → ℤ]`. The coefficient of `X^m` gives `D(h) = 0` when
`m ≠ χ`.

`eq_one_of_mem_weightSubgroup_of_snd_comp`: for `m ∉ P` the coordinate of
`comp e σ m f` is a scalar, so it has zero `ε`-part. For `m ∈ P`, `m ≠ χ`, and the
`ε`-part vanishes by assumption. Summing over the components (`sum_support_comp`), all
infinitesimal coordinates vanish.

`le_weightSubgroup` applies the published
`Langlands.Algebra.GradedAugmented.eq_zero_of_notMem` to `C = B ⧸ J`. Its inputs are:
- the grading `weightGradedAlgebra` of the restricted action (indexed by `I → ℤ`);
- the augmentation `counit` of the corepresentation `cutCorepresentableBy hJ`, which
  kills homogeneous elements of nonzero weight (`IsHomogeneous.counit_eq_zero`);
- the subsemigroup `P`.

Its rigidity hypothesis `IsRigidInDegree` holds as follows. An algebra map
`φ : C → k[ε]` lifting the counit, with `ε`-part vanishing in degrees `≠ χ`, is the
coordinate map of a tangent vector `X` of `H` supported on `χ`. By assumption `X = 1`,
so `φ` is `inl ∘ counit` and its `ε`-part vanishes. The conclusion of `eq_zero_of_notMem`
applies to the image `c` of `comp e σ m f - counit e (comp e σ m f)` for `m ∉ P`:
- `c` is homogeneous of weight `m` (`comp_restrict`; for `m = 0` the scalar is
  homogeneous of weight `0`);
- `c` has counit `0` (`counit_cut_mk`).

So `c = 0`. Hence every point `x ∈ H(A)` satisfies
`coord e x (comp e σ m f) = counit e (comp e σ m f)` for `m ∉ P`, i.e. `x ∈ U_P(A)`.

## Provenance

Internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task 023326af).
There, the filtration `weightFiltration b a r` is generated by the smooth connected
closed `b`-stable subgroups whose Lie algebra weights (`actionWeightSupport`, built from
the eigenvectors `actionEigenvectors` on dual-number kernels) lie in the cyclic tail.
`IsWeightTangent` is the corresponding eigenvector condition for a corepresented
functor. `le_weightSubgroup` gives the maximality of the subgroups `U_P` among such
generators; this is used to identify the filtration with the explicit subgroups. In
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., §3.3 (Proposition 3.3.6 and the
construction before Lemma 3.3.8), the corresponding facts come from the dynamic method.
The route here, via the published graded vanishing theorem, is internal to this
formalization.
