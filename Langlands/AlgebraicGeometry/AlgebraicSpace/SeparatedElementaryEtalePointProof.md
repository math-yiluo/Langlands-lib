# Elementary étale points of separated algebraic spaces: proof

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedElementaryEtalePointStatement.{u}`.
The entry theorem is `Langlands.AlgebraicGeometry.AlgebraicSpace.separatedElementaryEtalePoint`.

The target: let `K : Type u` be a field, `X` an algebraic space over `Spec K` with
`IsSeparated X`, `A` a finite type `K`-algebra, `x : RingPoints K X A` with
`IsEtale (uliftYonedaEquiv.symm x)` and `p` a prime of `A`. Then there are a finite type
`K`-algebra `B : Type u`, an étale point `y : RingPoints K X B` and a prime `q` of `B` such that
(1) for every `K`-algebra `D` and maps `f : B →ₐ[K] D`, `g : A →ₐ[K] D` whose spectra form a
pullback square of presheaves over `y` and `x`, some prime of `D` contracts to `q` along `f` and
to `p` along `g`; and (2) for every `K`-algebra `C` and maps `f g : B →ₐ[K] C` whose spectra form
a pullback square over `y` and `y`, and every `μ : C →ₐ[K] B` with `μ ∘ f = μ ∘ g = id`, a prime
of `C` contracting to `q` along both `f` and `g` equals `μ⁻¹(q)`.

## Route

The proof works with the given chart `x` and follows the construction in the proof of Stacks
Project Lemma 68.8.3 (Tag 0BBN), which is how the Stacks proof of Lemma 68.11.4 (Tag 0BBP)
proceeds, using the Library's tuple modules (`EtaleEquivalenceRelationTuple*`) and the charts of
`UniformFieldPointChartsProof`.

Let `a : h_U → X` be `x`, with `U = Spec A` over `Spec K` (`ringTest K A`), and let
`E = rel hpb ht hs` be the étale equivalence relation `R = U ×_X U ⇉ U` of a represented kernel
pair `(t, s)` of `a`. Since `X` is separated, `R` is affine. As in the Library tuple modules,
index `n` means `n + 1` coordinates, so the Lean `V_n` below is the Stacks quotient
`V_{n+1} = W_{n+1}/S_{n+1}`. The point `p ∈ U` lies in exactly one difference
`T_n \ T_{n+1}` of consecutive tuple threshold opens (`exists_unique_tupleDegreeLocus`), where
`T_n = E.tupleThresholdOpen n` is the set of points related to the first coordinate of a distinct
related `(n + 1)`-tuple. So `p` is related, by a point `r` of `R` with `s r = y₀` and
`t r = p`, to the first coordinate `y₀` of a distinct related tuple `w'`, and `p ∉ T_{n+1}`.

The chart is the affine quotient `V_n = quot n` of the distinct related `(n + 1)`-tuples by the
symmetric group, with the étale map `tM : V_n → X` induced by the first coordinate
(`UniformFieldPointCharts.exists_chart`). With `B = AffineCoordinateRing K V_n` and
`e = affineSchemeOverIso K V_n : V_n ≅ Spec B`, the point is
`y = uliftYonedaEquiv (h(e⁻¹) ≫ tM)` and `q = e(q')` for `q' = tupleSymmetricMap n w'`.

Both conditions are checked on points with values in algebraically closed fields. Condition (2)
rests on the uniqueness of such points of `V_n` outside the symmetric threshold open
`tupleSymmetricThresholdOpen n (n + 1)` with a given image in `X`; `q'` lies outside it because
`p ∉ T_{n+1}` and `T_{n+1}` is invariant under the relation.

## Declarations

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedElementaryEtalePoint`. The file
sets `backward.isDefEq.respectTransparency false`, as `UniformFieldPointChartsProof` does: the
fields of `EtaleEquivalenceRelation.ofKernelPair` are `U.left`, `R.left`, `t.left`, `s.left`
only after unfolding that definition.

- `exists_algClosed_point`: every point `z` of a scheme `Z` is the image of the unique point of
  `Spec Ω` under some `Spec Ω → Z`, with `Ω` algebraically closed (the algebraic closure of the
  residue field, composed with `Z.fromSpecResidueField z`).
- `exists_lift_of_isPullback`: two points `T → V₁`, `T → V₂` with equal images in a presheaf
  `F` lift to a point of a represented pullback `P` of `V₁ → F ← V₂` (full faithfulness of the
  Yoneda embedding `schemeYoneda`).
- `hom_ext_of_isPullback`: points of a represented pullback are determined by their two
  projections.

In the section `Tuples`, `h` is a pullback square exhibiting `(t, s) : R ⇉ U` as the kernel pair
of `a : h_U → X.presheaf`, with `t.left`, `s.left` étale and `R.left`, `U.left` affine, and
`tM : h_{V_n} → X.presheaf` satisfies `h(quotMap n) ≫ tM = h(projOver n 0) ≫ a`.

- `eq_of_comp_chart_eq`: two points `α β : Spec Ω → V_n` over `Spec K`, `Ω` algebraically
  closed, with `α` outside `tupleSymmetricThresholdOpen n (n + 1)` and the same image in `X`,
  are equal. Proof: lift `α`, `β` to points `a₀`, `b₀` of the distinct tuples along the
  surjective quotient map (`LangWeil.SpaceFamily.exists_lift_of_surjective`); their first
  coordinates have the same image in `X` (`hcomp`), so a point `r` of `R` relates them
  (`EtaleEquivalenceRelation.exists_lift_of_isPullback`), and `tupleCrossLift` gives a point of
  the cross scheme `tupleCrossScheme n n` with ends `a₀`, `b₀`. The first coordinate of `a₀` is
  outside `tupleThresholdOpen (n + 1)` (`tupleSymmetricMap_mem_threshold_iff`), and
  `tupleCross_fieldPoint_symmetric_eq_of_not_threshold` gives equal images of `a₀`, `b₀` in
  `V_n`.
- `exists_point_of_isPullback`: for `e : V_n ≅ W`, a represented pullback `D` of
  `h(e⁻¹) ≫ tM` and `a`, a distinct tuple `w'` and a point `r` of `R` with `s r` the first
  coordinate of `w'`, some point of `D` maps to `e(tupleSymmetricMap n w')` in `W` and to `t r`
  in `U`. Proof: take `ρ₀ : Spec Ω → R` through `r` (`exists_algClosed_point`). The first
  coordinate is étale, hence locally of finite type and locally quasi-finite
  (`locallyQuasiFinite_of_etale`), so `ρ₀ ≫ s` lifts to `ω : Spec Ω → (distinct tuples)` with
  `ω` through `w'` (`LangWeil.SpaceFamily.exists_lift_at_point`). The points `ω ≫ quotMap n ≫ e`
  and `ρ₀ ≫ t` have the same image in `X` (by `hcomp` and `h.w`), so they lift to `ξ` in `D`
  (`exists_lift_of_isPullback`); the image of the point of `Spec Ω` under `ξ` is the required
  point.
- `eq_comap_of_isPullback`: for `e : V_n ≅ Spec B`, a prime `q` of `B` with `e⁻¹(q)` outside
  `tupleSymmetricThresholdOpen n (n + 1)`, a represented pullback `Spec C` of `h(e⁻¹) ≫ tM` with
  itself with projections `Spec f`, `Spec g`, and `μ : C →ₐ[K] B` with `μ ∘ f = μ ∘ g = id`, a
  prime `P` of `C` with `f⁻¹(P) = q` equals `μ⁻¹(q)`. Proof: take `ξ : Spec Ω → Spec C` through
  `P`. The points `ξ ≫ Spec f` and `ξ ≫ Spec g` of `Spec B` have the same image in `X`
  (`hpb.w`), and the first goes through `q`, so after `e⁻¹` they are equal by
  `eq_of_comp_chart_eq`. With `δ = Spec μ`, `δ ≫ Spec f = δ ≫ Spec g = id` (`ringTestMap_comp`,
  `ringTestMap_id`), so `ξ` and `(ξ ≫ Spec f) ≫ δ` have the same two projections and are equal
  (`hom_ext_of_isPullback`). Evaluating at the point of `Spec Ω` gives `P = μ⁻¹(q)`. The
  hypothesis that `P` contracts to `q` along `g` is not needed.

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `separatedElementaryEtalePoint : SeparatedElementaryEtalePointStatement.{u}`.

## Proof of `separatedElementaryEtalePoint`

1. `exists_kernelPair` gives the kernel pair `(t, s)` of `a = uliftYonedaEquiv.symm x` with
   étale projections; `R` is affine by `isAffine_of_isPullback_of_closedDiagonal`, since
   `IsSeparated X` says the diagonal of `X` is a closed immersion.
2. `exists_unique_tupleDegreeLocus` gives `n` with `p ∈ T_n` and `p ∉ T_{n+1}`;
   `mem_pointSaturationOpen` gives the tuple `w'` and the point `r` of `R` with `s r` the first
   coordinate of `w'` and `t r = p`. `exists_chart` gives the étale `tM`.
3. Finite type of `B`: the quotient map `quotMap n` is finite, étale and surjective, and its
   composite with the structure map of `V_n` is the first coordinate (étale) followed by
   `Spec A → Spec K` (locally of finite type since `A` is of finite type). Hence
   `V_n → Spec K` is locally of finite type
   (`locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`), and
   `affineCoordinate_finiteType_iff` gives `Algebra.FiniteType K B`.
4. `y` is étale by `IsEtale.iso_comp`. The image `q'` of `w'` in `V_n` is outside
   `tupleSymmetricThresholdOpen n (n + 1)`: otherwise the first coordinate of `w'` lies in
   `T_{n+1}` (`tupleSymmetricMap_mem_threshold_iff`), and then so does `p`, which is related to
   it by `r` (`tupleThresholdOpen_invariant`).
5. Condition (1) is `exists_point_of_isPullback` with `W = Spec B` and the pullback square of the
   spectra of `f`, `g`; the images of a point under `Spec f`, `Spec g` are its contractions.
   Condition (2) is `eq_comap_of_isPullback`, applied with `e⁻¹(e(q')) = q'`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Stacks Project, Decent Algebraic Spaces, Lemma 68.11.4 (Tag 0BBP) and its proof through
  Lemma 68.8.3 (Tag 0BBN): registered sources `stacks-decent-spaces-chapter-ed88ff78-2026-11-05`
  and `stacks-stratification-2026-11-02`. The chart `V_p = W_p/S_p` and its étale map to `X` are
  those of the proof of Lemma 68.8.3; the verification of the two conditions on points with
  values in algebraically closed fields is this proof's own.
