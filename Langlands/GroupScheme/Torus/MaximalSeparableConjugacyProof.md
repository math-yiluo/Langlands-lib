# Maximal tori are conjugate over a finite separable extension: proof

Worker 172.

`Langlands.GroupScheme.maximalTorusSeparableConjugacy` proves the published
`Langlands.GroupScheme.MaximalTorusSeparableConjugacyStatement.{u}`
([`Torus.MaximalSeparableConjugacyStatement`](MaximalSeparableConjugacyStatement.md)) in every
universe `u`. The theorem has no hypotheses: its type is exactly the statement. That statement
and every module it imports are unchanged.

For a field `k : Type u`, a group scheme `G` over `Spec k` with `Smooth G.X.hom` and
`IsAffineHom G.X.hom` (not assumed connected), and maximal tori `j : T.toGrp ⟶ G` and
`j' : T'.toGrp ⟶ G`, the theorem gives:

1. a field `K : Type u` with `Algebra k K`, `FiniteDimensional k K` and
   `Algebra.IsSeparable k K`, and a `K`-point `g` of `G_K` with
   `range (j_K ≫ int(g)) = range (j'_K)`;
2. if `IsSepClosed k`, a `k`-point `g` of `G` with `range (j ≫ int(g)) = range j'`.

This is Milne, *Algebraic Groups* (2017), Theorem 17.87 and the sentence after its proof
(p.380). The Lean proof follows a different route from Milne's, described below. It composes
published Library results with one new helper lemma.

## Imports

- `Langlands.GroupScheme.Torus.MaximalSeparableConjugacyStatement`: the target.
- `Langlands.GroupScheme.Torus.EtaleLocalMaximalConjugacyProof`: the étale-local conjugacy of
  maximal tori over an arbitrary base and its base-change lemmas for `SubgroupConjugate`.
- `Langlands.GroupScheme.Torus.RelativeFieldComparison`: a torus over a field is a relative
  torus.
- `Langlands.GroupScheme.Reductive.SplitIsogenyRigidityReduction`: a maximal torus over a field
  is maximal on every residue-field fibre of `Spec k`.
- `Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisChartPoint`: a nonempty scheme étale over
  `Spec k` has a point over a finite separable extension of `k`.
- `Langlands.AbelianScheme.Tate.BaseChangeCoherence`: the comparison `baseChangeIdIso` between
  base change along the identity and the original group.

## Conjugacy with a source isomorphism

`SubgroupConjugate i i'` ([`Rational.SubgroupConjugacy`](../Rational/SubgroupConjugacy.md)), for
`i : H ⟶ G` and `i' : H' ⟶ G`, says that there are a base point `g` of `G` and an isomorphism
`e : H ≅ H'` with `i ≫ int(g) = e.hom ≫ i'`. It implies the equality of subgroup functors in the
target: `SubgroupFunctor.range_iso_comp e i'` gives `range (e.hom ≫ i') = range i'`. The proof
works with `SubgroupConjugate` because the Library proves that it is preserved by base change.

## Helper: `SubgroupConjugate.of_baseChange_id`

For a scheme `S` and `i : H ⟶ G`, `i' : H' ⟶ G` over `S`: if the base changes of `i` and `i'`
along `𝟙 S` are `SubgroupConjugate`, then so are `i` and `i'`.

Proof. The natural isomorphism `Functor.mapGrpNatIso Over.pullbackId ≪≫ Functor.mapGrpIdIso`
has components `baseChangeIdIso`. Its naturality squares for `i` and `i'` say that
`(baseChange (𝟙 S)).map i ≫ (baseChangeIdIso G).hom = (baseChangeIdIso H).hom ≫ i`, and the
same for `i'`. Composing the hypothesis with `(baseChangeIdIso G).hom`
(`SubgroupConjugate.postcomp`) and rewriting by these squares gives
`SubgroupConjugate ((baseChangeIdIso H).hom ≫ i) ((baseChangeIdIso H').hom ≫ i')`.
`SubgroupConjugate.of_precomp_isos` removes the two source isomorphisms.

This lemma is a derived helper for this proof; it is the identity counterpart of the published
`SubgroupConjugate.of_baseChange_comp`.

## Proof of the theorem

1. **Étale-local conjugacy.** `hj.1 : IsTorus T.toGrp` gives `RelativeTorus.IsTorus T.toGrp` by
   `IsTorus.isRelativeTorus`, and `IsMaximalTorus.isFibrewiseMaximalTorus` gives
   `IsFibrewiseMaximalTorus j`; the same holds for `j'`. The published
   `EtaleLocallySubgroupConjugate.of_relativeTori` (the strengthened form of
   `etaleLocalMaximalTorusConjugacy`, Conrad, *Reductive group schemes*, Theorem 3.2.6) then
   gives an étale cover `𝒰` of `Spec k` such that, for every member `f_a : U_a ⟶ Spec k`, the
   base changes of `j` and `j'` along `f_a` are `SubgroupConjugate`. This step uses the
   smoothness and affineness of `G`; it does not need `G` connected.
2. **A member over the point.** `Scheme.Cover.exists_eq` gives a member `a` and a point `y` of
   `U_a` (over the closed point of `Spec k`). So `E := Over.mk f_a` is a nonempty scheme étale
   over `Spec k` (`Scheme.Cover.map_prop`).
3. **A finite separable point.** `GaloisChartPoint.exists_separable_point E` gives a field
   `K : Type u` with `Algebra k K`, `FiniteDimensional k K`, `Algebra.IsSeparable k K`, and a
   morphism `w : specOver k K ⟶ E` over `Spec k`. Its over-condition reads
   `w.left ≫ f_a = Spec.map (ofHom (algebraMap k K)) =: b`.
4. **Conjugacy over `K`.** `SubgroupConjugate.baseChange` along `w.left` and
   `SubgroupConjugate.of_baseChange_comp` give conjugacy of the base changes of `j` and `j'`
   along `w.left ≫ f_a`, which is `b` after rewriting by step 3. Writing this conjugacy as
   `⟨g, e, he⟩`, the point `g` and `SubgroupFunctor.range_iso_comp e` give part 1 for this `K`.
5. **Separably closed case.** If `IsSepClosed k`, then `algebraMap k K` is bijective
   (`IsSepClosed.algebraMap_bijective`, using that `K/k` is separable). Let
   `σ : K ≃ₐ[k] k` be the inverse of `AlgEquiv.ofBijective (Algebra.ofId k K)` and
   `s := Spec.map (ofHom σ) : Spec k ⟶ Spec K`. Since `σ` fixes `k`, `σ ∘ algebraMap k K` is the
   identity of `k`, so `s ≫ b = 𝟙 (Spec k)` by `Spec.map_comp`, `CommRingCat.ofHom_comp`,
   `CommRingCat.ofHom_id` and `Spec.map_id`. Base change of the conjugacy of step 4 along `s`,
   `of_baseChange_comp` and this equation give conjugacy of the base changes along `𝟙 (Spec k)`.
   The helper `of_baseChange_id` turns it into `SubgroupConjugate j j'`, and
   `SubgroupFunctor.range_iso_comp` gives part 2.

The inspected axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Comparison with Milne's proof

Milne represents the transporter `R ↦ {g ∈ G(R) | g T₁_R g⁻¹ = T₂_R}` by a closed subscheme `X`
of `G`, shows that `X` is smooth and nonempty by Theorem 17.10 over `k^a`, and takes a point of
`X` over a finite separable extension (A.48). The Lean proof does not construct the transporter
scheme. It uses instead the published étale-local conjugacy theorem, whose proof combines
Theorem 17.10 (`maximalTorusConjugacy`, applied in the identity component) with smooth
transporter lifting. A point of one member of the resulting étale cover over a finite separable
extension then plays the role of Milne's point of `X(k')`. The separably closed case is the
special case `k' = k`, as in Milne.

## Scope

The theorem is the full target: every universe, every field, every smooth affine `G` (not
assumed connected or reductive) and every pair of maximal tori, with no additional hypotheses.
It records only the conjugating point, not the transporter scheme or its torsor structure.
