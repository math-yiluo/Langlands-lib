# Proof of the finite smooth cover after a DVR extension

`Langlands.GroupScheme.dvrFiniteSmoothCover.{u}` proves the Library proposition
`Langlands.GroupScheme.DvrFiniteSmoothCoverStatement.{u}`, imported from
`Langlands.GroupScheme.DvrFiniteSmoothCoverStatement`, in every universe `u` and with no
additional hypotheses. Its type is exactly that closed proposition; the statement module is
unchanged.

```lean
theorem dvrFiniteSmoothCover : DvrFiniteSmoothCoverStatement.{u}
```

## Statement proved

Let \(R\) be a discrete valuation ring with a specified fraction field \(K\), and let \(G\) be a
group scheme over \(\operatorname{Spec}R\) that is flat, locally of finite type, quasi-compact and
separated, whose generic fibre \(G_K\) is affine. Then there are a discrete valuation ring \(R'\)
in the same universe, a flat surjective morphism
\(b\colon\operatorname{Spec}R'\to\operatorname{Spec}R\), a group scheme \(H\) over
\(\operatorname{Spec}R'\) that is smooth, quasi-compact and separated with affine generic fibre
over `FractionRing R'`, and a group-scheme homomorphism \(\pi\colon H\to b^{*}G\) whose underlying
scheme morphism is finite and surjective. The group \(G\) need not be smooth, reduced or
connected, and the residue field of \(R\) is arbitrary.

## Proof

The proof composes two finite surjective group maps, each obtained after its own flat surjective
extension of discrete valuation rings, using constructions already in the Library.

1. **Smooth generic fibre.** `DvrSmoothGenericReduction.reduction R K G` applied to
   `Langlands.AlgebraicGeometry.dvrPotentialGenericReduction` (the proof of
   `DvrPotentialGenericReductionStatement`) gives a value `P` of
   `DvrSmoothGenericReduction.Reduction G`. It consists of a discrete valuation ring `P.ring`, a
   flat surjective morphism `P.base : Spec P.ring ⟶ Spec R`, a group scheme `P.group` over
   `P.ring`, and a group homomorphism `P.map : P.group ⟶ P.base*G` whose underlying morphism is
   finite and surjective. The group `P.group` is flat, locally of finite type, quasi-compact and
   separated, and its generic fibre over `FractionRing P.ring` is smooth and affine. In that
   construction `P.group` is the schematic closure in `P.base*G` of the reduced generic subgroup,
   which is geometrically reduced after the extension supplied by
   `dvrPotentialGenericReduction`; see the pages of `DvrSmoothGenericReduction` and
   `DvrGenericReduction`.
2. **Smooth total group.** These properties of `P.group` are exactly the instance hypotheses of
   `DvrCoverAssembly.smoothGenericCover`. Applied to
   `Langlands.AlgebraicGeometry.dvrStableNormalization` (the proof of
   `DvrStableNormalizationStatement`), it gives a value `D` of `DvrCoverAssembly.Cover P.group`: a
   further flat surjective DVR extension and a smooth, quasi-compact, separated group scheme with
   affine generic fibre, together with a finite surjective group homomorphism to the base change
   of `P.group`. That group is the stable normal model constructed in `DvrStableGroup`.
3. **Composition.** `DvrCoverAssembly.Cover.comp P.base P.map P.finite P.map_surjective D` is a
   value `C` of `DvrCoverAssembly.Cover G`. Its base morphism is `D.base ≫ P.base`, which is flat
   and surjective as a composite of flat surjective morphisms. Its covering group is `D.group`.
   Its group map is `D.map`, followed by the base change of `P.map` and the canonical isomorphism
   between iterated base change and base change along the composite. That map is finite and
   surjective, since these properties are stable under base change and composition.
4. The fields of `C` (`ring`, its instances, `base`, `flat`, `surjective`, `group`, `map`,
   `smooth`, `quasiCompact`, `separated`, `affineGeneric`, `finite`, `map_surjective`) are
   exactly the witnesses and conjuncts of the statement. The generic fibre in `Cover` is taken
   along `Spec.algebraMap ring (FractionRing ring)`, which is by definition (an `abbrev` in
   Mathlib) the morphism `Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R')))` of the
   statement.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations used

- `DvrFiniteSmoothCoverStatement` (`Langlands.GroupScheme.DvrFiniteSmoothCoverStatement`);
- `DvrSmoothGenericReduction.reduction` and `DvrSmoothGenericReduction.Reduction`
  (`Langlands.GroupScheme.DvrSmoothGenericReduction`);
- `dvrPotentialGenericReduction` (`Langlands.AlgebraicGeometry.DvrPotentialGenericReductionProof`);
- `DvrCoverAssembly.smoothGenericCover`, `DvrCoverAssembly.Cover` and
  `DvrCoverAssembly.Cover.comp` (`Langlands.GroupScheme.DvrCoverAssembly`);
- `dvrStableNormalization` (`Langlands.AlgebraicGeometry.DvrStableNormalizationProof`).

## Sources

The route is that of Brian Conrad's appendix to Gopal Prasad and Jiu-Kang Yu, *On quasi-reductive
group schemes*, Theorem A.2 and Corollary A.4 (author preprint, pp.28–29), as recorded on the
page of the statement: after a DVR extension the reduced generic group becomes smooth, and its
normalization is a finite smooth group. The implemented argument closes the reduced generic
subgroup instead of reducing the whole group, and then applies stable normalization to that
closure. Registered source `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`. The pages of the imported
modules give the sources of the individual steps.
