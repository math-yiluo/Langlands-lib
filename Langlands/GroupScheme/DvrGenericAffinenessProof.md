# Proof of Raynaud's affineness criterion over a discrete valuation ring

`Langlands.GroupScheme.dvrGenericAffineness.{u}` proves the Library proposition
`Langlands.GroupScheme.DvrGenericAffinenessStatement.{u}`, imported from
`Langlands.GroupScheme.DvrGenericAffinenessStatement`, in every universe `u` and with no
additional hypotheses. Its type is exactly that closed proposition; the statement module is
unchanged.

```lean
theorem dvrGenericAffineness : DvrGenericAffinenessStatement.{u}
```

## Statement proved

Let \(R\) be a discrete valuation ring with a specified fraction field \(K\), and let \(G\) be a
group scheme over \(\operatorname{Spec}R\) whose structural morphism is flat, locally of finite
type and quasi-compact, and whose actual generic fibre \(G_K\), the group-scheme base change
along \(\operatorname{Spec}K\to\operatorname{Spec}R\), has affine structural morphism. Then the
structural morphism of \(G\) is affine if and only if it is separated. No smoothness,
connectedness, henselianity, completeness or residue-field condition is imposed, and all rings
and schemes live in the same arbitrary universe `u`.

## Proof

The proof is a single application of the conditional reduction
`DvrGenericAffinenessReduction.dvrGenericAffineness_of_smooth_and_cover`
(module `Langlands.GroupScheme.DvrGenericAffinenessReduction`), whose type is

```text
SmoothDvrGenericAffinenessStatement.{u} →
  DvrFiniteSmoothCoverStatement.{u} → DvrGenericAffinenessStatement.{u},
```

to the Library's proofs of its two premises in the same universe:

1. `Langlands.GroupScheme.smoothDvrGenericAffineness.{u}`
   (module `Langlands.GroupScheme.SmoothDvrGenericAffinenessProof`) proves
   `SmoothDvrGenericAffinenessStatement.{u}`: a smooth, quasi-compact, separated group scheme
   over a discrete valuation ring whose generic fibre over a specified fraction field is affine
   is itself affine. The reduction applies it over \(R'\) with the fraction field
   `FractionRing R'`, the one used in the cover of item 2.
2. `Langlands.GroupScheme.dvrFiniteSmoothCover.{u}`
   (module `Langlands.GroupScheme.DvrFiniteSmoothCoverProof`) proves
   `DvrFiniteSmoothCoverStatement.{u}`: after a flat surjective extension
   \(\operatorname{Spec}R'\to\operatorname{Spec}R\) of discrete valuation rings, a flat separated
   finite-type group scheme over \(R\) with affine generic fibre receives a finite surjective
   group homomorphism from a smooth, quasi-compact, separated group scheme over \(R'\) with affine
   generic fibre.

Inside the reduction, the direction "affine implies separated" is Mathlib's instance that affine
morphisms are separated. For the converse, the cover of item 2 is affine by item 1; the base
change of \(G\) to \(R'\) is then affine as the target of a finite surjective morphism from an
affine scheme (`AffineQuotient.isAffine_of_finite_surjective`), and affineness descends along the
flat surjective morphism \(\operatorname{Spec}R'\to\operatorname{Spec}R\)
(`FaithfullyFlatAffineDescent.isAffine_of_isPullback`). The page of
`DvrGenericAffinenessReduction` describes these steps in detail.

The theorem depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations used

- `DvrGenericAffinenessStatement` (`Langlands.GroupScheme.DvrGenericAffinenessStatement`);
- `DvrGenericAffinenessReduction.dvrGenericAffineness_of_smooth_and_cover`
  (`Langlands.GroupScheme.DvrGenericAffinenessReduction`);
- `smoothDvrGenericAffineness` (`Langlands.GroupScheme.SmoothDvrGenericAffinenessProof`);
- `dvrFiniteSmoothCover` (`Langlands.GroupScheme.DvrFiniteSmoothCoverProof`).

## Sources

The statement is Raynaud's criterion as given in Gopal Prasad and Jiu-Kang Yu, *On quasi-reductive
group schemes*, Proposition 3.1, author-preprint PDF/printed p.5, registered source
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`. The route follows the
proof there: pass by a faithfully flat DVR extension and normalization to a smooth group with a
finite surjective map to the base change, prove the smooth case by affinization, and descend
affineness. The pages of the imported modules give the sources of the individual steps.
