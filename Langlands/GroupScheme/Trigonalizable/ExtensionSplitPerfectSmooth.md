# Milne 16.26 from the étale case

Module
`Langlands.GroupScheme.Trigonalizable.ExtensionSplitPerfectSmooth`,
namespaces `Langlands.GroupScheme.TrigonalizableExtensionSplit` and
`Langlands.GroupScheme`.

This module reduces case (b) of Milne's Theorem 16.26 to the single premise
`EtaleDiagonalizableExtensionSplitStatement` (see
[`EtaleExtensionSplitStatement`](EtaleExtensionSplitStatement.md): over a
perfect field, an extension of a finite étale `D(Λ)`, that is, with `Λ`
finite of order prime to the characteristic exponent of `k`, by a smooth
connected unipotent group splits). It then proves the published target
`TrigonalizableExtensionSplitStatement` from that premise. Cases (a) and (c)
use no premise. The premise itself is not proved here.

## Declarations

- `oneStepSplitting_of_charZero`: over a field of characteristic zero,
  `OneStepSplitting k Λ` holds for every `Λ`. The closed polynomial `f` of a
  closed subgroup of `𝔾ₐ` with `f ≠ 0` is monic with `f(0) = 0`, and its
  degree is a power of the characteristic exponent `1`
  (`PerfectCorrection.eq_zero_or_eq_pow_of_coeff_ne_zero`), so `f = X`, which
  is surjective on `k`. `exists_section_of_solvable` applies.
- `exists_section_of_perfect_of_smooth (hP : EtaleDiagonalizableExtensionSplitStatement.{u})`:
  for `G`, `U`, `i`, `Λ`, `q` as in the target with `[PerfectField k]`,
  `Smooth U.X.hom`, `ConnectedSpace U.X.left`, `IsClosedSubgroup i`,
  `IsUnipotent U`, `(SubgroupFunctor.range i).IsNormal` and
  `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, there is
  `s : D(Λ) ⟶ G` with `s ≫ q = 𝟙`. This is case (b) of 16.26.
- `trigonalizableExtensionSplit_of_etale (hP : EtaleDiagonalizableExtensionSplitStatement.{u}) :
  TrigonalizableExtensionSplitStatement.{u}`: Milne 16.26 in all three cases.

## Proof of case (b)

`admitsTower` (from [`ExtensionSplitAlgClosed`](ExtensionSplitAlgClosed.md),
valid over every field) gives a finite character-linear kernel tower for `q`.
Let `p` be the characteristic exponent of `k`.

If `p = 1`, `k` has characteristic zero, and `oneStepSplitting_of_charZero`
with `exists_section_of_admitsTower'` (from [`PerfectOneStep`](PerfectOneStep.md))
splits the tower.

If `p` is prime:

1. `PrimeToPart.exists_exponent` gives `e` with `p ∤ e` killing the
   prime-to-`p` torsion of `Λ`. Put `K = PrimeToPart.saturation p Λ e`,
   `g = QuotientAddGroup.mk' K` and
   `ι₁ = Diagonalizable.restrictMap (CommRingCat.of k) g : D(Λ ⧸ K) ⟶ D(Λ)`.
   It is a closed subgroup (`Diagonalizable.isClosedImmersion_restrictMap`,
   `g` surjective).
2. Let `G₁ = SubgroupPreimage.groupScheme q ι₁` be the inverse image of
   `ι₁`, with inclusion `incl`, projection `π₁ : G₁ ⟶ D(Λ ⧸ K)` and the
   factorization `z : U ⟶ G₁` of `i` (`SubgroupPreimage.kernelInclusion`,
   using `i ≫ q = 0`). `G₁` is affine and locally of finite type, `z` is a
   closed subgroup (`z ≫ incl = i` is a closed immersion), `range z` is normal
   (conjugating in `G₁` is conjugating in `G` and `incl` is a monomorphism),
   and `π₁` is an fppf quotient by `range z`
   (`SubgroupPreimage.isFppfQuotient_projection`). `Λ ⧸ K` is finitely
   generated and killed by `e` (`PrimeToPart.e_smul_eq_zero`), so
   `PrimeToPart.finite_and_coprime_card` shows that it is finite of order
   prime to `p`.
3. The premise `hP`, applied to `k` (perfect), its characteristic exponent
   `p`, `G₁`, `U`, `z`, `Λ ⧸ K` and `π₁`, with the hypotheses of step 2 and the smoothness, connectedness and
   unipotence of `U`, gives a section `σ₁'` of `π₁`. Then `σ₁ = σ₁' ≫ incl` satisfies `σ₁ ≫ q = ι₁` by
   the pullback square.
4. `PrimeToPart.relativeSolvable` and `oneStepSplittingRel_of` (from
   [`RelativeTower`](RelativeTower.md)) give `OneStepSplittingRel k Λ ι₁`, and
   `exists_section_of_admitsTower_rel` splits the tower of `q` by a section
   extending `σ₁`.

## Proof of the target

Split the disjunction of the target. Case (a) is
`exists_section_of_isAlgClosed` (`ExtensionSplitAlgClosed`). Case (b) is
`exists_section_of_perfect_of_smooth` with the premise. Case (c) is
`exists_section_of_perfect_of_connected`
([`ExtensionSplitPerfectConnected`](ExtensionSplitPerfectConnected.md)).

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, printed
pages (PDF page = printed page + 16):

- Theorem 16.26, p.332: "The extension e → G_u → G → D → e splits in each of
  the following cases: (a) the field k is algebraically closed; (b) the field
  k is perfect and G_u is smooth and connected; (c) the field k is perfect
  and D is connected."
- Proof, p.333: "In case (b), we choose N as in Corollary 16.23, and then the
  top extension splits because of 15.34(a)."

The implemented route for case (b) differs from Milne's. Milne chooses the
normal series so that every step is `𝔾ₐ`, through Corollaries 16.22–16.23.
Those corollaries assume `G` smooth (16.22) or `D` a split torus (16.23), and
they are not used here. Instead the tower of 16.21 (built in
`ExtensionSplitAlgClosed`) is kept, whose steps may be non-smooth subgroups of
`𝔾ₐ`. The extension is first split over the étale subgroup `D(Λ ⧸ K)`; this
is the premise, a special case of SGA 3 XVII, Lemme 5.2.3 i) c)
(`sga3-expose-xvii-gille-polo-2008`, SHA256
`687f333c4f86221e7898f44c1706845d8e0b79af50ab31f3ed9a3b0f696ae25b`, printed
pp.346–347). That section is then extended step by step along the tower,
which is possible because the correction equation of each step is solvable
compatibly with it (`RelativeSolvable`, proved for `ι₁` in `PrimeToPart`).
The splitting of the tower relative to a partial section is internal.
