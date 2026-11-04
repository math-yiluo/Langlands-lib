# Homomorphic sections of character-linear kernel towers, given the one-step splitting theorem

This module reduces the existence of a homomorphic section along a finite
character-linear kernel tower to the one-step splitting theorem
`LinearAdditiveExtensionSplittingStatement` (Milne 2022, Theorem 15.34(d), with a
diagonalizable quotient). That theorem appears only as an explicit hypothesis
`hsplit` of the theorems below. The module does not prove it, does not assert it,
and does not assert that any tower exists.

The module reuses the published interfaces `LinearKernelTower.HasTower`,
`LinearKernelTower.AdmitsTower` and `LinearKernelTower.IsCharacterLinearKernel`
(`Langlands.GroupScheme.LinearKernelTower`), the actual pullback
`SubgroupPreimage.groupScheme` with its inclusion and projection
(`Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction`), the kernel
lift `SubgroupPreimage.kernelInclusion` with its fppf-quotient lemma
(`Langlands.GroupScheme.SplitSolvableExtension`), and the kernel comparison
`RelativeRoot.IsFppfQuotient.kernelIso` (`Langlands.GroupScheme.Rational.FppfQuotientSmooth`).

## Declarations

- `AutomorphicAction.transportActed b e`. For an automorphic action `b` of `H`
  on `G` and an isomorphism of group schemes `e : G ≅ G'`, this is the action of
  `H` on `G'` with action morphism `(H.X ◁ e.inv) ≫ b.hom ≫ e.hom`.
  `transportActed_act` states that on test points
  `(b.transportActed e).act h x = b.act h (x ≫ e.inv) ≫ e.hom`.
  The published `AutomorphicAction.transport`
  (`Langlands.GroupScheme.Rational.TorusActionBridge`) also changes the acting
  group along a homomorphism. This module does not import that module, which
  has many further dependencies. It uses this acted-on-only variant under a
  distinct name, so the two modules can be imported together. No comparison
  between the two definitions is stated here.
- `LinearKernelTower.isClosedSubgroup_of_section`. Over a field `k`, let
  `r : Q ⟶ D` and `t : D ⟶ Q` be homomorphisms of group schemes with
  `t ≫ r = 𝟙 D`, where `Q` is affine over `k`. Then `t` is a closed subgroup,
  meaning that its underlying scheme morphism is a closed immersion. The proof
  uses Mathlib's lemma that `f` is a closed immersion if `f ≫ g` is one and `g`
  is separated. Here `g` is the underlying morphism of `r`, which is separated
  because its source is affine.
- `LinearKernelTower.exists_section_of_step` (one tower step). Let `k` be
  algebraically closed, `Λ` a finitely generated abelian group (torsion allowed),
  and `D := Diagonalizable.groupScheme (CommRingCat.of k) Λ`. Let `E` be affine
  and locally of finite type over `k`, and let `Q` be affine. Let `p : E ⟶ Q` be
  an fppf quotient whose all-test kernel is the range of `kernelι p`. Let
  `r : Q ⟶ D` be such that `IsCharacterLinearKernel D (p ≫ r) p` holds, and let
  `t : D ⟶ Q` satisfy `t ≫ r = 𝟙 D`. Then, given `hsplit`, there is a
  homomorphism `s : D ⟶ E` with `s ≫ p ≫ r = 𝟙 D`.
- `LinearKernelTower.exists_section_of_hasTower hsplit n q`. Over the same `k`,
  `Λ` and `D`, every homomorphism `q : E ⟶ D` with `HasTower D n q` has a
  homomorphism `s : D ⟶ E` with `s ≫ q = 𝟙 D`.
- `LinearKernelTower.exists_section_of_admitsTower hsplit h`. The same conclusion
  holds from `AdmitsTower D q`, that is, from a tower of some finite length.

The last theorem is the meaning of the statement
`LinearKernelTower.SectionExistenceStatement`, as specified by task
`e2b7437f-c78c-43e7-a63a-9853584f835f`, except that it has the hypothesis
`hsplit`. Once `LinearAdditiveExtensionSplittingStatement` is proved, that
statement follows by applying this theorem to the proof.

## Proof

**One step.** Let `incl : E' ⟶ E` and `π : E' ⟶ D` be the inclusion and
projection of the actual pullback `E' := SubgroupPreimage.groupScheme p t`. The
inverse image of the section `t` is
`E' = E ×_Q D`, and `incl ≫ p = π ≫ t`. Hence
`incl ≫ p ≫ r = π ≫ t ≫ r = π`.

- `t` is a closed subgroup by `isClosedSubgroup_of_section`. So `incl` is a closed
  subgroup (`SubgroupPreimage.isClosedSubgroup`), `E'` is affine
  (`SubgroupPreimage.isAffineHom`), and `E'` is locally of finite type over `k`,
  because its structure morphism factors as the closed immersion `incl` followed
  by the structure morphism of `E`.
- `kernelι p ≫ p = 0` (`SplitSolvable.kernel_comp_eq_zero`). So the kernel lifts
  to a monomorphism `z : kernel p ⟶ E'` with `z ≫ incl = kernelι p`
  (`SubgroupPreimage.kernelInclusion`). The projection `π` is an fppf quotient
  whose all-test kernel is the range of `z`
  (`SubgroupPreimage.isFppfQuotient_projection`). `IsFppfQuotient.kernelIso`
  then gives an isomorphism `e : kernel p ≅ kernel π` with
  `e.hom ≫ kernelι π = z`. Consequently
  `kernelι π ≫ incl = e.inv ≫ kernelι p`.
- Let `(a, χ, b)` be the character-linear data for `p`. Transport them to
  `kernel π`: put `a' := e.inv ≫ a`, which is still a closed subgroup because
  `e.inv` is an isomorphism, keep `χ`, and put `b' := b.transportActed e`.
  The conjugation equation for `π` is checked after composing with the
  monomorphism `incl`. For test points `g` of `E'` and `x` of `kernel π`, both
  sides become `(g ≫ incl) * (x ≫ e.inv ≫ kernelι p) * (g ≫ incl)⁻¹`. On the
  left this uses `g ≫ π = (g ≫ incl) ≫ (p ≫ r)` and the conjugation equation for
  `p`. On the right it uses that composition with the homomorphism `incl`
  preserves products and inverses. The character-linearity equation for `b'`
  and `a'` reduces to that for `b` and `a` after cancelling `e.hom ≫ e.inv`.
- `hsplit` applied to `π`, which is flat, surjective and locally of finite
  presentation, with the data `(a', χ, b')` gives a homomorphism
  `s' : D ⟶ E'` with `s' ≫ π = 𝟙 D`. Then `s := s' ≫ incl` satisfies
  `s ≫ p ≫ r = s' ≫ π = 𝟙 D`.

**Induction.** `exists_section_of_hasTower` is proved by recursion on the length
`n`. At length `0`, `q` is an isomorphism and `inv q` is a section. At length
`n + 1`, the tower supplies `p : E ⟶ Q` and `r : Q ⟶ D` with `p ≫ r = q`, the
fppf and character-linearity conditions, and `HasTower D n r`. The latter tower
makes `Q` affine (`HasTower.isAffineHom`). By recursion `r` has a section `t`,
and the one-step theorem gives a section of `p ≫ r = q`.
`exists_section_of_admitsTower` unpacks the length.

## Provenance

This is internal. The route follows Milne, *Algebraic Groups* (2022 corrected
reprint, `milne-2022-algebraic-groups`), proof of Theorem 16.26(a), printed
pp.332–333 (zero-based PDF indices 342–343). There the smaller quotient is split
by induction, the preceding extension is pulled back along that section
(diagram (118)), and Theorem 15.34(d), printed pp.319–320 (indices 329–330),
splits the resulting extension of `D` by a linear closed additive subgroup.
Here that theorem enters only as the hypothesis `hsplit`. The Lean development
consists of the universal property of the actual pullback, the published
all-test kernel comparison, and transport of the conjugation and linearity
equations along the resulting kernel isomorphism. No smoothness, connectedness
or reducedness of `E` or of the kernels is assumed: they may be finite or
nonreduced, and the characters may be trivial.
