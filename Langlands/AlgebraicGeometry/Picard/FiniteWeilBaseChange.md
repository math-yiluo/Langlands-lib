# Ground base change of the actual finite Weil pairing

This module compares the existing finite Weil pairing `finiteWeilLevelBilinearMap` of an
abelian scheme `A` over `S` with the same construction for its base change
`A' := (baseChange b).obj A` along a morphism `b : S' ⟶ S`. Here `T` is a test scheme over `S'`,
and `T₀ := (Over.map b).obj T` is the same scheme regarded over `S`. Both pairings take values
in `TateTwist.Level Γ(T.left, ⊤) n`, because `T₀.left` is `T.left`.

The module adds no hypotheses beyond the existing inputs. The dual of `A'` is any `hA'`, with
any inverse/evaluation data `MA'`, `evaluationA'`. The dual of `A` is compared with it through
the canonical comparison `dualSchemeBaseChangeIso`. That comparison needs the named
proposition `PicardZeroUniversalBaseChangeStatement` (`universality`). No geometric hypothesis
on either dual is used.

## Main results

- `dualLevelBaseChange b A … universality hA MA evaluationA hA' MA' evaluationA' T n` is an
  additive equivalence from the actual `n`-torsion points over `T` of the dual group scheme of `A'`
  (`dualCommGroupSchemeFromEvaluation` for `A'`) to the actual `n`-torsion points over `T₀` of
  the dual group scheme of `A`. By `toSection_dualLevelBaseChange`, its effect on underlying
  dual points is `dualPointBaseChange`: precompose with the inverse of
  `dualSchemeBaseChangeIso`, then take the slice-adjunction mate `baseChangeParameterMate b`.
- `finiteWeilLevelBilinearMap_baseChange`: for `x` an `n`-torsion point of `A'` over `T` and `y`
  an `n`-torsion point of the dual of `A'` over `T`,

  `finiteWeilLevelBilinearMap … hA' MA' evaluationA' n T x y =
    finiteWeilLevelBilinearMap … hA MA evaluationA n T₀ (levelBaseChange b A.toGrp T n x)
      (dualLevelBaseChange … T n y)`,

  where `GroupScheme.Tate.levelBaseChange` is the existing primal identification.
- `finiteWeilLevelBilinearMap_nondegenerate_baseChange_iff`: the pairing over `T` has trivial
  left and right kernels exactly when the pairing over `T₀` does.
- `dualKernelCharacter_evaluation_familyBaseChange`: the character-level form, for any
  homomorphism `f : A ⟶ B` and any `f' : A' ⟶ B'` whose underlying morphism lies over that of
  `f` (`hom f' ≫ pullback.fst B.X.hom b = pullback.fst A.X.hom b ≫ hom f`). Take a dual point `p'`
  of `B'` over `T` in the kernel of the dual of `f'`, and a point `x'` of `ker f'` over `T`. The
  unit `Gm.pointsEquiv S' T (characterEvaluation (dualKernelCharacter … f' … p' _) x')` equals the
  unit computed over `S` for `f` at `dualPointBaseChange … p'` and at the corresponding point
  `x` of `ker f` over `T₀`. The kernel condition for that old dual point is a hypothesis of
  this lemma; the level-pairing theorem proves it for torsion points.

## Construction and proof

1. *Relative spaces.* `familyBaseChangeSpaceMap b A T : T ×_{S'} A' ⟶ T₀ ×_S A` (an isomorphism
   in the Library) intertwines:
   - shears (`shear_familyBaseChangeSpaceMap`), with translation parameters related by
     `baseChangePointsEquiv`;
   - homomorphism family maps (`homFamilySpaceMap_familyBaseChangeSpaceMap`);
   - kernel translations (`kernelShear_familyBaseChangeSpaceMap`);
   - pullback of base units (`relativeUnitsPullback_familyBaseChangeSpaceMap`).
2. *Trivializations.* From a trivialization `α` of `f^* M` on `T₀ ×_S A`,
   `familyBaseChangeKernelTrivialization` builds one on `T ×_{S'} A'`. It uses
   `squarePullbackIso` around the square of item 1, as `squareKernelTrivialization` does in
   `FiniteWeilFunctorialityProof`.
3. *Kernel action.* `kernelTranslationAut_familyBaseChange` shows that the transported
   kernel-translation automorphism is the pullback of the original one. It uses
   `equalCompositeUnitAut_square`, `equalCompositeUnitAut_congr` and
   `equalCompositeUnitAut_precomp`. Taking scalars and descending through universal global
   functions gives equal units on the common parameter scheme
   (`kernelTranslationScalar_familyBaseChange`, `kernelTranslationUnit_familyBaseChange`).
4. *Intrinsic characters.* `intrinsicKernelCharacter_evaluation_familyBaseChange` combines the
   unit comparison with `characterEvaluation_section` and `intrinsicKernelCharacterHom_points`. The
   two section test objects over `S` differ only in how their structure morphisms are
   bracketed. They are compared by the identity morphism and `kernelTranslationUnit_precomp`.
5. *Dual points.* `dualPointFamilyBaseChangeIso` identifies the Poincaré representative of `p'`
   with the ground base change of the representative of `dualPointBaseChange … p'`. It composes
   the pullback-composition iso `dualPointFamilyPullbackIso`, the characterizing iso
   `dualSchemeBaseChangePullbackIso` and the slice-adjunction iso `baseChangeFamilyPullbackIso`.
   `dualKernelCharacter_eq_of_iso` and `dualKernelCharacter_eq_intrinsic` then reduce item 5 to
   item 4.
6. *Group structure on duals.* `rigidifiedClassesBaseChange` and its lemmas are shared with
   `DualAbelianBaseChangeProof` through [DualBaseChangeClasses](DualBaseChangeClasses.md).
   Their definitions and hypotheses are unchanged. With
   `dualCommGroupSchemePointMulEquiv`, they show that the comparison is multiplicative
   (`dualSchemeBaseChangeIso_hom_mul`). `dualGrpBaseChangeIso` is the resulting isomorphism of
   group objects, built by `Grp.mkIso`. `levelEquivOfIso` turns an isomorphism of commutative
   group objects into an equivalence of torsion levels. Composing with `levelBaseChange` gives
   `dualLevelBaseChange`.
7. *Pairing.* `finiteWeilLevelBilinearMap_coe` expresses the unit of a pairing value as the
   dual torsion character evaluated at the primal kernel lift.
   `dualTorsionCharacter_eq_dualKernelCharacter` and `torsion_dualSchemeMap_eq_origin` rewrite
   the dual torsion character as a dual-kernel character of the underlying dual point.
   `hom_multiplication_baseChange_fst` is the compatibility of `[n]` with base change. Item 5
   then gives `finiteWeilLevelBilinearMap_baseChange`. The nondegeneracy equivalence follows
   because both point identifications are additive equivalences.

## Provenance and scope

This is derived infrastructure. Edixhoven, van der Geer and Moonen, *Abelian Varieties*
(preliminary draft), Chapter VII, Proposition (7.4), printed p.99 / PDF p.103, states that the
character isomorphism `δ_T` of a free quotient "is compatible with base change `T′→T`". Its
proof defines `δ_T` by replacing `S` with `T`, and its last line on PDF p.104 says the
compatibility is "immediate from the construction". The finite Weil pairing of Chapter XI,
Definition (11.11), is built from Theorem (7.5), which applies (7.4) to the kernel of an isogeny.
This module formalizes that compatibility for the specific Lean constructions above, with the
ground base changed from `S` to `S'`. The Lean route is the one described above, not a quotation
of the source.

The module does not prove nondegeneracy of the pairing, Cartier duality, or any bijectivity of
`dualKernelPointCharacter`. It only transports such statements between `S` and `S'`. For a
geometric point `s : Spec K ⟶ S` one can take `b = s` and `T = Over.mk (𝟙 _)`; then `T₀` is
`Over.mk (𝟙 _ ≫ s)`, which is rewritten to `Over.mk s` by `Category.id_comp`.
