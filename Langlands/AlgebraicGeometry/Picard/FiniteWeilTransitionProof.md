# Proof of divisibility compatibility of the actual finite Weil pairing

`Langlands.AbelianScheme.relativeFiniteWeilTransition` proves the
published proposition
`Langlands.AbelianScheme.RelativeFiniteWeilTransitionStatement`
(module `Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionStatement`),
which is imported unchanged. All of the statement's quantifiers stay
general: a quasi-separated base `S`, an actual abelian scheme `A/S`,
its `HasDualScheme` witness, the seven dual-constructor propositions,
the inverse Poincaré bundle `MA` with its evaluation isomorphism, and
positive `n ∣ m`. Write `r = m / n`, `Aᵛ` for the constructed dual
group scheme `dualCommGroupSchemeFromEvaluation`, and
`beta_n(y)(x)` for the existing intrinsic evaluation behind
`finiteWeilPairing`. The proof adds no hypothesis. The positivity
assumptions are not used. Nothing in it requires `n` or `m` to be
invertible on `S`, or any étaleness, smoothness or properness of the
dual.

The proof has two parts. The first is a new compatibility of the
Library's dual-kernel characters with composition of homomorphisms.
It is stated for arbitrary homomorphisms of abelian schemes
`h = f ≫ g` (section `Composition`). The second specializes it to
`[m] = [r] ≫ [n]` and identifies the two dual points involved
(section `Transition`).

## 1. Kernel characters along a composite (section `Composition`)

Let `f : A ⟶ B`, `g : B ⟶ C` and `h : A ⟶ C` be homomorphisms of
abelian schemes over `S` with `f ≫ g = h`. Fix a scheme `T` over `S`.
Let `κ : ker h ⟶ ker g` satisfy
`κ ≫ ι_g = ι_h ≫ f`, where the `ι` are the kernel inclusions.

**Trivializations.** Let `α` trivialize the pullback of a module `M`
on `T ×_S C` along the family map `T ×_S B → T ×_S C` of `g`. Then
`compositeHomPullbackTrivialization` trivializes the pullback of
`pullback (𝟙) M` along the family map of `h`. It composes three
isomorphisms:

1. the published square comparison `squarePullbackIso`, for the square
   `homFamilySpaceMap_composite_square`. That square comes from
   `homFamilySpaceMap_comp` and has `𝟙` as its fourth side;
2. the pullback of `α` along the family map of `f`;
3. `pullbackUnitIso`.

**Translation automorphisms.** Let `k` be a point of `ker h` over
`a : U ⟶ T`, and let `k'` be a point of `ker g` with
`k' ≫ ι_g = k ≫ ι_h ≫ f`. Lemma `kernelTranslationAut_comp` proves
that the translation automorphism `kernelTranslationAut` for `h`, `k`
and the composite trivialization is the pullback of the one for `g`,
`k'` and `α`. The pullback is `structureAutPullback` along the family
map of `f`. The proof needs three facts:

- naturality of `homFamilySpaceMap f`;
- `kernelShear h a k ≫ f_T = f_U ≫ kernelShear g a k'`, from
  `shear_homFamilySpaceMap` and the hypothesis on `k'`;
- the published `equalCompositeUnitAut_square` and
  `equalCompositeUnitAut_precomp`.

`equalCompositeUnitAut_congr` carries out the substitution of equal
maps inside `equalCompositeUnitAut`.

**Scalars and units.** The published `structureAutScalar_pullback`
then gives `kernelTranslationScalar_comp`: the global unit for `h` is
the image of the global unit for `g` under `appTop` of the family map
of `f`. Lemma `relativeUnitDescend_homFamilySpaceMap` states that
descent of global units to `T` commutes with this map. It follows from
injectivity of `relativeUnitsPullback` and
`homFamilySpaceMap_fst f U`. Together these prove
`kernelTranslationUnit_comp`: the descended units on the parameter
scheme agree.

**Characters.** `intrinsicKernelCharacter_evaluation_comp` states:

```text
chi_g(α)(x ≫ κ) = chi_h(composite trivialization)(x)
```

for every `x : T ⟶ ker h`. It is proved under the injective
`Gm.pointsEquiv` by rewriting both sides with
`characterEvaluation_section`,
`characterHomEquiv_intrinsicKernelCharacter`,
`intrinsicKernelCharacterHom_points` and
`baseChangePointsEquiv_sectionPointsEquiv_symm`. That last lemma
identifies the base-change point of the section attached to `x` with
`sectionBaseIso ≫ x`. The remaining goal is
`kernelTranslationUnit_comp`, with `k'` the image of the section under
`κ`.

**Dual-kernel characters.** `dualKernelCharacter_evaluation_comp`
transfers this to the actual Poincaré-derived characters
`dualKernelCharacter`. Let `p, p' : T ⟶ Cᵛ` be equal points. The proof
takes as arguments that `p` is killed by `gᵛ` and `p'` by `hᵛ`. It
does not derive one from the other. Then

```text
beta_g(p)(x ≫ κ) = beta_h(p')(x).
```

The published `dualKernelCharacter_eq_intrinsic` computes the left
side with `dualKernelPullbackModuleIso` for `g`.
`dualKernelCharacter_eq_of_iso` computes the right side with the
representative `pullback (𝟙) M`. It is isomorphic to `M` by
`Scheme.Modules.pullbackId`, and the composite trivialization
trivializes it. So no dual of a composite homomorphism is needed.
This is a relative, morphism-level analogue of the composition
compatibility of kernel pairings in Edixhoven–van der Geer–Moonen,
*Abelian Varieties*, Proposition (11.21)(ii), which motivates it. The
Lean proof does not follow that source.

## 2. The transition (section `Transition`)

- `multiplication_div_comp`: `[r] ≫ [n] = [m]` on `A`. It unfolds
  `multiplication` as an integer multiple of `𝟙` and uses
  `Nat.div_mul_cancel`.
- `characterEvaluation_nsmul`: evaluating `r • χ` gives the `r`-th
  power. This is induction with `Cartier.characterEvaluation_add`.
- `dualTorsionCharacter_pow`: `chi_n(y ^ r) = r • chi_n(y)`. It is
  `map_nsmul` for the published `dualTorsionCharacterAddHom`.
- `dualTorsionCharacter_transition`: for `x : T ⟶ A[m]` and
  `y : T ⟶ Aᵛ[m]`, write `κ` for each of the two `kernelTransition`
  maps, and `κ x`, `κ y` for `x ≫ κ`, `y ≫ κ`. Then

  ```text
  beta_n(κ y)(κ x) = beta_m(y)(x) ^ r.
  ```

  The two lemmas above rewrite the right side as
  `beta_m(y ^ r)(x)`. After unfolding `dualTorsionCharacter` and
  `dualKernelPointCharacter`, apply
  `dualKernelCharacter_evaluation_comp` with `f = [r]`, `g = [n]`,
  `h = [m]`, and `κ = kernelTransition A.toGrp h`. The required
  equation for `κ` is the published `kernelTransition_ι`. The two dual
  points are equal by a calculation that uses
  `relativeDualMultiplicationKernelIso_inv_ι` and `kernelTransition_ι`
  for `Aᵛ`. Here `ι_k` is the torsion inclusion
  `Aᵛ[k] ⟶ Aᵛ`:

  ```text
  κ y ≫ ι_n = y ≫ ι_m ≫ [r] = (y ≫ ι_m) ^ r = y ^ r ≫ ι_m.
  ```

  The middle step uses `points_multiplication`. The last step uses
  `MonObj.pow_comp`, because `ι_m` is a group homomorphism.
- `finiteWeilValue_transition`: the point form
  `value_n(κ x, κ y) = value_m(x, y) ≫ mu.transition S h`. It is proved
  with the published uniqueness lemma `finiteWeilValue_unique`. The
  right side is composed with the inclusion `μ_n ⟶ G_m`, and
  `mu.transition_incl` (`transition ≫ incl_n = incl_m ≫ [r]`) is
  applied. Then `finiteWeilValue_incl`, `points_multiplication` and
  `dualTorsionCharacter_transition` turn the composite into
  `beta_m(y)(x) ^ r = beta_n(κ y)(κ x)`.

## 3. The statement

`relativeFiniteWeilTransition` applies `finiteWeilValue_transition`
to the universal point `(prod.fst, prod.snd)` of
`A[m] ×_S Aᵛ[m]`. It then rewrites with `finiteWeilPairing_points`,
`prod.lift_fst_snd` and `prod.lift_map`. The result is the asserted
equation of actual morphisms
`A[m] ×_S Aᵛ[m] ⟶ μ_n` over `S`.

Every step is an equation of morphisms of schemes over `S`, or an
equation of points over an arbitrary test scheme. The final step uses
the universal point. Nothing is checked only on geometric points, so
nonreduced test schemes and every residue characteristic are covered.

## Scope

This module proves only the transition compatibility. It does not
prove Cartier duality, perfectness, alternation, functoriality along
other homomorphisms, or the inverse-limit Tate pairing. The
composition lemma of section 1 is proved for arbitrary homomorphisms
of abelian schemes. Its only application here is to multiplication
maps.
