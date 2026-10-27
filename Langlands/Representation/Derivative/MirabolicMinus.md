# Mirabolic minus localization functors

Author: Worker 749.

This module constructs the Bernstein–Zelevinsky minus functors `Ψ⁻` and
`Φ⁻` on actual smooth complex representations of the actual mirabolic
groups, in an unnormalized form and in an explicit determinant-normalized
form. It proves only elementary construction laws: quotient, action,
smoothness, morphism and functor laws. It contains no Haar-modulus
identification, exactness, adjunction, plus functor, derivative iteration,
filtration, pairing or classification result.

## Source

The registered original is Bernstein and Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977),
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

- §1.8(b), printed p.444 (PDF page 5, zero-based index 4): for closed
  subgroups `M`, `U` with `M` normalizing `U` and a character `θ` of `U`
  normalized by `M`, the space `E(U,θ)` is spanned by the vectors
  `π(u)ξ - θ(u)ξ`. The quotient `r_{U,θ}(E) = E/E(U,θ)` carries the action
  `δ(m)(ξ + E(U,θ)) = mod_U^(-1/2)(m) · (π(m)ξ + E(U,θ))`. Here `mod_U(m)`
  is the topological module of the conjugation automorphism `u ↦ m u m⁻¹`.
  The printed exponent is negative; this was checked on the rendered page.
  The definition ends on p.445 (PDF page 6), which names the result the
  `θ`-localisation `r_{U,θ}(π)`.
- §3.1, printed p.450 (PDF page 11, zero-based index 10): `P_n ⊂ GL_n` has
  last row `(0,...,0,1)`. Its unipotent radical `V_n` is the last-column
  subgroup. `G_(n-1)` and `P_(n-1)` are embedded in the standard way, and
  `θ((v_ij)) = ψ(v_(n-1,n))` for a fixed nontrivial additive character `ψ`.
- §3.2, printed pp.450–451 (PDF pages 11–12, zero-based indices 10–11):
  `Ψ⁻ = r_{V,1} : Alg P_n → Alg G_(n-1)` and
  `Φ⁻ = r_{V,θ} : Alg P_n → Alg P_(n-1)`, normalized as in §1.8. The source
  notes that these differ from the functors of its reference [1] by a twist
  with `mod^(1/2)`.

The task contract calls the pages 5 and 11–12 zero-based indices, but they
are the one-based PDF page numbers. The printed page numbers above were
checked against the PDF. No applicable errata entry was found in
the supplied literature or public notes. The published audit
`notes/henniart/segment-head-independence.md` records the same.

### Rank shift

`GeneralLinear.mirabolic n F.Carrier` is the source's `P_(n+1)`, and
`GeneralLinear.Mirabolic.radical n F.Carrier` is `V_(n+1)`. Hence:

- `psiMinusUnnormalized T n` and `psiMinus T n` are the source's `Ψ⁻` for
  `P_(n+1) → GL_n`;
- `phiMinusUnnormalized T ψ n` and `phiMinus T ψ n` are the source's `Φ⁻`
  for `P_(n+2) → P_(n+1)`, localized at a character of
  `radical (n+1) F.Carrier = V_(n+2)`.

Every `n : ℕ` is allowed. At `n = 0`, `Ψ⁻` is the functor `P_1 → GL_0`,
localizing at the trivial character of `V_1`. `Φ⁻` is the functor
`P_2 → P_1`, using the published character on `V_2`. No character is defined
on a radical without coordinates.

### What the source supplies and what is derived

The source supplies the quotient `E/E(U,θ)`, the choice `θ = 1` for `Ψ⁻`
and the positive last-coordinate character for `Φ⁻`, the groups and their
standard embeddings, and the normalization sign `-1/2`. Everything else
here is derived implementation: the pullback of the descended range-subgroup
action along the published continuous group equivalences, the morphism and
functor laws, smoothness, and the open-kernel facts. So is the replacement
of `mod_U^(-1/2)` by an explicit determinant character. This module does
not prove that the Haar automorphism modulus equals the determinant norm.
That comparison is a separate proof obligation, and no definition here
assumes it.

## Parameters

Throughout, `p : ℕ` is prime (`[Fact p.Prime]`), `F : PadicField.{uF} p`,
and `T : F.TopologicalData` is supplied. Every functor statement installs
`letI := T.topology`; no canonical topology is substituted. The additive
character is `ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology`, which
bundles continuity and nontriviality, so the trivial additive character is
not covered. Representations are `SmoothRep.{0, uF, uV} ℂ _`. Every functor
keeps the carrier universe `uV`, which is independent of `uF`.

## Local pullback helper

In namespace `Langlands.Derivative.Mirabolic`, for any commutative ring `R`
and topological groups `G`, `H`:

- `continuousPullbackMap φ f` is the same linear map as the intertwiner `f`,
  viewed as an intertwiner between `ρ.comp φ` and `σ.comp φ`;
- `continuousPullback φ hφ A` is
  `SmoothRep.of (A.representation.comp φ) (isSmooth_comp φ hφ A.isSmooth)`;
- `continuousPullbackFunctor φ hφ` is the functor with these objects and
  maps; its identity and composition laws hold by `rfl`.

This helper is local and elementary. It avoids importing
`SmoothRep.pullbackFunctor` from `Representation/CompactCoefficient/GroupTransport`,
which has a heavier import chain. The carriers and linear maps are unchanged.

## Unnormalized Ψ⁻

`psiMinusUnnormalized T n` is

```
Jacquet.Localization.smoothFunctor (radical n F.Carrier) 1 (leviSubgroup n F.Carrier)
    leviSubgroup_le_normalizer
    (Jacquet.Localization.isInvariant_one _ _ leviSubgroup_le_normalizer)
  ⋙ continuousPullbackFunctor leviContinuousEquiv.toMonoidHom leviContinuousEquiv.continuous
```

It sends `SmoothRep ℂ (mirabolic n F.Carrier)` to
`SmoothRep ℂ (GeneralLinear n F.Carrier)`. The published smooth localization
functor acts on the actual quotient through the actual Levi range subgroup.
The pullback along the published continuous equivalence
`GL_n ≃ₜ* leviSubgroup n` turns this into an action of `GL_n`.

`psiMinusQuotient T n A` is the canonical linear map
`Jacquet.Localization.mk A.representation (radical n F.Carrier) 1` from `A` to
`Jacquet.Localization.Coinvariants A.representation (radical n F.Carrier) 1`.
The proved laws are:

- `psiMinusUnnormalized_obj_carrier`: the object carrier is that
  `Coinvariants` type (`rfl`);
- `psiMinusUnnormalized_obj_representation`: the object action is
  `Jacquet.Localization.action ... (leviSubgroup n F.Carrier) ...` composed
  with `leviEquiv.toMonoidHom` (`rfl`);
- `psiMinusQuotient_surjective` and `ker_psiMinusQuotient`: `q` is surjective,
  and its kernel is exactly
  `Jacquet.Localization.relations A.representation (radical n F.Carrier) 1`,
  from `mk_surjective` and `ker_mk`;
- `psiMinusQuotient_radical`: `q(A.representation u v) = q(v)` for
  `u : radical n F.Carrier`, by `mk_apply_subgroup` and the trivial character;
- `psiMinusUnnormalized_action`:
  `g • q(v) = q(A.representation (levi g) v)` for `g : GeneralLinear n F.Carrier`
  (`rfl`);
- `psiMinusUnnormalized_isSmooth`: every output object is smooth. There is no
  exactness or finite-length hypothesis.
- `psiMinusUnnormalized_map_quotient`: the image of `f : A ⟶ B` sends
  `q_A(v)` to `q_B(f v)` (`rfl`);
- `psiMinusUnnormalized_map_equivariant`, `psiMinusUnnormalized_map_id` and
  `psiMinusUnnormalized_map_comp`: the induced maps are `GL_n`-equivariant,
  and the identity and composition laws hold.

## Unnormalized Φ⁻

`phiMinusUnnormalized T ψ n` is

```
Jacquet.Localization.smoothFunctor (radical (n+1) F.Carrier) (T.mirabolicTheta ψ n)
    (successorSubgroup n F.Carrier) successorSubgroup_le_normalizer (theta_isInvariant ψ n)
  ⋙ continuousPullbackFunctor successorContinuousEquiv.toMonoidHom
      successorContinuousEquiv.continuous
```

It sends `SmoothRep ℂ (mirabolic (n+1) F.Carrier)` to
`SmoothRep ℂ (mirabolic n F.Carrier)`. It uses the published normalizer proof
`successorSubgroup_le_normalizer` and the published invariance proof
`theta_isInvariant` for the actual successor subgroup, then pulls back along
`P_(n+1) ≃ₜ* successorSubgroup n`.

`phiMinusQuotient T ψ n A` is
`Jacquet.Localization.mk A.representation (radical (n+1) F.Carrier) (T.mirabolicTheta ψ n)`,
with codomain the actual `Coinvariants` type. The laws `phiMinusUnnormalized_obj_carrier`,
`phiMinusUnnormalized_obj_representation`, `phiMinusQuotient_surjective`,
`ker_phiMinusQuotient`, `phiMinusUnnormalized_isSmooth`,
`phiMinusUnnormalized_map_quotient`, `phiMinusUnnormalized_map_equivariant`,
`phiMinusUnnormalized_map_id` and `phiMinusUnnormalized_map_comp` match the
`Ψ⁻` laws. The two that differ are:

- `phiMinusQuotient_radical`:
  `q(A.representation u v) = (T.mirabolicTheta ψ n u : ℂ) • q(v)` for
  `u : radical (n+1) F.Carrier`, which is `mk_apply_subgroup`;
- `phiMinusUnnormalized_action`:
  `h • q(v) = q(A.representation (successor h) v)` for
  `h : mirabolic n F.Carrier` (`rfl`).

## Explicit determinant normalization

The normalization characters are the exact expressions

```
psiMinusCharacter T n := realPowerCharacter (T.determinantNorm n) (-(1 / 2 : ℝ))
phiMinusCharacter T n :=
  realPowerCharacter ((T.determinantNorm (n+1)).comp (mirabolic n F.Carrier).subtype)
    (-(1 / 2 : ℝ))
```

on `GL_n` and on `P_(n+1) ⊂ GL_(n+1)`. `T.determinantNorm` is the
residue-normalized absolute value of the determinant. These are the
`|det|^(-1/2)` characters of the actual output groups. This is the
explicit determinant-normalized convention. Its sign follows BZ77 §1.8(b).
Its use of `|det|` in place of `mod_U` is a convention, not a theorem
proved here.

`isOpen_ker_psiMinusCharacter` and `isOpen_ker_phiMinusCharacter` prove the
kernels open. Each applies `isOpen_ker_realPowerCharacter` to the open kernel
`T.isOpen_ker_determinantNorm`. The topological-group instance
`T.generalLinearTopologicalGroup` supplies separately continuous
multiplication. For `Φ⁻`, the kernel of the composite is the preimage of an
open set under the continuous subtype inclusion.

The normalized functors are

```
psiMinus T n   := psiMinusUnnormalized T n ⋙ SmoothRep.twistFunctor (psiMinusCharacter T n) _
phiMinus T ψ n := phiMinusUnnormalized T ψ n ⋙ SmoothRep.twistFunctor (phiMinusCharacter T n) _
```

`psiMinus_eq` and `phiMinus_eq` state these equalities of functors (`rfl`).
The twist keeps carriers and linear maps, so the normalized functors keep the
actual quotient carriers (`psiMinus_obj_carrier`, `phiMinus_obj_carrier`) and
the quotient-induced maps (`psiMinus_map_quotient`, `phiMinus_map_quotient`).
The normalized action formulas are

```
psiMinus_action:  g • q(v) = (realPowerCharacter (T.determinantNorm n) (-(1/2)) g : ℂ)
                               • q(A.representation (levi g) v)
phiMinus_action:  h • q(v) = (realPowerCharacter ((T.determinantNorm (n+1)).comp
                                 (mirabolic n F.Carrier).subtype) (-(1/2)) h : ℂ)
                               • q(A.representation (successor h) v)
```

`psiMinus_action_eq_smul` and `phiMinus_action_eq_smul` state that on every
vector of the quotient, the normalized action is the character value times the
unnormalized action. The laws `psiMinus_isSmooth`,
`psiMinus_map_equivariant`, `psiMinus_map_id` and `psiMinus_map_comp` hold,
and so do their `phiMinus` counterparts.

## Imports and independence

The module imports `Langlands.Representation.Derivative.MirabolicCharacter`,
`Langlands.Representation.Category.Twist`,
`Langlands.Representation.Twist.RealPower`,
`Langlands.Representation.Smooth.Transfer.PullbackProof` and
`Langlands.Group.GL.NormalizedCharacter`. Their `Langlands` import closure
has 49 modules on groups, local fields, smooth representations, twists,
localization and Whittaker characters. It contains no classification,
segment, multisegment, square-integrable, tempered or socle module. Neither
the module nor its closure uses `SegmentHeadProductIrreducibility`,
`GenericSegmentProductUniqueness`, `SquareIntegrableLanglandsClassification`,
or any result of the excluded exhaustion, existence, coverage, conversion,
uniqueness or segment-classification tasks.
