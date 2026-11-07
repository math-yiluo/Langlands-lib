# The compact-restriction inertia decomposition from Renard VI.3.2(ii),(iii)

This module is an internal reduction for the proof of
`Langlands.CuspidalSupport.RationalCompactRestrictionInertiaDecompositionStatement`.
It does not prove that statement on its own. Its last theorem derives it from
two published propositions that are taken as hypotheses. These are Renard
VI.3.2(ii) (`RationalNormKernelFiniteRestrictionStatement`) and VI.3.2(iii)
(`RationalNormKernelTwistEquivalenceStatement`). Neither proposition is proved
here, and neither is a premise of the final target. The final proof will apply
this theorem to their independently published proofs. The generic open-subgroup and open-normal-family projectors are imported from
[OpenNormalFamilyProjector](OpenNormalFamilyProjector.md). That module preserves
the original declaration names, signatures and proofs; this module re-exports
them and contains only the rational application.

## The rational application

`rationalCompactRestrictionInertiaDecomposition_of_normKernel` assumes
`hfin : RationalNormKernelFiniteRestrictionStatement.{uF, uV}` and
`htw : RationalNormKernelTwistEquivalenceStatement.{uF, uV, uV}`. It concludes
`RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV}`, the
unchanged target.

The proof introduces the field, the connected reductive group scheme and the
target's instances, and puts the canonical topology `rationalPointTopology F G.X`
on the rational points. It then introduces the irreducible `π` and the target's
compact-coefficient premise for the restriction of `π` to
`N := Plancherel.rationalCommonNormKernel G`. `N` is open by the published
`Plancherel.isOpen_rationalCommonNormKernel` and normal by the published
instance. The finite irreducible spanning family of the restriction comes from
the last conjunct of `hfin` applied to `π`. The semisimplicity and
finite-length conjuncts are not used.

The target's factors `rationalInertiaDecompositionProperties G π` are equal to
`SmoothRep.irreducibleSubquotientProperties (IsRationalInertiaRelated G π)`. Both
Bool cases hold by `rfl`: the `true` factor is `rationalInertiaBlockProperty G π`
and the `false` factor is `rationalInertiaComplementProperty G π`. So it
suffices to apply `openNormalFamily_categoryDecomposition` with
`P := IsRationalInertiaRelated G π`.

The remaining test compares restrictions with inertia. Fix an irreducible `D`.
`htw` applied to `D` and `π` gives `(A ↔ B) ∧ (A ↔ C)`. Here `A` says that the
restrictions of `D` and `π` to `N` are equivalent, `B` says that
`Langlands.twist χ D ≃ π` for some `χ` in the published unramified-character
subgroup, and `C` says that a nonzero intertwiner maps the restriction of `D`
into the restriction of `π`. Hence `C ↔ B`. It remains to identify `B` with
`IsRationalInertiaRelated G π D`, that is, with `∃ χ, D ≅ rationalUnramifiedTwist G χ π`:

- From `B`: the equivalence `twist χ D ≃ π` is an isomorphism
  `rationalUnramifiedTwist G χ D ≅ π` (`SmoothRep.mkIso`). Its inverse shows
  `IsRationalInertiaRelated G D π`, and the published
  `IsRationalInertiaRelated.symm` (inverse character) gives
  `IsRationalInertiaRelated G π D`.
- Conversely, `IsRationalInertiaRelated.symm` yields `χ` and
  `π ≅ rationalUnramifiedTwist G χ D`. The inverse isomorphism, converted by
  `SmoothRep.equivOfIso`, is an equivalence `twist χ D ≃ π`.

The representation underlying `rationalUnramifiedTwist G χ D` is
definitionally `Langlands.twist χ.val.toMonoidHom D.representation`, so these
conversions involve no twist-direction change beyond the explicit use of
`symm`.

## Provenance and scope

This theorem is an internal composition of the published rational inertia API
and the generic projector decomposition imported from
`OpenNormalFamilyProjector`. Its mathematical route follows Renard VI.3.3.1,
which constructs the inertia block from the finitely many restriction types
given by VI.3.2(ii), using the IV.1.5 projectors, and identifies it with the
inertia class by VI.3.2(iii). No step of the source proof of VI.3.2 is reproved
here. The generic declarations were moved to their own module by Worker 1740,
with their original author Worker 1168 as coauthor. The rational theorem and
its statement are unchanged. The module adds no axioms; its declarations depend
only on `propext`, `Classical.choice` and `Quot.sound`.
