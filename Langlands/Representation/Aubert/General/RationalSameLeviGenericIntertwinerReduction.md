# Reduction of the same-Levi intertwiner statement to represented parabolics

Author: Worker 194.

This module proves `rationalSameLeviGenericNonzeroIntertwiner_of_represented`:
`RepresentedSameLeviGenericNonzeroIntertwinerStatement.{u, v}` implies
`RationalSameLeviGenericNonzeroIntertwinerStatement.{u, v}`. The hypothesis is the
version for actual represented parabolics that share one Levi scheme. The target is
the version for the literal standard subgroups `P_J` and `g P_I g⁻¹` of `G(F)`, with
their common literal Levi `L_J`. All declarations here are internal bridge lemmas
between two Library interfaces and do not quote a source.

## Declarations

- `exists_ne_zero_hom_of_isos`: if `A ≅ A'`, `B' ≅ B` and some morphism `A' ⟶ B'` is
  nonzero, then some morphism `A ⟶ B` is nonzero. It composes with the isomorphisms
  and cancels them.
- `RepresentedParabolic.leviInductionObjIsoOfPointImages`: let `p : P ⟶ G` be a
  represented parabolic with Levi `l` and radical `r`, and let `P', M', U'` be its
  point images. Let `e : M(F) ≃ₜ* M'` agree with the point map of `l ≫ p`. Then
  `leviInductionFunctor p l r … X` is isomorphic to
  `normalizedInductionFunctor h' hU'` applied to the pullback of `X` along `e⁻¹`.
  After substituting the point images, `e` equals `leviPointsEquiv p l` by
  extensionality. The isomorphism is then the identity, because `leviInductionFunctor`
  is defined as this pullback followed by the induction from the point images.
- `RepresentedParabolic.exists_ne_zero_normalizedInduction_of_leviInduction`: the
  transport step, with every scheme and subgroup a variable. Take a second represented
  parabolic `q` with the same Levi scheme `M`, point images `Q', M', V'`, a smooth
  representation `σ` of `M'`, an open-kernel character `χ` of `M'`, and an unramified
  character `ψ` of `M(F)` with `ψ m = χ (e m)`. If some morphism
  `i_P^G((σ ∘ e)ψ) ⟶ i_Q^G((σ ∘ e)ψ)` between the represented inductions is nonzero,
  then some morphism between the normalized inductions of `σ.twist χ` from
  `(P', M', U')` and `(Q', M', V')` is nonzero. The proof builds the identity-carrier
  isomorphism `σ.twist χ ≅ e⁻¹*((σ ∘ e).twist ψ)`, applies
  `leviInductionObjIsoOfPointImages` on both sides, and uses
  `exists_ne_zero_hom_of_isos`. The hypothesis on `ψ` is typed exactly like the
  character binder of the represented statement: unramified characters of `M(F)` for
  the rational norm family, with the canonical rational-point topology. The openness
  proof of its kernel is a separate argument. This makes the instantiation in the main
  proof syntactic.
- `RationalPointFamily.range_leviHom_carrier`, `pointImage_parabolicHom` and
  `pointImage_leviToParabolic_comp`: the rational points of the represented standard
  Levi and parabolic are the literal `levi i ν K` and `parabolic i ν K`. They follow
  from `Standard.isRepresentedBy_leviHom`, `Standard.isRepresentedBy_parabolicHom` and
  `Standard.leviToParabolic_comp`.
- `comp_innerIso_inv_rationalPoint` and `pointImage_comp_innerIso`: the inner
  automorphism `G.innerIso g` acts on points by conjugation, so the point image of
  `j ≫ (G.innerIso g).hom` is `conjugateSubgroup g (pointImage j)`.
- `pointImage_leviHom_comp_innerIso_inv`, `range_leviHom_comp_innerIso_inv`,
  `leviSchemeIsoOfConj` and `leviSchemeIsoOfConj_hom_comp`: assume
  `x ∈ L_J ↔ g⁻¹ x g ∈ L_I` and that both Levi schemes are connected reductive. Then
  `L_J` conjugated by `g⁻¹` and `L_I` have the same rational points. Both are smooth,
  connected and closed, so `SubgroupFunctor.range_le_of_localField_points` applied in
  both directions shows that their ranges agree as subgroup functors.
  `IsClosedSubgroup.sourceIsoOfRangeEq` then gives the scheme isomorphism
  `eL : L_J ≅ L_I` with `eL.hom ≫ leviHom_I = leviHom_J ≫ (G.innerIso g).inv`.

## Proof of the reduction

Fix the data of the target statement. Use `T2Space k` from
`BruhatTits.localField_t2Space` and the canonical `pointTopology` on `G(F)`.

1. `standard_representatives_geometric_of_standardCocharacter` gives the geometric
   facts for the standard represented parabolic `P_J`, with Levi `leviToParabolic J`
   and radical `unipotentToParabolic J`, and likewise for `P_I`.
2. The second represented parabolic is `q = parabolicHom I ≫ (G.innerIso g).hom`, with
   Levi `lQ = eL.hom ≫ leviToParabolic I` and radical `unipotentToParabolic I`. The
   Library lemmas `IsParabolicSubgroup.comp_iso`, `IsRationalLeviSubgroup.iso_comp`
   and `isIso_subgroupMultiplication_iso_comp` transfer the hypotheses. The relation
   `leviSchemeIsoOfConj_hom_comp` gives the shared-Levi equation
   `leviToParabolic J ≫ parabolicHom J = lQ ≫ q`.
3. The point images of `q`, `lQ ≫ q` and `unipotentToParabolic I ≫ q` are
   `g P_I g⁻¹`, `L_J` and `g U_I g⁻¹`. These are the subgroups of the decomposition
   `conjugateWithLevi g hIJ` used by `conjugateInductionFunctor`.
4. Let `e = leviRationalPointHomeomorph i ν J : L_J(F) ≃ₜ* L_J`. Its point values are
   those of both Levi embeddings. The pullback `σ ∘ e` is irreducible and admissible
   by `isIrreducible_comp_continuousMulEquiv_iff` and
   `isAdmissible_comp_continuousMulEquiv`.
5. The represented statement, applied to these two parabolics and to `σ ∘ e`, gives a
   nonzero polynomial `poly`. The target locus `leviUnramifiedPrincipalOpen i ν J hLJ
   poly` is by definition the preimage of `rationalUnramifiedPrincipalOpen` under
   `(leviRationalUnramifiedCharacterHomeomorph i ν J).symm`. For `χ` in this locus,
   `ψ = (leviRationalUnramifiedCharacterHomeomorph i ν J).symm χ` therefore lies in the
   represented locus, and `ψ m = χ (e m)` holds by definition.
6. `exists_ne_zero_normalizedInduction_of_leviInduction` turns the represented nonzero
   morphism into a nonzero morphism from `normalizedInductionFunctor` of `P_J` to
   `conjugateInductionFunctor` of `g P_I g⁻¹`, applied to `σ.twist χ`. The latter
   functor is by definition `normalizedInductionFunctor` of the conjugate
   decomposition.

## Elaboration notes

The main proof sets `maxHeartbeats` to 800000 and
`backward.isDefEq.respectTransparency.types false`, as
`CuspidalSupport.BernsteinRepresentedInduction` does for the same comparison. It
passes the two openness proofs of the twists as holes, which unification fills from
the goal and from the represented morphism. `SmoothRep.twist` is an abbreviation, so
a syntactic difference in its proof argument would make Lean unfold the twist and the
group-scheme structure of the concrete Levi scheme.
