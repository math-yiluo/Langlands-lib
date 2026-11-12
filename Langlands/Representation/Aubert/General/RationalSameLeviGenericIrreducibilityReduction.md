# Same-Levi generic irreducibility from Renard VI.8.4 and one irreducible twist

This module proves that the published same-Levi target
`RationalPointFamily.RationalSameLeviGenericInductionIrreducibilityStatement.{u, v}`
follows from two published propositions that the Library does not yet prove:

- `Renard.AlgebraicFamily.InducedIrreducibilityOpenStatement.{u, v}` (Renard
  VI.8.4). For an actual rational parabolic `P = MU` and an irreducible smooth
  representation `ρ` of `M(k)`: if one unramified twist `ρ ⊗ ψ₀` has
  irreducible normalized induction, then some polynomial `f` in the full
  rational-norm unramified-character coordinates of `M` has `ψ₀` in its
  principal open `Plancherel.rationalUnramifiedPrincipalOpen M … f`, and every
  `ψ` in that principal open has irreducible induction.
- `Renard.AlgebraicFamily.IrreducibleInducedTwistExistenceStatement.{u, v}`
  (the existence consequence of Konno, Theorem 4.2). Every irreducible
  admissible `ρ` of the actual Levi points has one unramified twist whose
  normalized induction is irreducible.

The main theorem takes both propositions as explicit hypotheses. It adds no
other premise, and it proves neither input. The final declaration,
`RationalPointFamily.rationalSameLeviGenericInductionIrreducibilityFromInputs`,
has exactly the type
`RationalSameLeviGenericInductionIrreducibilityFromInputsStatement.{u, v}`
(module `RationalSameLeviGenericIrreducibilityFromInputsStatement`). It is the
main theorem, read as that implication.

## Density: the Levi scheme of `J` is a conjugate of the Levi scheme of `I`

`range_le_of_pointImage_le` works over an infinite field. Let `a : A ⟶ G` be a
homomorphism from a connected reductive group, and `b : B ⟶ G` a closed
subgroup. If every rational point of `a` lies in the rational points of `b`,
then `a` factors through `b` on every test scheme. Connected reductive groups
are smooth, so `reductiveRationalPointDensity` and
`RationalDensity.rationalPointsDetectFunctions_of_smooth` show that rational
points detect functions on `A`. `RationalPointsDetectFunctions.exists_factor`
then factors `a` through the closed immersion `b`.

`exists_iso_comp_innerIso_of_pointImage` applies this in both directions to
`a` and `b ≫ innerIso g`. The two closed subgroups need connected reductive
sources and rational points conjugate by `g`, in the sense
`x ∈ a(k) ↔ g⁻¹ x g ∈ b(k)` (`mem_pointImage_comp_innerIso`). Their subgroup
functors are then equal. `IsClosedSubgroup.sourceIsoOfRangeEq` gives an
isomorphism `e : A ≅ B` with `e.hom ≫ b ≫ innerIso g = a`.

## Comparison: represented induction and literal induction

`leviInduction_isIrreducible_iff_of_pointImage` compares two inductions. One is
the represented induction `leviInductionFunctor p l r` of a representation `A`
of `M(k)`. The other is the subgroup induction
`normalizedInductionFunctor h hU'` of a representation `B` of a subgroup `N`,
for any semidirect decomposition `P' = N ⋉ U'` of `G(k)` with the same point
images as `p`, `l ≫ p` and `r ≫ p`. Suppose a linear equivalence `f : A ≃ B`
intertwines the actions along a map `φ : M(k) → N` that lifts `l ≫ p` on
points. Then one induction is irreducible exactly when the other is. The proof
unfolds `leviInductionFunctor_obj` and applies the published
`RepresentedParabolic.normalizedInduction_isIrreducible_congr`. The required
equivariance is the hypothesis on `f`, read through `leviPointsEquiv`.

## Generic irreducibility for one actual parabolic

`exists_generic_leviInduction_isIrreducible` combines the two inputs for one
actual rational parabolic `(p, l, r)` and one irreducible admissible `ρ` of
`M(k)`. The existence input gives a twist `ψ₀` whose induction is irreducible.
The VI.8.4 input then gives a polynomial `f` whose principal open
`rationalUnramifiedPrincipalOpen M f` contains `ψ₀`, such that every `ψ` in it
has irreducible induction. `f` is nonzero because its principal open is
nonempty.

## The main theorem

`RationalPointFamily.rationalSameLeviGenericInductionIrreducibility_of_inputs`
proves the target from `hOpen` and `hExist`. Fix the data of the target. `k` is
infinite, because a nonarchimedean local field has an element of valuation
`> 1` whose powers are pairwise distinct.
`standard_representatives_geometric_of_standardCocharacter` supplies, for `I`
and for `J`, the actual standard parabolic, Levi and radical representatives
with all represented-parabolic hypotheses. Their point images are the literal
subgroups `parabolic`, `levi` and `unipotent`
(`Standard.isRepresentedBy_parabolicHom`, `Standard.isRepresentedBy_leviHom`,
`standard_unipotent_pointImage`).

- **Conjugate parabolic with Levi source `L_J`.** The density section, applied
  to `Standard.leviHom` for `J` and `I` and the hypothesis `hIJ`, gives
  `e : L_J ≅ L_I` with `e.hom ≫ leviHom_I ≫ innerIso g = leviHom_J`. Set
  `p' = parabolicHom_I ≫ innerIso g`, `l' = e.hom ≫ leviToParabolic_I` and
  `r' = unipotentToParabolic_I`. These are again a represented parabolic.
  `IsParabolicSubgroup.comp_iso`, `IsRationalLeviSubgroup.iso_comp` and
  `isIso_subgroupMultiplication_iso_comp` transport the hypotheses, and the
  radical hypothesis is unchanged. Moreover `l' ≫ p' = leviHom_J`. So the Levi
  of this data is the scheme `L_J` itself, with the same unramified-character
  coordinates as the target.
- **The representation.** Let `ρ` be the pullback of `σ` along
  `leviRationalPointHomeomorph i ν J : L_J(k) ≃ levi i ν J`. Irreducibility
  and admissibility transfer (`SmoothRep.isIrreducible_pullbackFunctor_obj_iff`,
  `Langlands.isAdmissible_comp_continuousMulEquiv`).
- **Two polynomials.** Apply `exists_generic_leviInduction_isIrreducible` to
  `ρ` with the standard data of `J`, giving `f₁ ≠ 0`, and with the conjugate
  data `(p', l', r')`, giving `f₂ ≠ 0`. The target's polynomial is `f₁ * f₂`,
  which is nonzero.
- **The common locus.** Let `χ` be a literal character in
  `leviUnramifiedPrincipalOpen i ν J hLJ (f₁ * f₂)`, and let
  `ψ = (leviRationalUnramifiedCharacterHomeomorph i ν J).symm χ`. By definition,
  `ψ` lies in the scheme-side principal open of `f₁ * f₂`. Evaluating
  `f₁ * f₂` gives `f₁(ψ) ≠ 0` and `f₂(ψ) ≠ 0`. So both represented inductions
  of `ρ ⊗ ψ` are irreducible.
- **Back to the target's inductions.** The twist `ρ ⊗ ψ` is the pullback of
  `σ ⊗ χ` along the same homeomorphism, so the identity linear map is
  equivariant along `leviRationalPointHomeomorph`, by `rfl`. The comparison
  lemma then transfers irreducibility in two cases:
  - the standard data of `J`, with the decomposition
    `isSemidirectDecomposition_of_standardCocharacterStatement … J`, which
    gives the first conjunct;
  - the conjugate data, with `(… I).conjugateWithLevi g hIJ` and the closed
    radical `isClosed_conjugateSubgroup g (hU I)`. This is the definition of
    `conjugateInductionFunctor`, which gives the second conjunct.

  The point images of `p'` and `r' ≫ p'` are the conjugates
  `conjugateSubgroup g (parabolic i ν I)` and
  `conjugateSubgroup g (unipotent i ν I)`
  (`mem_pointImage_comp_innerIso`, `mem_conjugateSubgroup`).

The main theorem runs with `set_option maxHeartbeats 800000`; its elaboration
uses about 491,000 heartbeats.

## Scope and provenance

This is an internal reduction. Konno, Theorem 4.2, and Renard VI.8.4 enter only
through the two published propositions. They are explicit hypotheses, not
proved here. The common locus intersects the two polynomial loci given by
VI.8.4 for the two actual parabolics, as the task's source route asks. No
coordinate change between `L_I` and `L_J` is needed, because the conjugate
parabolic is presented with Levi source `L_J`. The reduction keeps every
hypothesis of the target, including arbitrary characteristic and the
non-split, non-quasisplit scope. It uses no same-Levi generic isomorphism,
induced K0 Weyl conjugacy or composition-factor identity.
