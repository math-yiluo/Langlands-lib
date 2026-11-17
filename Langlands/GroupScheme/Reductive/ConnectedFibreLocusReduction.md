# Reduction of the closedness of the connected-fibre locus to discrete valuation rings

This module proves that the local statement over discrete valuation rings,
`Langlands.GroupScheme.ConnectedFibreLocus.DvrCoreStatement`, implies Conrad's
Proposition 3.1.12 (*Reductive group schemes*, 2014), the Library statement
`Langlands.GroupScheme.ConnectedFibreLocusClosedStatement`. All declarations are in the
namespace `Langlands.GroupScheme.ConnectedFibreLocus`. The module does not prove
`DvrCoreStatement`; the final theorem takes it as a hypothesis.

## Route

Let `G` be a smooth affine group over a scheme `S` all of whose geometric fibres have
reductive identity components, and let `Y = connectedFibreLocus G` be the set of points
with connected fibre. Conrad's proof treats the closed fibre over a discrete valuation ring
and reduces the general case to it. The Lean proof makes this reduction explicit as
follows.

1. `Y` is locally constructible over an arbitrary base (`isLocallyConstructible_connectedFibreLocus`
   in `ConnectedFibreLocusFibres`, from the Library's local constructibility of the
   geometrically connected fibre locus).
2. `Y` is stable under specialization. Over an affine open `Spec A`, the group descends to a
   smooth affine group `G₀` over a finitely generated `ℤ`-algebra `R₀`
   (`exists_finiteType_model`), and `Y` is the preimage of the locus of `G₀`
   (`connectedFibreLocus_baseChange`). A specialization `t ⤳ s` in `Spec A` maps to a
   specialization in the Noetherian scheme `Spec R₀`. If the images differ, the Library's
   `nonempty_dvrSpecialization` realizes it by a morphism `Spec R → Spec R₀` from a discrete
   valuation ring sending the generic point to the image of `t` and the closed point to the image of `s`.
   `DvrCoreStatement` then applies to the pulled-back group over `R`.
3. A locally constructible set stable under specialization is closed.

The second clause of the target statement (connected generic fibre implies all fibres
connected) follows from closedness, since every point is a specialization of a generic
point.

## `isClosed_of_isLocallyConstructible_of_stableUnderSpecialization`

A locally constructible subset `Y` of a scheme `S` that is stable under specialization is
closed. *Proof.* Closedness is local. On an affine open `U` with `Spec Γ(U) ≅ U`, the
preimage of `Y` is constructible in a prime spectrum and stable under specialization, hence
closed (Mathlib's `PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible`).
The image of its complement under the open embedding `Spec Γ(U) → S` is an open
neighbourhood of any given point outside `Y` that is disjoint from `Y`.

## `connectedFibreLocus_of_iso`, `identityComponentReductiveLocus_of_iso`

For isomorphic group schemes `G ≅ H` over the same base, the connected-fibre loci agree,
and, for smooth affine groups, the reductive identity-component loci
(`identityComponentReductiveLocus`) agree. *Proof.* Base change the isomorphism to the
residue fields (respectively the geometric points) and, for the second locus, apply the
identity-component functor (`IdentityComponent.mapIso`) and `IsConnectedReductive.of_iso`.

## `dvrSpecialization_map_of_eq_bot`, `dvrSpecialization_map_of_eq_maximalIdeal`

For a Library `DvrSpecialization X η s` (a morphism `Spec R → X` from a discrete valuation
ring with generic point mapping to `η` and closed point mapping to `s`), a point of
`Spec R` with zero prime ideal maps to `η`, and a point with maximal prime ideal maps to
`s`. *Proof.* Such a point equals the generic (respectively closed) point of `Spec R`.

## `mem_connectedFibreLocus_of_dvrSpecialization`

Assume `DvrCoreStatement`. Let `H` be a smooth affine group over `X` and
`d : DvrSpecialization X η s`. If `η` and `s` lie in `identityComponentReductiveLocus H` and
`η ∈ connectedFibreLocus H`, then `s ∈ connectedFibreLocus H`. *Proof.* Let `R` be the
discrete valuation ring of `d`, `K` its fraction field and `G'` the pullback of `H` to
`Spec R`. Every prime of `R` is zero or maximal, so every point of `Spec R` maps to `η` or
`s`, and `identityComponentReductiveLocus G' = univ` by the Library's base-change formula
`identityComponentReductiveLocus_baseChange`. The point `Spec K → Spec R` maps to the
generic point, hence to `η` in `X`. The point `Spec (R/𝔪) → Spec R` maps to the closed point, hence to `s`.
By `connectedSpace_fieldPoint_iff` (from `ConnectedFibreLocusFibres`), `G'_K` is connected
because `η ∈ connectedFibreLocus H`. `DvrCoreStatement` gives that `G'_{R/𝔪}` is connected,
and `connectedSpace_fieldPoint_iff` again gives `s ∈ connectedFibreLocus H`.

## `mem_connectedFibreLocus_of_specializes_affine`

Assume `DvrCoreStatement`. Let `A` be a commutative ring and `G` a smooth affine group over
`Spec A` with `identityComponentReductiveLocus G = univ`. If `t ⤳ s` in `Spec A` and
`t ∈ connectedFibreLocus G`, then `s ∈ connectedFibreLocus G`. *Proof.* Take a finite-type
model `G ≅ (G₀)_A` over `R₀ → A` (`exists_finiteType_model`). `R₀` is Noetherian, being of
finite type over `ℤ`. Let `p : Spec A → Spec R₀`. The reductive locus of `G₀` contains the
image of `p` (base change and isomorphism invariance), and `x ∈ connectedFibreLocus G` if
and only if `p x ∈ connectedFibreLocus G₀`. If `p t = p s` there is nothing to prove.
Otherwise `p t ⤳ p s` is realized by a discrete-valuation-ring point
(`nonempty_dvrSpecialization`), and `mem_connectedFibreLocus_of_dvrSpecialization`
applies.

## `stableUnderSpecialization_connectedFibreLocus`

Assume `DvrCoreStatement`. For a smooth affine group `G` over any scheme `S` with
`identityComponentReductiveLocus G = univ`, the connected-fibre locus is stable under
specialization. *Proof.* Given `t ⤳ s`, choose an affine open `U ∋ s`, which also contains
`t`. Pull `G` back along `Spec Γ(U) ≅ U → S`. The pulled-back group still has all identity
components reductive, its connected-fibre locus is the preimage of that of `G`, and the
specialization lifts to `Spec Γ(U)` because `U → S` is an open embedding. Conclude with
`mem_connectedFibreLocus_of_specializes_affine`.

## `connectedFibreLocusClosed_of_dvrCore`

`DvrCoreStatement.{u} → ConnectedFibreLocusClosedStatement.{u}`. *Proof.* The set
`connectedFibreLocus G` is definitionally the set in the target statement. It is locally
constructible (`isLocallyConstructible_connectedFibreLocus`) and stable under
specialization (previous lemma), hence closed. If a generic point `η` (a point specializing
to every point) lies in this closed set, every point does.
