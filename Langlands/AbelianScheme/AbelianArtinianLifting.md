# Abelian-scheme lifts across elementary local Artinian extensions

Module `Langlands.AbelianScheme.AbelianArtinianLifting`.

`abelianArtinianLifting` proves `AbelianArtinianLiftingStatement`. For a
surjection `φ : R' →+* R` of local Artinian rings with `R'` a `ℚ`-algebra and
`maximalIdeal R' * ker φ = 0`, it gives an abelian scheme `A` over `Spec R'`
and an isomorphism `(AbelianScheme.baseChange t).obj A ≅ B` of abelian schemes
over `Spec R` for every abelian scheme `B` over `Spec R`. Here
`t := Spec.map (CommRingCat.ofHom φ)`. The residue field can be any field of
characteristic zero.

## Proof

`abelianArtinianLifting_of_smoothLifting` combines two theorems.

1. `abelianSmoothArtinianLifting` gives a smooth proper `p : X ⟶ Spec R'`
   with section `s` and a pointed isomorphism `e₀ : B.X.left ≅ pullback p t`
   over `Spec R`.
2. `pointedAbelianArtinianLifting` lifts the group law to the pointed scheme.
   It gives `A` over `Spec R'` with an isomorphism `e : A.X.left ≅ X` over
   `Spec R'` carrying the identity section of `A` to `s`.

The reduction lemma uses `pullback.map` to base change `e` to `Spec R`
and composes with `e₀.inv`. The second pullback projections show that the
composite is over `Spec R`. In `pullback p t`, the images of the unit sections
under the base change of `e` and under `e₀.hom` agree on both projections.
Their first projection is `t ≫ s` and their second is `𝟙 (Spec R)`.
The composite is therefore pointed. `isoOfPointedIso` applies
`pointedMorphismRigidity` over `Spec R` to make it an isomorphism of abelian
schemes on the actual pullback.

## Provenance

Lan's *Arithmetic compactifications of PEL-type Shimura varieties*, Harvard thesis
revised 14 March 2021, proves scheme lifting in Proposition 2.2.4.1
(printed pp. 152–154, PDF pp. 180–182) and passes from a pointed scheme lift to
an abelian scheme in Propositions 2.2.2.3 and 2.2.2.5
(printed pp. 144–145, PDF pp. 172–173). The group-law input implements the
construction of Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*,
3rd ed., Proposition 6.15 (printed pp. 124–126, PDF pp. 137–139).
