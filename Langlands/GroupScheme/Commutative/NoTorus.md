# Characters and unipotence of commutative groups without cocharacters

Work over an arbitrary field `k : Type u`. The field and all group schemes
remain in the arbitrary universe `u`.

## Surjectivity of a nonzero character

`rationalCharacters.surjective_of_ne_zero` states that a nonzero rational
character of a smooth connected affine group scheme `H` over `Spec k` is
surjective as a morphism of underlying schemes. The group `H` need not be
commutative. Here a rational character is an actual group-scheme morphism to
`Gm`, with the additive wrapper used by `rationalCharacters`.

The proof uses the existing split-torus image factorization
`IsSplitTorus.exists_fppfQuotient_factor`: the character factors as an fppf
quotient `q : H ⟶ D` followed by an inclusion `m : D ⟶ Gm`, with `D` a
split torus. If `m` were the zero character, the original character would
vanish. The published `RelativeRoot.characterFpqc` therefore proves that
`m` is surjective. The fppf quotient is surjective as well, so their
composite is surjective.

## An actual detecting cocharacter

For a smooth connected affine commutative group scheme `Z`, the definition
`CommutativeNoTorus.detectingCocharacter Z χ hχ` chooses an actual
homomorphism `Gm ⟶ Z.toGrp` over the original field for each nonzero
rational character `χ`.

`CommutativeNoTorus.characterRestrict_detectingCocharacter_ne_zero`
proves that restricting `χ` along this chosen map is nonzero. The
construction applies the published
`CentralSurjectionImage.exists_gm_characterRestrict_ne_zero_of_surjective`
to the surjectivity theorem above; the detecting property is the
specification of that choice. It does not choose a map merely on rational
points or after a field extension.

Consequently, `CommutativeNoTorus.character_eq_zero_of_gm_hom_eq_zero`
proves that every rational character vanishes when every actual
homomorphism `Gm ⟶ Z.toGrp` is zero. Otherwise the detecting cocharacter
would be zero, forcing its character restriction to vanish.

## The algebraically closed unipotence consequence

`CommutativeNoTorus.isUnipotent_of_gm_hom_eq_zero` assumes additionally
that `k` is algebraically closed. Commutativity gives solvability, and
`IsSolvableGroupScheme.isUnipotent_of_characters_eq_zero` from
`Absolute.CharacterUnipotence` applies to the character vanishing just
proved. Thus `Z.toGrp` is unipotent.

`CommutativeNoTorus.isUnipotent_of_no_torus` gives the same consequence
from the hypothesis that every homomorphism from any `k`-torus to `Z`
has bottom all-test range. It specializes the hypothesis to `Gm` and uses
`SubgroupFunctor.eq_zero_of_range_eq_bot` to identify each such map with
zero. Only this elementary range lemma is used from
`Torus.NoTorusBaseChangeReduction`; no no-torus base-change reduction is
assumed.

## Provenance and scope

This is an internal construction and deduction from the named published
factorization, character-surjectivity, cocharacter-detection, character
criterion and range interfaces. The proof above describes its implemented
route, rather than supplying a new external structural input.

The detecting construction and character vanishing work over arbitrary
fields, including finite and imperfect fields. The unipotence consequences
here require an algebraically closed field and a commutative group.
The exact arbitrary-field, possibly noncommutative
`NoTorusUnipotentStatement` remains a separate proof obligation.
