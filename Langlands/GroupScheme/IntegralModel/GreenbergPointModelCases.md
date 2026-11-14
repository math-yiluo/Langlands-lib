# Characteristic cases and the first Greenberg level

This derived module factors the exact point-model statement of
`GreenbergPointModel.md` into two exhaustive characteristic cases and proves
its level-one instance. Its universe `u` is arbitrary. The original statement
and all of its imports are unchanged.

`HasGreenbergPointModel R n X` is exactly the existential conclusion of
`GreenbergPointModelStatement` for fixed `R`, `n` and `X`. It includes the
smooth affine target model, its multiplicative point equivalence, all smooth
affine source groups and homomorphisms, the commuting square on points and
preservation of geometric connectedness. The target model and its point
equivalence are chosen before the source and homomorphism.

`EqualCharacteristicGreenbergPointModelStatement` adds
`ringChar R = ringChar (IsLocalRing.ResidueField R)` to the hypotheses of
the original statement. `MixedCharacteristicGreenbergPointModelStatement`
adds its negation. Both retain a DVR in `Type u`, algebraically closed
residue field, every positive level and every smooth affine target and source.
`GreenbergPointModelCasesStatement` is the conjunction of those two
case statements. The terms "equal" and "mixed" refer to the characteristics of the DVR and
its residue field. Neither case statement is proved here.

`greenbergPointModel_of_characteristicCases` proves the full original
statement from proofs of these two case statements. It decides the indicated
characteristic equality and applies the corresponding premise. The theorem
`greenbergPointModel_iff_characteristicCases` also proves the converse by
restricting the original statement to either extra hypothesis. This is a
logical decomposition, not a construction of the Greenberg functor or a proof
of either all-level case.

`hasGreenbergPointModel_one` proves the fixed-input conclusion at level one
for every commutative local ring and smooth affine group over it. Its target
model is the ordinary special fibre. The comparison
`greenbergLevelOnePointsEquiv` uses the existing congruence/residue test
isomorphism and the group-valued functor of points. Its naturality lemma is
`baseChangePointRestriction_naturality` applied to that same isomorphism.
Affineness, smoothness and geometric connectedness of the chosen models follow
by base change. This proof does not require a DVR or an algebraically closed
residue field, and covers all characteristics.

The source context is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`,
the paragraph before Theorem A.4.19 and the theorem's proof, printed
pp.628–629 / PDF pp.659–660. It uses Weil restriction in equal
characteristic and the Greenberg construction in mixed characteristic, and
identifies the first level with the special fibre. The registered
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.49, adds perfectness of the residue field; the case statements retain
the original algebraically closed residue field. The predicates and logical
decomposition are internal organization of that published target. The
level-one theorem implements the canonical quotient comparison directly.
