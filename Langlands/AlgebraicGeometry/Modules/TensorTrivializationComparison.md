# Comparing local tensor trivializations

This derived unit compares the actual sheaf isomorphisms
`tensorRestrictionTrivialization M N U t` as the line trivialization `t`
varies on one fixed open `U` of an arbitrary scheme `S`.

The comparison scalar `tensorTrivializationScalar t s` is the unit of
`Γ(U.toScheme, ⊤)` associated to the automorphism `t.symm ≪≫ s` of the
structure module. The identity, inverse and composition formulas express
the corresponding formulas for these structure-module automorphisms.
No rank, quasi-coherence or global triviality hypothesis is needed: the two
local trivializations are explicit inputs.

The contraction associated to `s` is the contraction associated to `t`
followed by multiplication by this scalar. Equivalently, expansion with
`t` followed by contraction with `s` is that scalar endomorphism of
`M.restrict U.ι`. The last lemma evaluates this equality on every open
`V` of `U.toScheme`; the multiplier there is the restriction of the
specified global unit.

The proof reuses the published
`SerreVanishing.tensorMap_id_unitEnd`, which describes the right unitor
after tensoring with an endomorphism of the structure module. Functoriality
of the sheaf tensor and `t.hom ≫ t.inv = 𝟙` reduce the comparison to that
lemma. The canonical restriction-tensor comparison is common to both
contractions. Cancelling the contraction isomorphism gives the second
morphism equality, and evaluating it gives the section formula.

This is internal infrastructure derived from the published sheaf tensor,
its unitors, the restriction comparison and the structure-module unit
correspondence. It does not establish compatibility between different
trivializing opens, equality of projective cocycles, or representability
of the ordinary full-level moduli functor. Those remain separate proof
obligations.
