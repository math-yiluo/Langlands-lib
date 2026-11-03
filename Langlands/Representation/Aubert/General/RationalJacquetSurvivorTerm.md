# The actual standard term in the rational Jacquet survivor

This internal unit defines `standardConjugatedJacquetTerm` as the actual
normalized induction inside a target standard Levi, after inverse-conjugation
pullback on an actual fine Levi, after ambient standard normalized Jacquet
restriction. All three maps act on exact finite-length Grothendieck groups,
with the original short exact sequence relations.

The law `standardConjugatedJacquetTerm_eq_transported` compares this
term with the already defined `transportedLeviJacquetTerm`. The source and
target coarse standard Levis, and one fine subset inside each, are arbitrary.
Coarse and fine ambient Levi membership under the specified group element,
and parabolic and unipotent membership restricted to the target coarse Levi,
are explicit geometric inputs. The field and carrier universes are independent,
with carrier universe `max (u + 1) v`. The ambient group is locally compact and
nonarchimedean in the canonical rational-point topology. Closed radicals,
closed standard Levis, the standard-cocharacter and Levi-intersection inputs,
and exact finite-length preservation for ambient and restricted functors are
explicit.

Three named maps keep the actual standard operations explicit:
`standardLeviInductionK0` is induction from the ambient fine Levi inside a
coarse Levi; `standardLeviJacquetK0` is the corresponding restriction to the
ambient fine Levi; and `standardAmbientJacquetK0` is ambient standard Jacquet
restriction. These are definitions of the existing actual maps, with the
canonical subgroup-copy identifications retained.

The intermediate law `standardLeviInductionK0_transport` uses
`LeviConjugation.inductionMap_transport` to move
fine induction past the specified conjugation. The law
`standardLeviJacquetK0_comp_ambient` uses
`standardJacquetK0_stages_of_modulus` on the source to factor the fine
ambient Jacquet map. That step keeps the compact-limit hypothesis and the
actual positive Haar-modulus product equality explicit.
The law `standardLeviInductionK0_comp_jacquet` specializes
`LeviConjugation.inductionMap_comp_jacquetMap` and cancels the two canonical
subgroup-copy pullbacks. A private elementary linear-map composition lemma
combines these three checked identities by associativity. This gives precisely the literal
restricted-Levi alternating term in `transportedLeviJacquetTerm`.

Provenance is internal, through the three imported modules. No subgroup
membership, positive Haar factorization, geometric expansion, or longest
representative assertion is proved here. The final associated-subset
specialization must supply these inputs from actual geometry. No
representation comparison or desired K0 equation is assumed as a premise.
The whole rational Aubert Jacquet compatibility statement remains a separate
obligation.
