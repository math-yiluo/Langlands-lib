# Affine quotients of finite free scheme actions

For a finite group `G` acting freely on an affine scheme `X`, this internal
helper constructs an affine quotient with a finite étale surjective quotient
map. The action, scheme, and all test schemes are in the same arbitrary universe
`u`. The action convention and freeness hypothesis are those of
`FiniteFreeSchemeAction` in the preceding relation module.

`source_isFinite` proves that the fold from the coproduct of copies of `X`
is finite. The coproduct is identified with the spectrum of the finite
product of copies of the coordinate ring of `X`. The fold corresponds to the
diagonal ring homomorphism into that product. The product is a finite module,
so the induced spectrum morphism is finite. The identification is verified
on each coproduct summand using the evaluation homomorphism.
`target_isFinite` expresses the other projection as the coproduct of the action
automorphisms followed by the fold. Both projections are already étale by
the relation module, hence flat and locally of finite presentation.

`AffineQuotient` records the quotient scheme, its affineness, the quotient map,
the relation equation, finiteness, étaleness, surjectivity, the kernel-pair
square, and the coequalizer property. These properties refer to the actual
scheme morphisms.

`nonempty_affineQuotient` applies the published
`FiniteLocallyFreeQuotient.existsAffineQuotient`. Joint monicity follows
from the actual monomorphism proved in the relation module, since an affine
scheme is separated. The equivalence relation on every scheme-valued point set
uses that module's reflexivity, symmetry, and transitivity witnesses.
The theorem gives an affine quotient with a finite flat surjective map and
the stated kernel pair and coequalizer. Étaleness descends from the étale
relation projection along the finite flat surjective quotient map, using
Mathlib's fpqc descent theorem. `quotient` chooses this data.

For any such quotient, `invariant` says that its map is unchanged by each
action automorphism. `equalizes` checks the relation equation for an invariant
morphism by restriction to each summand. `desc` applies the coequalizer
universal property to obtain its descended map; `map_desc` gives the
factorization equation, and `hom_ext` gives uniqueness.

The construction is derived from the free symmetric action used in the first
proof paragraph of Stacks Lemma 68.8.3 (Tag 0BBN), registered source
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
The quotient existence input is the published proof of Stacks Proposition
39.23.9 (Tag 03BM), registered source
`stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`,
`03BM.txt`, statement and proof. The present helper supplies the group-action
specialization and finite-coproduct calculation; it imports that quotient
proof by Lean name. It does not prove the tuple stratification or the
Noetherian first-level theorem.
