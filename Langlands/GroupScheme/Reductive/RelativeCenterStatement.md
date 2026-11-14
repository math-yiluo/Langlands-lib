# Statement: the relative reductive centre

Worker 673.

`Langlands.GroupScheme.ReductiveRelativeCenterStatement.{u}` is a
statement-only definition returning `Prop`. It has no proof in this module.

For every scheme `S` and every reductive `S`-group `G`, it asserts the existence
of a group scheme `Z` and homomorphism `z : Z ⟶ G` with three properties:

- `IsSchemeTheoreticCenter z`: the underlying scheme map is a closed immersion
  and its range on every test scheme is the full centre functor of `G`.
- `RelativeMultiplicativeType.IsMultiplicativeType Z`: an fppf cover of `S`
  makes `Z` diagonalizable with finitely generated abelian character groups.
- For every scheme map `b : S' ⟶ S`, the pulled-back homomorphism represents
  the full scheme-theoretic centre of the pulled-back group.

`IsReductive` means smooth and affine over `S`, with connected reductive
geometric fibres. The predicates and pullback are the published definitions
from `Reductive.Basic`, `Reductive.Semisimple`, and
`Torus.RelativeMultiplicativeType`. In particular, the centre includes its
nonreduced structure and need not be smooth or a torus.

The base is arbitrary, including the empty scheme, and every object and base
change lies in the indicated universe `u`. No Noetherian, connectedness,
splitness or local-ring condition is imposed on `S`.

The source is Brian Conrad, *Reductive group schemes* (2014), source ID
`conrad-2014-reductive-group-schemes`, retained as
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
PDF and printed page numbers agree. Theorem 3.3.4 and its proof, pp.98–99,
give a reductive centre and identify it with the full scheme-theoretic
centre. Definition 3.3.3, p.98, includes multiplicative type, in the sense of
Definition B.1.1, p.280. The proof of Theorem 3.3.4 begins by using arbitrary
base-change compatibility of the reductive centre; the construction and
all-test identification on p.99 give the asserted centre property after
base change.

This formulation records only the centre, its multiplicative type and that
compatibility. It omits the source's additional identification with the kernel
of the action on the maximal-torus functor. It is a prerequisite for the
maximal central torus construction in Corollary 5.3.3, p.164, rather than a
statement of that corollary.
