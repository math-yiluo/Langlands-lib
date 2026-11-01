# The ordinary relative Picard presheaf

For any scheme morphism `f : X → S`, `RelativePicard.presheaf f` constructs
the functor `(Over S)ᵒᵖ ⥤ AddCommGrpCat.{u+1}` whose value at `T → S` is
the actual Picard group of `T ×_S X`. Its restriction along `h : T → U`
is the homomorphism induced by the actual module-sheaf pullback along the
canonical map `T ×_S X → U ×_S X`. There are no compactness, separation,
section, or representability hypotheses.

The implementation composes the opposite of the published `relativeSpace f`
with the published `Group.functor`. Thus both the abelian group laws and
the identity and composition laws are inherited from proved constructions.
`RelativePicard.classPresheaf f` forgets only the abelian group structure,
giving the corresponding functor to `Type (u+1)`. The object and map formulas
for both functors are proved by reflexivity.

`classOf f T L` is the ordinary Picard class of an actual locally free
rank-one module sheaf on the fibre product. `classOf_eq_iff_iso` identifies
equality of these classes with existence of an actual line-bundle
isomorphism. `exists_representative` provides such a line bundle for every
section. `map_classOf` proves that the restriction is the class of actual
line-bundle pullback. The trivial, tensor and inverse class formulas
specialize the published ordinary Picard results. The tensor formula uses
the proved canonical pullback-tensor preservation theorem, without an
additional preservation hypothesis.

The precise original reference is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, Chapter VI §1, printed p.87
(PDF p.91), the displayed definition of `P_{X/S}` immediately before
Definition (6.1). The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Worker 144 read that page and the following page directly. The functor
composition and class formulas are internal packaging of this definition
using the published ordinary Picard group.

The factor order is `T ×_S X`; `relativeSpaceSymmetry` supplies the canonical
isomorphism to the source's `X ×_S T`. The class universe remains `u+1`,
as for the actual module-sheaf classes in `Group`. No smallness reduction
is claimed. Sheafification, comparison with rigidified classes and
representability are separate constructions.
