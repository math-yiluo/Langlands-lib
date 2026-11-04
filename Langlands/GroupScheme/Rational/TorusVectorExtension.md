# Group sections of arbitrary-torus extensions by linear vector groups

`IsTorus.extensionSection` constructs an actual homomorphism of group schemes
`H ⟶ E` splitting `q : E ⟶ H`, when `H` is an arbitrary torus and the supplied
kernel has natural finite vector coordinates in which conjugation by `E` is
linear. An original section of `q` as a morphism of schemes is an explicit input.

Let `k : Type u` be any field. The hypotheses are:

- `V`, `E`, and `H` are group schemes over `Spec k`, with `V` and `H` affine
  over the field (`IsAffineHom V.X.hom` and `IsAffineHom H.X.hom`).
- `n : V ⟶ E` is a monomorphism on underlying relative schemes.
- Its actual subgroup-functor range is the full kernel of `q` on every test
  scheme: `range n = range (kernelι q)`.
- `s : H.X ⟶ E.X` is a morphism of schemes over `Spec k` and
  `s ≫ q.hom.hom = 𝟙 H.X`.
- For a natural number `d`, `e T` identifies the group of `T`-points of `V`
  with the additive vectors `Fin d → Γ(T.left, ⊤)`, written multiplicatively.
  `he : IsLinearVectorCoordinates (VectorExtensionDescent.action n q hn) e`
  asserts both naturality under precomposition and scalar-linearity of actual
  ambient conjugation on every test scheme.
- `hH : IsTorus H` is the unchanged torus predicate. No splitness over `k`
  is assumed.

`IsTorus.exists_extensionSection` proves
`∃ σ : H ⟶ E, σ ≫ q = 𝟙 H`. The definition `IsTorus.extensionSection`
chooses such a homomorphism, and `IsTorus.extensionSection_comp` proves its
quotient composite is exactly the identity.

The proof chooses the field extension already provided by `IsTorus H` and
pulls back `n`, `q`, and `s`. The published
`VectorExtensionDescent.range_baseChange_kernel` preserves the full kernel
presentation; this also supplies its normalization by the extension group.
`vectorBaseChangeCoordinates` supplies the same finite vector coordinates after
extension. The helper `splitTorus.conj_baseChange` proves that actual normalized
conjugation commutes with field extension, by applying the pullback point
equivalence, composing with the monic kernel inclusion, and comparing the two
ambient conjugation formulas. Therefore `IsLinearVectorCoordinates.baseChange`
applies to the conjugation action required by the split-torus theorem.

`IsSplitTorus.exists_extensionSection` then constructs a group section over the
splitting field. Finally `VectorExtensionDescent.extensionSectionOfBaseChange`
uses the original scheme section and the original linear vector coordinates to
construct a group section over `k`; its companion composite identity gives the
claimed splitting. This coefficient-contraction construction does not assert
that the resulting section base changes to the particular splitting-field
section.

The provenance is an internal deduction from the imported split-torus extension,
actual base-change, vector-coordinate and coefficient-contraction constructions.
There is no assumption on the characteristic, perfection or cardinality of the
field, nor on the finiteness or separability of the chosen splitting extension.
Existence of the original scheme section and existence of the linear vector
coordinates remain explicit inputs. This module supplies a focused extension
splitting step; it does not establish the full solvable maximal-torus conjugacy
statement.
