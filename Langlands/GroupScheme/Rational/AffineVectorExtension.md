# Sections of affine extensions by vector groups

`RelativeRoot.IsVectorGroupOfDimension.exists_quotientSection` proves that an
actual quotient `q : E ⟶ H` has a section as a morphism of schemes over the
original field, under the following hypotheses:

- `k : Type u` is any field, and `E`, `V`, and `H` are group schemes over `Spec k`.
- `E` and `H` are affine over the field.
- `n : V ⟶ E` is a monomorphism on underlying relative schemes, with
  `range n = range (kernelι q)` on every scheme test.
- The underlying scheme morphism of `q` is flat and surjective.
- `V` is a vector group of some finite dimension `d`, in the existing natural,
  all-test coordinate predicate `IsVectorGroupOfDimension V d`.

The conclusion is `∃ s : H.X ⟶ E.X, s ≫ q.hom.hom = 𝟙 H.X`.
The section is a regular morphism over `Spec k`; this first theorem asserts no
multiplicativity of that section.

The proof derives smoothness, affineness and split unipotence of `V` from its
natural vector coordinates. Affineness of `E` makes its structure morphism
quasi-compact, and the quotient morphism is consequently quasi-compact by the
composition criterion. The full-kernel equality gives the exact fiber relation
`q(g) = q(h)` if and only if `g⁻¹ h` lies in `range n` on every test. The
published `HomogeneousQuotient.affine_section_of_split_unipotent_torsors`, applied
to the unconditional `splitUnipotentAffineTorsorStatement`, then supplies the
section.

`IsTorus.exists_affine_extensionSection` adds `IsTorus H` and specified natural
finite vector coordinates `e` satisfying
`IsLinearVectorCoordinates (VectorExtensionDescent.action n q hn) e`.
The action here is actual ambient conjugation by `E` on its monomorphic full
kernel. The theorem constructs a homomorphism of group schemes
`σ : H ⟶ E` with `σ ≫ q = 𝟙 H`. It first obtains the scheme section above,
then uses `IsTorus.exists_extensionSection` for arbitrary tori.
`IsTorus.affineExtensionSection` chooses such a homomorphism and
`IsTorus.affineExtensionSection_comp` proves its exact quotient identity.

The provenance is an internal deduction from the imported vector-group,
affine torsor and arbitrary-torus extension constructions. No characteristic,
perfection, cardinality or splitness restriction is imposed. The original
scheme section is now constructed from the flat-surjective affine quotient;
existence of scalar-linear coordinates for the ambient conjugation remains an
explicit hypothesis. Constructing those coordinates from a torus quotient and
assembling maximal-torus conjugacy are further obligations of the host task.
