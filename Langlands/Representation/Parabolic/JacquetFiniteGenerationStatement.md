# Finite generation of normalized standard Jacquet modules

Author: Worker 186.

The closed proposition
`Langlands.Parabolic.NormalizedJacquetFiniteGenerationStatement.{uF,uV}`
states that the actual normalized standard Jacquet representation of a smooth,
finitely generated complex representation of `GL_n(F)` is finitely generated
over the complex group algebra of its block Levi. This pair defines a
proposition and supplies no proof of it.

## Exact scope

The proposition quantifies a prime `p` through `[Fact p.Prime]`, an actual finite
extension `F : PadicField.{uF} p`, a compatible realization
`T : F.TopologicalData`, every natural rank `n`, and every
`B : GeneralLinear.BlockShape n`. It installs `T.topology` before expressing
smoothness. The carrier `V : Type uV` has only an additive commutative group
structure and a complex module structure. The universes `uF` and `uV` are
independent.

For each actual representation
`ρ : Representation ℂ (GeneralLinear n F.Carrier) V`, the hypotheses are
`IsSmooth ρ` and
`Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) ρ.asModule`.
The conclusion is
`Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier))
  (T.normalizedJacquet B ρ).asModule`.
Here `Module.Finite` means finite generation as a module over the specified
group algebra: finitely many vectors have group translates whose complex
linear span is the whole representation. It does not mean that `V` is
finite-dimensional over `ℂ`.

There is no admissibility, irreducibility, finite-length, central-character,
positive-rank, or nonzero-carrier hypothesis. In particular, the zero
representation is allowed. Finite generation after restriction to the
parabolic is not supplied as an assumption.

## Actual quotient and normalization

The imported module `Langlands.Representation.Jacquet.Parabolic` constructs
`B.JacquetModule ρ` by restricting `ρ` to the actual upper block parabolic
`P = B.parabolic F.Carrier` and quotienting by the span of
`ρ(u)v - v` for its actual unipotent radical `N`. The target representation is
the published `T.normalizedJacquet B ρ`, on this quotient, with action

```text
m · [v] = δ_P(m)^(-1/2) [ρ(B.leviEmbedding F.Carrier m) v].
```

The full explicit block character is `T.leviModulus B`; equivalently the
normalizing scalar is the inverse of `T.leviHalfModulus B`, as expressed by
`PadicField.TopologicalData.normalizedJacquet_mk_eq_inv_halfModulus`.
The parabolic is upper, and the half-modulus has the inverse sign used for
Jacquet modules.

## Source and derived specialization

The original read for this pair is W. Casselman, *Introduction to the theory
of admissible representations of p-adic reductive groups*, draft of 1 May
1995, Theorem 3.3.1 and its finite-generation proof, printed/PDF page 35.
The quotient and its unnormalized action were also read in §3.2,
Proposition 3.2.1 and the subsequent construction, printed/PDF pages 33–34.
The theorem and finite-generation proof on page 35 were checked in the page
image as well as the extracted text.

Registered source: `casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The retained file is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
No source-specific errata file for this source was found in the project
notes, the current Library notes, or the literature collection.

Casselman's theorem treats smooth representations of reductive p-adic groups
and their unnormalized Jacquet modules, and gives separate finite-generation
and admissibility assertions. This proposition takes only the
finite-generation assertion, specializes to `GL_n` and standard block
parabolics, and then uses the published normalized action.

For the source's finite-generation argument, choose a finite generating set
`X`, a compact open subgroup `K` fixing every element of `X`, and a finite
set `Γ` such that `P Γ K = G`. The images of the finitely many vectors
`ρ(γ)x` generate `V_N` as an `M`-representation: the `K` factor fixes `X`,
and the unipotent factor acts trivially on the quotient. This argument uses
smoothness and finite generation, independently of the admissibility part
of Theorem 3.3.1.

The normalization step is a derived elementary observation, not a verbatim
assertion of that theorem. Multiplying each Levi action operator by a
nonzero complex character value leaves the complex span of the translates
of any generating set unchanged. The inverse half-modulus takes values in
`ℂˣ`, so finite generation is preserved by this twist. This pair does not
formalize that argument.

The inclusion of rank zero is a further elementary extension under the
Library conventions. An ordered positive block shape of total size zero has
no blocks; both `GL_0(F)` and its block Levi are trivial groups. The radical
is trivial and the empty-product half-modulus is one. Thus the source and
target actions identify with the same trivial action on the quotient
canonically identified with `V`, and the asserted implication preserves
finite generation. No positive-rank condition is needed.

## Proof boundary

The only new Lean declaration is this closed `Prop`-valued definition.
Smoothness of the normalized quotient is already proved in the imported
construction and is not repeated as a conclusion here. A separate proof
must establish the full finite-generation proposition. This pair neither
assumes that proposition nor uses induction finite generation or the
downstream admissible finite-length theorem.
