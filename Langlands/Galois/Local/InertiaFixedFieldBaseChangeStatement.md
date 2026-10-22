# Inertia fixed fields under finite local base change

Author: Worker 60.

`Langlands.PadicField.InertiaFixedFieldBaseChange.{u}` is a proposition
asserting the full maximal-unramified-field identity under finite local
base change. This module states the proposition and does not prove it.

## Exact fields, maps, and quantifiers

For every natural number `p` with `[Fact p.Prime]`, every
`F : PadicField.{u} p`, and every
`D : Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`, put

```text
C   = AlgebraicClosure F.Carrier
C_D = AlgebraicClosure D.field
U_F = IntermediateField.fixedField (F.absoluteInertia F.canonicalTopologicalData)
U_D = IntermediateField.fixedField
        ((D.asPadicField (p := p)).absoluteInertia
          (D.asPadicField (p := p)).canonicalTopologicalData).
```

Here `D.field` is the actual finite intermediate field of `C/F`, with its
inherited field operations and inclusion in `C`. Its `asPadicField` wrapper
uses the composite `Padic p`-algebra through `F.Carrier`. Both inertia
subgroups use the existing canonical topological and valuation data.
The fixed fields are the existing intermediate fixed fields inside the
respective algebraic closures, not separately chosen abstract fields.
The common universe `u` is arbitrary.

The Lean definition installs the literal composite algebra

```text
F.Carrier → D.field → C_D
```

by composing the two actual algebra maps and taking `toAlgebra`. It fixes
the scalar actions on `C_D` to those from these actual algebras and
constructs its `IsScalarTower` instance by reflexivity of the composite
algebra-map equation. These are local definitions, not additional
hypotheses or independently chosen scalar structures.

For every `F.Carrier`-algebra homomorphism `j : C →ₐ[F.Carrier] C_D`, the
sole further premise is

```text
∀ a : D.field, j (a : C) = algebraMap D.field C_D a.
```

Thus the restriction of `j` to the given finite subfield agrees with the
canonical inclusion of that field into its own algebraic closure. The
conclusion is equality in `IntermediateField D.field C_D`:

```text
U_D = IntermediateField.adjoin D.field (j '' (U_F : Set C)).
```

The right side is the smallest subfield of `C_D` containing the actual
image of `D.field` and the transported set `j(U_F)`, hence the actual
compositum `D F_nr` in these compatible closures. The conclusion is field
equality, rather than an abstract isomorphism or a single containment.

The finite extension `D/F` may be non-Galois and may have degree one.
There is no unramifiedness, total ramification, inertia comparison,
fixed-field exhaustion, residue Galois comparison, norm-surjectivity,
or cohomology hypothesis. The proposition applies to every compatible
`j`; it does not construct or assert the existence of such a map.
Constructing compatible algebraic-closure embeddings is separate work.

## Original source and derived formulation

The source is Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay
Greenberg, Springer GTM 67 (1979), registered as
`serre-1979-local-fields`, retained at
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The original passages read for this statement are:

- Chapter III, section 5, Theorems 2–3 and Corollaries 1–3, printed
  pages 54–55 / PDF pages 61–62: finite unramified extensions correspond
  to finite separable residue extensions; their embeddings correspond
  to residue embeddings; their union is the maximal unramified field.
- Chapter V, section 4, Lemma 7 and its proof, printed pages 89–90 /
  PDF pages 96–97: after finite descent from the maximal unramified
  field, the descended field's maximal unramified extension is
  identified with its compositum with the original maximal unramified
  field.

No project errata entry for this source was present when checked.
The universal compatible-closure equality is a derived p-adic
specialization of these passages, not a verbatim theorem in Serre.

The arithmetic translation must first identify `U_F` and `U_D`, defined
using the actual canonical inertia, with the unions of their finite
unramified stages. This includes the comparison of the canonical
valuations and residue maps with Serre's conventions. In the project's
finite-stage convention, unramifiedness is equality of the canonical
absolute ramification indices of the base and the finite extension.
For p-adic fields, finite residue fields are perfect, and the tower
formula for normalized valuations translates this equality into
relative ramification index one. These are proof obligations, not
premises of the present proposition.

Both containments in the displayed field equality require arithmetic:

1. Every finite unramified stage over `F` remains unramified after
   adjoining its image to `D`. Equivalently for containment purposes,
   its specified image lies in a finite unramified stage over `D`.
   Taking the union of these stages puts `j(U_F)` in `U_D`, and
   `IntermediateField.adjoin` then puts the entire compositum in `U_D`.
2. Every finite unramified stage over `D` lies in the compositum with
   some sufficiently large finite unramified stage over `F`. The residue
   field of `D` is a finite extension of that of `F`. If their residue
   degree is `f` and the desired unramified stage over `D` has degree
   `n`, a residue extension of degree `fn` over the residue field of
   `F` contains the required residue extension over `D`. Lifting this
   extension and the compatible residue embeddings by III.5 gives the
   required containment in the specified closure. Passing through all
   finite unramified stages gives the reverse containment.

The degree description explains a mathematical route; no residue-degree
formula, lifting theorem, or either containment is proved by this module.
The passage from the residue-field construction to these exact images,
using the compatibility of `j` on `D`, remains part of the proof.

## Relation to neighboring statements and finite descent

Worker 154's published
`Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeStageExistence`
asserts containment of a specified finite unramified Galois source stage
in some finite unramified Galois target stage. Its compatible closure
map is supplied as an algebra structure and scalar tower. Applying that
statement here requires installing the algebra structure from `j` and
checking its scalar compatibility. Together with finite unramified
exhaustion of the actual inertia fixed fields, it supplies the forward
containment described above. It does not supply the reverse containment
or the full equality asserted here. That statement is not assumed in
the Lean target.

Finite unramified exhaustion of the actual inertia fixed field and
generic descent of finite extensions from a directed union are separate
obligations. After generic descent expresses a finite extension of
`F_nr` as `D F_nr`, the present identity identifies that compositum with
`D_nr`; this is the local-field identification used in Serre V.4
Lemma 7. If descent initially yields an abstract finite field, its
realization in the specified closure and the compatible embeddings must
also be supplied separately.

This proposition contains no generic descent theorem, simultaneous
finite-tower construction, or norm equation. Those results, the
downstream norm transport, and the proof of this full field comparison
remain separate work.
