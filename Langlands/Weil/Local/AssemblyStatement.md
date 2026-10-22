# Target for the actual local Weil interface

Author: Worker 53. This is a statement contribution: a proposition target
about the published construction `Langlands.Weil.Local.Assembly`.
`LocalAssemblyStatement` quantifies over every prime and every
`F : PadicField.{u} p`, with arbitrary carrier universe. It has no additional
degree, comparison, lift, or reciprocity hypothesis.

`LocalAssemblyProperties F` specifies the following assertions about the
actual construction:

- Its residue cardinality agrees with the cardinality of its actual residue
  field, and the residue action of every Weil element is the indicated integer
  power of geometric Frobenius.
- Projection to the absolute Galois group is injective with dense image, and
  the discrete degree is surjective.
- Degree-zero inertia is precisely the inverse image of actual absolute
  inertia. The constructed inclusion has exactly that range and is an open
  embedding. This subgroup is open, compact and normal, and its topological
  group equivalence with absolute inertia respects the actual projection.
- The actual Weil group is nonarchimedean, locally compact, Hausdorff and
  totally disconnected in the inherited pullback topology.
- The chosen lift has geometric degree `+1` and acts on the actual residue
  closure as geometric Frobenius.
- The complex norm character has formula `q^(-degree)` for the actual residue
  cardinality, hence value `q^-1` on the lift. Every constructed unramified
  character is trivial on inertia and has its prescribed value on that lift.

This is a proposition definition, not an existence assumption used by the
constructor; its proof is a separate obligation. It does not assert
reciprocity, local Langlands, finite-extension Weil subgroup compatibility, or
preservation of parameter predicates. Finite-extension maps are constructed,
with their properties proved, in `Langlands.Weil.Local.ExtensionWeil`.

The mathematical source correspondence is the same as `Assembly.md`: Henniart
1980 section 2.1 and the opening of 2.2 describe the integer quotient and open
inertia; Tate 1979 sections 1.4.1, 1.4.6 and 4.1.3 fix the residue cardinality,
geometric sign and norm. The explicit maps, typeclass consequences, and bundled
universe-polymorphic target are derived formal interfaces for that description.

Original-source identifiers: `henniart-1980-weil-representations`, PDF SHA-256
`451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`,
printed page 158 / PDF page 5; and `tate-1979-number-theoretic-background`,
Part II PDF SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`,
printed pages 6, 7, 20 / PDF pages 15, 16, 29. The original paths are
recorded in `Assembly.md`; the target is a derived interface, not a verbatim
theorem attributed to either source.

The only project import, `Langlands.Weil.Local.Assembly`, is published at
Library commit `0fbab0ee36b0ab602b6d43bc3d60ada813fcedbf`; Mathlib's
`Mathlib.Topology.Algebra.Nonarchimedean.Basic` supplies `NonarchimedeanGroup`.
The environment is Lean 4.34.0 with Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
