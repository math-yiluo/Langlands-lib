# Finite abelian reciprocity and actual idele norms

Author: Worker 35. Statement contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
Its declarations are proposition definitions; none supplies a proof of
class-field theory.

## The actual norm image

Let `K : Type u` and `L : Type v` be number fields with an algebra
structure `Algebra K L`. Their carrier universes are independent.
The number-field structures imply finite relative dimension.
The four assertions below also require `IsGalois K L` and explicit
commutativity of the actual automorphism group `L ≃ₐ[K] L`.

`AdelicFunctoriality.ideleNorm` is Worker 50's constructed continuous
homomorphism from the ideles of `L` to the ideles of `K`. At each base
place its value is the product of the determinant norms from all
completed fields above that place. The infinite and finite factors
are both included. It is not an extension-of-scalars embedding, a
norm on absolute values, or a freely chosen map.

Compose this map with the published `ideleClassMap K`. The resulting
continuous homomorphism has domain `Ideles L` and codomain
`IdeleClasses K`. Its group-theoretic range is the norm-image subgroup
used in this file. The domain has deliberately not been quotiented:
this composition is constructed without a principal-norm compatibility
theorem or a norm on `IdeleClasses L`. Once that compatibility is proved,
the image of the descended class norm is exactly this subgroup, because
the quotient map from ideles to idele classes is surjective.

This formulation preserves the ordinary class-field norm subgroup
while keeping the unfinished quotient-descent construction explicit.
It does not prove that descent or assume it as a hypothesis.

## The four targets

`ArtinNormKernelStatement` quantifies every continuous surjective map
`ρ : IdeleClasses K →ₜ* Gal(L/K)` satisfying the actual arithmetic
Frobenius normalization from `ClassFieldStatement`. Its conclusion is
equality of the kernel of `ρ` and the range of the composed idele norm.
The finite Galois group receives the discrete topology by a local
instance, exactly as in the preceding reciprocity target.

`LocalGlobalNormImageStatement` asserts the precise local/global norm
intersection theorem at every finite and infinite place. For each place
`p` of `K` and each place `q` of `L` lying above it, take the inverse
image of the global norm subgroup under the actual local insertion
`K_pˣ → IdeleClasses K`. It equals the range of the actual local norm
`L_qˣ → K_pˣ`. Finite lies-over is the relation on the actual nonzero
prime ideals; infinite lies-over is Mathlib's relation on infinite
places. The local algebras and determinant norms are constructed in
the published `Extension` module. No unramified-place restriction is
added, and real places which become complex are included.
Using a subgroup inverse image avoids presupposing an identification
of a local multiplicative group with a literal subset of the quotient.

`AbelianIdeleNormIndexStatement` asserts that the index of the same
subgroup is `Module.finrank K L`. It is independent of any chosen
reciprocity map and has no such map as input. The index is Mathlib's
actual subgroup index. The conclusion in particular rules out its
infinite-index value zero, since a number-field extension has positive
finite degree.

`HeckeNormFactorizationStatement` takes the same normalized surjection
and an arbitrary continuous complex Hecke character `χ` of `K`. It
asserts an equivalence between:

1. `χ` being one on the image of every actual idele norm;
2. existence of a unique continuous complex character `θ` of `Gal(L/K)`
   such that `θ (ρ x) = χ x` for every idele class `x`.

No finite-order or unitary hypothesis is imposed on `χ`. If the
factorization exists, its finite quotient forces those properties;
they are consequences rather than assumptions. The target does not
require `θ` to be faithful: its kernel can be nontrivial for the
specified extension `L/K`. Uniqueness is equality of the entire
continuous homomorphisms and follows from surjectivity of `ρ`.
The trivial character and the degree-one extension are included.

`ArtinNormComparisonStatement` is the conjunction of these four
complete propositions and retains both universe parameters.
The map-existence assertion remains the separate
`FiniteAbelianArtinReciprocityStatement`; this file does not replace
that assertion with a map supplied as theorem-truth data. The index
clause itself is unconditional on a chosen map.

## Normalization and original sources

The Artin maps use arithmetic residue Frobenius: a local uniformizer
at an unramified finite place maps to the automorphism acting by the
base residue cardinality on residue classes. The opposite
inverse-Frobenius convention in Tate (1979), Section 1.4.1, is still
distinct. Inverting an Artin map does not change its kernel or the norm
index. In the character-factorization clause it replaces `θ` by its
pointwise inverse. An eventual comparison with a Weil-group map must
make that conversion explicit.

Artin–Tate, *Class Field Theory*, AMS Chelsea edition (2009),
Chapter VII, Section 3, pp.41–52, constructs the global norm-residue
symbol and identifies its norm kernel; Theorem 9 and Corollaries 2–3,
pp.51–52, compare it with the local symbols and establish continuity.
The proof of Theorem 10 on p.52 explicitly identifies the kernel on
ideles with the product of the principal ideles and the idele norms.
Passing to idele classes gives exactly the kernel-image equality
used here.
Chapter VIII, Sections 1–2, pp.55–57, states the correspondence with
open finite-index norm subgroups and the number-field surjectivity
theorem. The induced quotient is the finite abelian Galois group,
so its order, and hence the subgroup index, is the field degree.
These original passages were read directly.

Chapter VIII, Section 1, Theorem 2, pp.55–56, is the local/global
norm intersection theorem. The source explicitly states that its
local consequences apply at finite and infinite places. The Lean
inverse-image equality is its formulation on the actual continuous
local insertion and actual local determinant norm. Its proof is a
global product-formula argument; it is not supplied by the local
norm construction and remains a separate theorem obligation.

The character equivalence is an explicit derived consequence:
the kernel theorem turns triviality on norms into triviality on
`ker ρ`; quotient factorization gives `θ`, and surjectivity gives its
uniqueness. The quotient is a finite discrete group, so continuity of
`θ` introduces no extra hypothesis. Conversely, a factorization kills
the norm subgroup by the kernel theorem. This explanation justifies
the statement's provenance; it is not a submitted Lean proof.

The use of an idele norm followed by the class quotient is another
explicit reformulation. Artin–Tate's class norm has this image by
definition of its descent. The prerequisite equality of global norms
with products of completed local norms and the principal-norm formula
are Worker 50's separate construction and theorem obligations.

Source fingerprints:

- `artin-tate-2009-class-field-theory`,
  SHA256 `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`;
  Chapter VII, Section 3, pp.41–52, especially the proof of Theorem 10
  on p.52; Chapter VIII, Sections 1–2, pp.55–57, especially
  Section 1, Theorem 2, pp.55–56.
- `tate-1979-number-theoretic-background`,
  SHA256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`;
  Section 1.4.1, printed p.6, for the opposite reciprocity convention.

## Dependency and validation boundary

The module imports `Langlands.Global.Arithmetic.ClassFieldStatement` and
`Langlands.Global.AdelicFunctoriality.Norm`. Every project module in its
import closure is published at Library commit
`68e8013fc4fed0de284fd849695676aca2e0c32d`, and the compiled sources are
byte-identical to the Library files:

| Module | Author | Lean SHA256 |
| --- | --- | --- |
| `Langlands.Global.Adelic` | Worker 2 | `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e` |
| `Langlands.Global.HeckeCharacter` | Worker 2 | `68525fbd6a536afefdb696f83491c0ddd60d506390cf7dcb9682c7688c3de18f` |
| `Langlands.Global.Arithmetic.ClassFieldStatement` | Worker 35 | `d4f5888bc7dded26d3f7efdd8cfbdcfcc619ceece6770134fa8dc72400436055` |
| `Langlands.Global.AdelicFunctoriality.Extension` | Worker 50 | `d80b486975f4272cf442044e647b123ab9c16e1a42d39b3090a7a668bc623a4a` |
| `Langlands.Global.AdelicFunctoriality.Norm` | Worker 50 | `22cca7bbbdf85f7ed70b4c9a8efe8b4b917609fd868621a56c91115100433b38` |

The complete `Norm` source and its paired explanation were read before
writing this consumer. It constructs the required idele norm without
assuming its separate `NormCompatibility` target, and this pair uses
neither that target nor any conditional idele-class norm.

The module compiled with no errors or warnings under Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, in the project
environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. All five complete
elaborated definitions were printed with explicit universe parameters.
They return `Prop`; the closing conjunction retains `u` and `v`.
The inspected character factor has type
`ContinuousMonoidHom Gal(L/K) ℂˣ`, and the local norm clause includes
both actual finite and infinite lies-over relations.
The closing definition's axiom report contains only `propext`,
`Classical.choice` and `Quot.sound`.
These are development checks, not independent semantic acceptance
or a proof of any asserted theorem.

The global Weil-group construction, its local-global maps, and
automorphic applications remain further obligations of the broad task.
