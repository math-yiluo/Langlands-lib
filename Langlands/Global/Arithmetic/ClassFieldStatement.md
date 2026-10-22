# Finite abelian global class-field statements

Author: Worker 35. Contribution to task
`369ca096-d0b6-4e25-8a06-66af3ef95878`, revision 2.
All declarations are proposition definitions. Defining them assumes no
reciprocity theorem, class-field existence theorem or Langlands theorem.

## Actual objects and the reciprocity convention

The base `K : Type u` is an arbitrary number field. `IdeleClasses K` is
the published actual quotient of the units of Mathlib's adele ring by
principal ideles, with its quotient topology. `finiteClassInclusion`
inserts a local nonzero element at one finite place, inserts one at every
other place, and passes to the quotient.

`HasArithmeticArtinNormalization ρ` is an explicit condition on a group
homomorphism from this quotient to the actual automorphism group of an
extension `L/K`. At every finite place and every unramified prime of `L`
above it, the image of every local uniformizer is required to be
arithmetic Frobenius. The relation `LiesOver`, the property
`Algebra.IsUnramifiedAt`, and `IsArithFrobAt` are Mathlib's predicates
on the actual rings of integers and their nonzero prime ideals.

A local uniformizer is a unit of the completion viewed as a field,
with multiplicative valuation `WithZero.exp (-1 : ℤ)`. It is not a unit
of the local valuation ring. This normalized value corresponds to
additive valuation one. Such elements exist in the actual completion.
Arithmetic Frobenius acts on the residue field by raising to the
cardinality of the residue field of the base prime. All primes above
the base place are quantified; in an abelian extension the resulting
Frobenius element is independent of that choice.

This is the **arithmetic** reciprocity convention of Artin–Tate. Tate's
1979 Weil-group convention sends a uniformizer to inverse Frobenius.
Consequently a later comparison with Tate's or Henniart's Weil
reciprocity must invert the present map. No silent interchange of these
normalizations is made here.

## The theorem group

`FiniteAbelianArtinReciprocityStatement` quantifies `K : Type u` and
`L : Type v` in independent universes, their number-field structures,
an algebra structure and `IsGalois K L`. The hypothesis
`∀ σ τ, σ * τ = τ * σ` is abelianness of the actual Galois group.
A number field extension is finite; Mathlib infers its finite
dimensionality. The conclusion is existence and uniqueness of a
continuous surjective homomorphism with the arithmetic normalization.
The map is existential, not an assumed field of a record.

The finite Galois group receives the discrete topology explicitly,
using a local `letI`. This is the ordinary topology on a finite Galois
group; no global topology instance is replaced.

`OpenIdeleClassSubgroupFiniteIndexStatement` says that every open
subgroup of `IdeleClasses K` has finite index. This is an assertion about
number fields, not a fact built into the definition of an open subgroup.

`FiniteAbelianClassFieldExistenceStatement` takes an open subgroup `H`
and retains finite index as an explicit hypothesis. It asks for an
actual intermediate field `L` of `AlgebraicClosure K`, its finite
dimensionality, its Galois and abelian properties, and a surjective
normalized continuous map whose kernel is exactly `H`.
The number-field instance on `L` is obtained by Mathlib's proved
`NumberField.of_module_finite K L`, after installing the existential
finite-dimensional instance. No finite-extension existence is hidden
in that instance construction.

`FiniteAbelianClassFieldKernelRigidityStatement` takes two finite
abelian intermediate fields of the same algebraic closure and two
normalized continuous surjections. If their kernels agree, the
intermediate fields are equal. Since a common closure was fixed,
equality of actual subfields is appropriate; this does not identify
arbitrary carrier presentations by literal type equality.

`FiniteOrderHeckeArtinRealizationStatement` takes an actual continuous
finite-order Hecke character. It asks for a finite abelian field `L`
inside the algebraic closure, a surjective normalized reciprocity map
and a faithful continuous complex character of its finite Galois group
whose pullback is the given Hecke character. Faithfulness corresponds
to choosing the class field of the original character's kernel.
The trivial character is permitted and yields the degree-one case.

`FiniteAbelianClassFieldStatement` conjoins the five complete targets.
The closed proposition retains universes `u` and `v`. Existential
fields are realized as actual intermediate fields in the closure of
`K`, so those existence clauses use universe `u`; reciprocity itself
still covers independent carrier presentations.

## Original sources and derived formulations

Artin–Tate, *Class Field Theory*, 2009 edition, Chapter VII, Section 3,
Theorem 9 and Corollaries 2–3, pp.51–52, give the global/local product
formula and continuity of the reciprocity map. The same section,
pp.41–51, constructs the global class formation and symbol; the finite
abelian map is obtained by passing to the finite quotient. Chapter VIII,
Section 2, Theorem 4, p.56, gives surjectivity for number fields.
The unramified normalization comes from the local norm-residue symbol
and the product formula. These passages were read directly.

Chapter VIII, Section 1, Theorem 1 and its corollary, p.55, give the
existence theorem and the one-to-one correspondence between open
finite-index subgroups and finite abelian extensions inside a fixed
algebraic closure. Section 2, pp.56–57, proves the number-field
existence theorem. Theorem 5, p.57, proves finite index for every open
subgroup. The kernel formulations here are the finite-quotient forms
of those statements, using the kernel of reciprocity in place of the
equal idele norm subgroup.

Uniqueness of the map from the unramified normalization alone is a
derived characterization, rather than a separate displayed assertion
of Theorem 9. The quotient of two candidate maps has finite abelian
image. By the existence theorem its open kernel is the norm subgroup
of a finite abelian extension. Equality of the two maps on uniformizers
outside the finite ramified set makes almost every prime split
completely in that extension. Artin–Tate, Chapter V, Section 4,
Theorem 2, p.17, says that a nontrivial finite normal extension has
infinitely many primes which do not split completely. The extension
must therefore be trivial, and the two maps agree. This derived
argument uses the non-splitting theorem; it does not assert that
individual uniformizers are topologically dense in the entire
idele-class group.

The finite-order character statement is a further explicit consequence.
A continuous finite-order complex character has finite image and
open finite-index kernel. Apply the existence theorem to that kernel,
and factor the character through the finite quotient, obtaining a
faithful character of its Galois group. These are future proof
obligations; no factorization proof is supplied by defining the target.

The statements do not yet identify the kernel with the image of the
**actual adelic norm**: that norm construction is a separate dependency.
They also do not replace the global Weil group, its class-formation
fundamental classes, its inverse-system construction or the
local-to-global Weil maps. Those remain required for the broad task.

### Source fingerprints

- Artin–Tate, *Class Field Theory*, AMS Chelsea, 2009:
  Chapter V, Section 4, Theorem 2, p.17; Chapter VII, Section 3,
  pp.41–52, especially Theorem 9 and
  Corollaries 2–3, pp.51–52; Chapter VIII, Sections 1–2, pp.55–57,
  Theorem 1 and its corollary, Theorems 4–5.
  Source `artin-tate-2009-class-field-theory`, SHA256
  `af7ba934904a3c10012e6fd326cea493ffb6200d885d97583277bb45f935c3dd`.
- Tate, *Number theoretic background*, Corvallis Part II, 1979,
  Section 1.4.1, printed p.6, for the explicitly opposite uniformizer
  convention, and Section 1.6.1, p.8, for the role of local insertion
  in the later Weil-group comparison.
  Source `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.

The cited non-splitting theorem suffices for the derived uniqueness
argument. The stronger Frobenius prime-realization assertions in the
separate `ChebotarevStatement` pair are not imported or assumed here.

## Dependencies and validation boundary

The only project imports are the published
`Langlands.Global.HeckeCharacter` and its `Langlands.Global.Adelic`
dependency at Library commit
`1804f2a6d98d21c2bbfa3c73ccf807df74c484bb`.
Their Lean SHA256 values are, respectively,
`68525fbd6a536afefdb696f83491c0ddd60d506390cf7dcb9682c7688c3de18f`
and `b1b7213c47725ac26e0ce09b0e483e548c8a4e1f3fd4a4972cedb64b7ce8258e`.
All other constructions are from Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, with Lean 4.34.0.
Native compilation and full elaborated-type inspection of the helper,
all five component targets, and the conjunction succeeded without
warnings or errors. The closed target depends only on the standard
Lean axioms `propext`, `Classical.choice` and `Quot.sound`.
This checks elaboration and logical dependencies, not the truth of
the stated class-field theorems.
Independent semantic acceptance and current publication remain required.
