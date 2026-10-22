# Arithmetic Frobenius coordinates for unramified p-adic extensions

Author: Worker 107.

The theorem
`Langlands.ClassFieldTheory.Local.arithmeticUnramifiedCoordinateExistence.{u,v}`
proves exactly the published proposition
`ArithmeticUnramifiedCoordinateExistence.{u,v}` from
[UnramifiedArithmeticStatement](UnramifiedArithmeticStatement.md).
For every prime `p` and every compatible finite Galois extension `E/F` of
`PadicField p` objects in independent universes, equality of their canonical
absolute ramification indices yields a multiplicative equivalence

`Gal(E.Carrier/F.Carrier) ≃* Multiplicative (ZMod [E : F])`.

This equivalence satisfies the existing `IsArithmeticUnramifiedCoordinate`
predicate: the actual spectral residue homomorphism is injective, and the
inverse image of the additive coordinate `1` acts on the actual extension
residue field by the base residue cardinality power. All hypotheses,
quantifiers and universe parameters of the published proposition are retained.
The degree-one case is included without a separate assumption or exception.

## Implemented proof

The auxiliary namespace is
`Langlands.ClassFieldTheory.Local.ArithmeticCoordinate`. Its constructions
use the canonical norm on `F`, its canonical normed algebra over `Padic p`,
the ultrametric certificate for the spectral norm, and properness from finite
dimensionality. These are the structures used in the target predicate.

1. `baseIntegerEquiv` is the identity on field elements, viewed as an
   equivalence between `LocalGalois.baseIntegers F.Carrier` and
   `F.canonicalTopologicalData.Integers`. The published
   `canonicalNorm_le_one_iff_mem_integers` identifies their underlying
   subrings. `baseResidueEquiv` applies the actual residue-field functor to
   this ring equivalence.

2. `spectralNorm_eq_canonicalNorm` identifies the spectral norm of `E` over
   `F` with `E.canonicalNorm`. Mathlib's `spectralNorm.normedAlgebra'`
   supplies the normed `F`-algebra structure for the canonical norm on `E`,
   using the given p-adic scalar tower. Uniqueness of the extended norm,
   `NormedAlgebra.norm_eq_spectralNorm`, proves the equality. Consequently,
   `extensionIntegerEquiv` and `extensionResidueEquiv` identify the actual
   spectral extension integer and residue rings with the canonical ones.
   These maps preserve the underlying field elements; no replacement
   residue action is introduced. The residue equivalences transfer the
   published finiteness of the canonical residue fields.

3. `residue_finrank` proves that the degree of the actual spectral residue
   extension equals `n = Module.finrank F.Carrier E.Carrier`. Write `e_F`,
   `f_F`, `e_E`, and `f_E` for the canonical absolute ramification indices
   and residue degrees. The published identities
   `e_F * f_F = [F : Q_p]` and `e_E * f_E = [E : Q_p]`, together with the
   field-degree tower formula and `e_F = e_E`, give `f_E = f_F * n`.
   Cancellation is justified by `ramificationIndex_pos`. The canonical
   residue cardinalities are `p ^ f_F` and `p ^ f_E`; transporting these
   cardinalities through the residue equivalences gives `|k_E| = |k_F| ^ n`.
   Mathlib's finite-vector-space cardinality formula also gives
   `|k_E| = |k_F| ^ [k_E : k_F]` for the actual spectral residue algebra.
   Since a finite field has more than one element, injectivity of natural
   exponentiation proves `[k_E : k_F] = n`. This argument only needs the
   residue ring equivalences and cardinalities, so it does not need an
   additional scalar-compatibility assertion between the two residue models.

4. `residueHom_injective` combines the published
   `LocalGalois.residueHom_surjective` with equal finite group cardinalities.
   The given Galois extension has `n` automorphisms. The actual residue
   extension is an extension of finite fields, hence Galois, and its
   automorphism group also has `n` elements by `residue_finrank`.
   A surjection between finite sets with these cardinalities is bijective.
   Thus injectivity of the precise residue homomorphism required by the
   target is proved, rather than assumed.

5. `coordinate_exists` packages this actual residue homomorphism as a
   multiplicative equivalence `r`. It takes Mathlib's
   `FiniteField.frobeniusAlgEquivOfAlgebraic` on the residue extension,
   denoted `φ`, and transfers it to `r.symm φ` in the field Galois group.
   The bijectivity of the finite-field Frobenius-power parametrization
   proves that every field automorphism is an integral power of this
   transferred element. `zmodMulEquivOfGenerator`, using the field Galois
   group cardinality `n`, then supplies an equivalence from
   `Multiplicative (ZMod n)` to the field Galois group. Its inverse is the
   coordinate `χ`. The generator formula sends `Multiplicative.ofAdd 1`
   to `r.symm φ`, so applying the actual residue homomorphism gives `φ`.
   Its defining action is `x ↦ x ^ Fintype.card k_F`; the equality of
   `Fintype.card` with `Nat.card` gives the exact required formula.

The closing theorem applies `coordinate_exists` to the quantified fields and
hypothesis. Positivity of the field degree supplies the target's local
`NeZero n` instance. For `n = 1`, the same cyclic-group construction and
Frobenius-power parametrization apply; they do not require a nontrivial
Galois group.

## Sources and provenance

Jean-Pierre Serre, *Local Fields*, Greenberg English translation, Springer
GTM 67 (1979), registered source `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
The retained original is
`/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 107 read III.5, Theorems 2 and 3 and their corollaries, printed
pp.54–55 / PDF pp.61–62, and XIII.2, example (a), printed p.191 /
PDF p.196. No project errata entry for this source was present when checked.

The first passage identifies unramified extensions and their morphisms with
separable residue extensions; the second specifies arithmetic Frobenius as
the cardinality-power generator for finite fields. The target is the
published p-adic specialization documented in its statement pair. The
implemented proof establishes the required finite Galois comparison by
norm uniqueness, the Library's proved normalization identities, residue
surjectivity, and finite cardinalities. It does not reimplement the source's
Hensel-lifting proof. The cyclic coordinate is derived from Mathlib's proved
finite-field Frobenius theorems. No unramified-lifting, coordinate-existence,
class-formation, reciprocity, or invariant premise is used.
