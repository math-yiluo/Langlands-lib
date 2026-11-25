# Reductions of primitive irreducible polynomials under unique extension

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file supplies the Galois-theoretic input for the converse of the unique-extension criterion: if a valuation ring V ⊂ K extends uniquely to every algebraic extension, then V satisfies `PrimitiveIrreducibleReductionProperty`, from which the file on primitive factorization derives Hensel's factorization lemma. Uniqueness makes the extended valuation ring invariant under automorphisms, so conjugate roots have the same value, and Vieta's formulas control the reduction.

## Main results

- `valuation_algEquiv_eq_of_unique_extension_of_finiteDimensional`: let L/K be finite and W the only valuation subring of L whose valuation extends that of V. Then every K-automorphism σ of L satisfies w(σx) = w(x).
- `valuation_eq_on_roots_of_irreducible_of_unique_extension`: for L/K finite and normal with such a unique W, all roots in L of an irreducible p ∈ K[X] have the same W-value.
- `primitive_irreducible_reduction_natDegree_zero_of_leadingCoeff_nonunit`: if Q ∈ V[X] is primitive, irreducible over K, has nonunit leading coefficient, and V extends uniquely to a splitting field of Q over K, then the reduction of Q is constant.
- `primitiveIrreducibleReductionProperty_of_unique_algebraic_extensions`: if V has a unique extension valuation subring on every algebraic extension E of K in the same universe, then `PrimitiveIrreducibleReductionProperty V` holds.

The file also restates, under the namespace `AlgebraicNumberTheory.Valuations`, the Vieta lemma that the constant coefficient of ∏(X − α) dominates the others when all α have value greater than 1.

## Proof

σ maps W onto itself, by a lemma of an earlier file, so it preserves the order of values; a strict change of the value of x would propagate along the finite orbit of σ and give a strict cycle. In the nonunit case, the Vieta estimate of the monic-factorization file makes the constant coefficient a unit, so the common root value exceeds 1 and all higher coefficients reduce to zero. In the unit case the reduction has full degree; after normalizing Q to be monic, `irreducible_monic_reduction_coprime_factor_degree_zero` from an earlier file, applied on a splitting field, rules out a coprime splitting into two nonconstant factors.

## Points to watch

- The main hypothesis quantifies over all algebraic extensions in the universe of K, though only splitting fields of single polynomials are used.
- Uniqueness means a unique valuation subring, that is uniqueness of the extended valuation up to equivalence.
- The nonunit case is the conclusion of the file on the nonmonic reduction branch, here derived from uniqueness rather than from an equal-root-value hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/UniqueExtensionPrimitive.lean`: the Lean file is the source byte for byte (SHA-256 `c553422fe1ca6b98e8170b4ccefabc0de083fd9e0c6667d36438e1224c8cbf12`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
