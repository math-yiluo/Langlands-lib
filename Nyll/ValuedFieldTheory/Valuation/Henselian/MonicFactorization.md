# Monic factor lifting and equal values of conjugate roots

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.MonicFactorization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a valuation ring V of a field K, this file isolates the monic form of Hensel's factor lifting and derives two consequences: all roots of an irreducible polynomial have the same value in a normal extension, and V is a henselian local ring. The comments attribute the root-value argument to Artin. Below, B denotes a valuation ring of an extension L of K whose valuation extends that of V (`HasExtension`).

## Definition

- `MonicResidualCoprimeFactorLifting V`: the library's proposition that for every monic f ∈ V[X] and monic coprime ḡ, h̄ over the residue field with f̄ = ḡ·h̄, there are monic G, H ∈ V[X] with f = G·H reducing to ḡ and h̄.

## Main results

- Vieta-type estimates for the coefficients of ∏(X − α) and for elementary symmetric functions; in particular, if r of the α have value t ≠ 0 and the others smaller value, the r-th elementary symmetric function has value t^r.
- `residue_ne_zero_of_isPrimitive_valuationSubring`: a primitive polynomial over V has nonzero reduction.
- `not_all_roots_same_valuation_of_primitive_irreducible_endpoints_nonunit`: if p ∈ V[X] is primitive, irreducible over K, splits in L, and has nonunit leading and constant coefficients, then its roots in L do not all have the same B-value.
- `exists_mixed_residual_minpoly_of_irreducible_roots_unequal`: for L/K normal and p irreducible splitting in L with two roots of different B-value, some monic Q ∈ V[X], irreducible over K, has a reduction with zero constant term and a nonzero root in the residue field of B.
- `monicResidualCoprimeFactorLifting_of_henselFactorization`: `HenselFactorizationProperty V` implies `MonicResidualCoprimeFactorLifting V`, by rescaling the factors with their mutually inverse leading coefficients.
- Consequences of `MonicResidualCoprimeFactorLifting V`: a monic f whose reduction splits into coprime monic factors of positive degree is reducible over K (`MonicResidualCoprimeFactorLifting.not_irreducible_map`); for L/K normal and p irreducible splitting in L, all roots of p in L have the same B-value (`MonicResidualCoprimeFactorLifting.irreducible_roots_same_valuation`); and V is a `HenselianRing` for its maximal ideal (`henselianRing_of_monicResidualCoprimeFactorLifting`).

## Proof

For roots of unequal value, let r be the number of roots of maximal value t and a = ±e_r(roots) ∈ K, of value t^r. The minimal polynomial of z = α^r/a, with α a root of value t, has integral coefficients, a conjugate of value below 1 and the root z of value 1; its reduction splits as X^s·R with s > 0 and R of positive degree coprime to X, which monic lifting forbids.

## Points to watch

- Although the namespace is `DiscreteValuationField`, no result assumes a discrete or rank-one valuation.
- The root statement holds for any B extending V; it does not assert uniqueness of the extension.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/MonicFactorization.lean`: the Lean file is the source byte for byte (SHA-256 `bdc36b6698b2b0d1194cd7a7c97c1bdb0258154568a09d2303fe7b8cd650ee24`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
