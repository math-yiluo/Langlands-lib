# Extending a finite Hensel prefix by one step

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file contains the inductive step of the finite Hensel construction over a local ring `R` without zero divisors, with π ≠ 0 in the maximal ideal 𝔪. A prefix is a pair of correction sequences whose iterates g_r, h_r (built from g0, h0) satisfy f − g_r·h_r = π^(r+1)·f_r for all r ≤ n.

`henselFactorization_extend_finite_prefix_one_step_of_mem_span` chooses p, q with deg p ≤ m, deg q ≤ d − m such that, with the corrections at index n+1 set to p and q, the identities for r ≤ n persist, f − g_(n+1)·h_(n+1) = π^(n+2)·f_(n+1), the new iterates keep the degree bounds m and d − m, and they reduce to g0, h0 modulo 𝔪. It assumes deg f ≤ d, m ≤ d, g0 of degree m reducing to ḡ ≠ 0 of degree m, deg h0 ≤ d − m, the degree bounds for the current iterates, and a·g0 + b·h0 − 1 = π·e.

It applies the single-step existence result. The Bezout relation needs an explicit factor π.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/Factorization/FiniteApproximation.lean`: the Lean file is the source byte for byte (SHA-256 `00ec4b32890c3e12b83584c65259c5afb3f9b4aed3ab9e4da935f87f53926087`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
