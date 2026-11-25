# Regrouping a finite product over fibers

Module `Nyll.ClassFieldTheory.Algebra.FinprodFibers`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A small lemma on finitely supported products in a commutative monoid G.

- `finprod_fibers_eq_sigma`: for any map g : α → β and any f : α → G with finite multiplicative support (`HasFiniteMulSupport f`), the product over b ∈ β of the products of f over the fiber {x | g x = b} equals the product of f over α, all products being `finprod`.

The proof reduces both sides to a product over the finite support of f and uses Mathlib's `Finset.prod_fiberwise_of_maps_to`. No finiteness of α, β or of the fibers is assumed; only the support of f is finite.

Despite the suffix `_sigma` in the name, the statement does not involve a sigma type: it regroups over fibers given as subtypes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Algebra/FinprodFibers.lean`: the Lean file is the source byte for byte (SHA-256 `ad479edcb8138f22c0d373bd866377078e7a15a243311a56181a0890bf1f81bd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
