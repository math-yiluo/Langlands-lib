# Ideal Frobenius classes

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let N be a subgroup of the idele class group C_K, m a modulus whose congruence subgroup lies in N, and v a prime not dividing m. The file studies the image of v under the ideal Artin map I^m → C_K/N, the ideal-class part of the decomposition law.

## Main definitions and results

- `idealFrobeniusClass m N hm v hv`: the image of the prime ideal v in C_K/N.
- `orderOf_idealFrobeniusClass`: its order equals the order of the class of v in I^m/H_m, where H_m is the kernel of the Artin map.
- `primeIdeal_pow_mem_idealArtinKernel_iff_orderOf_dvd`: vⁿ ∈ H_m if and only if that order divides n. If that order is positive, it is the least f > 0 with v^f ∈ H_m.

## Points to watch

- `idealFrobeniusClass` takes values in C_K/N, not in a Galois group. The docstring calls it the usual Frobenius under reciprocity; this file proves no comparison.
- The relation r·f = n of the decomposition law is not proved here. The header places it in `RamificationTheory.HilbertRamification.Dedekind.Basic`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/IdealClassFieldTheory/IdealFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `7e43eb94cea0d51070398ff40fef4bcb52fa27872396b0d12279df781deea729`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
