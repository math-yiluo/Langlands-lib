# Congruence subgroups and the topology of the idele class group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field and C_K its idele class group. The local higher-unit groups and the idele congruence subgroups are open. Each ray congruence subgroup of C_K is open, closed and of finite index. Every open subgroup of C_K contains the ray congruence subgroup of some modulus. So the closed subgroups of finite index are exactly those containing a congruence subgroup.

## Local and idelic openness

- `isOpen_localHigherUnitGroup`: the higher-unit group U_v^(n) is open in (K_v)ˣ. `localHigherUnitGroup_antitone` says it shrinks as n grows.
- `exists_localHigherUnitGroup_subset`: every neighbourhood of 1 in (K_v)ˣ contains some U_v^(n). The proof bounds |x − 1| ≤ |ϖ|ⁿ on U_v^(n) (`localHigherUnit_norm_sub_one_le`) and uses |ϖ| < 1 for a uniformizer ϖ.
- `isOpen_finiteCongruenceSubgroup`, `isOpen_infiniteCongruenceSubgroup` and `isOpen_ideleCongruenceSubgroup`: the finite, infinite and full idele congruence subgroups are open. So are the positivity subgroups at the infinite places; at a complex place it is the whole group.
- `exists_finiteCongruenceSubgroup_subset`: every open set of finite ideles containing 1 contains a finite congruence subgroup.

## Signs and connectedness

- `isConnected_infinitePositiveSubgroup` and `isConnected_narrowInfiniteCongruenceSubgroup`: the positive subgroup at an infinite place is connected, since it is the positive reals or ℂˣ, and so is their product.
- `infiniteSign`: the tuple of signs, with values in `SignTypeˣ`, at the real places. `infiniteSign_ker_eq_narrowInfiniteCongruenceSubgroup` says its kernel is the subgroup of ideles positive at every real place. That subgroup therefore has finite index.

## Finite index and cofinality

- Instances give finite index for each of the following. The infinite congruence subgroups have it. The finite congruence subgroup has it inside the compact group of integral finite ideles, being open there. The ideles integral at all finite places times Kˣ have it because the class group is finite, and so does I_K^m·Kˣ. Finally, `congruenceSubgroupFiniteIndex` covers the ray congruence subgroup in C_K.
- `isOpen_congruenceSubgroup` and `isClosed_congruenceSubgroup`.
- The finite, infinite, idele and ray congruence subgroups all shrink as the modulus grows. These are the lemmas `..._antitone`.
- `narrowInfiniteCongruenceSubgroup_mapsTo_openSubgroup`: every open subgroup of C_K contains the image of the narrow positivity subgroup. The image is connected and contains 1, and an open subgroup is clopen.
- `exists_congruenceSubgroup_le_of_isOpen`: every open subgroup H of C_K contains `m.congruenceSubgroup` for some modulus m. `chosenModulusInside` and `modulusInsideClosedFiniteIndex` choose such an m.
- `isClosed_and_finiteIndex_iff_exists_congruenceSubgroup_le`: H is closed of finite index if and only if it contains a ray congruence subgroup.

## Points to watch

- The existence proof uses a modulus `Modulus.narrowOfFinite f`, with every real place. `chosenModulusInside` takes an arbitrary witness by `Classical.choose`. Nothing makes it minimal or relates it to a conductor.
- The cofinality theorem needs only openness of H.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Topology.lean`: the Lean file is the source byte for byte (SHA-256 `f5e976f030953ab612757c1104636b9bc1f6e07a22857ae060da94733f96829d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
