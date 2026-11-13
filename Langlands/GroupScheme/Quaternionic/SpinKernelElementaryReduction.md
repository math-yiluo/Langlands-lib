# The rational kernel element of a quaternionic spin cover is elementary

Module `Langlands.GroupScheme.Quaternionic.SpinKernelElementaryReduction`, namespace
`Langlands.GroupScheme.Quaternionic.SpinKernel`.

The module derives `SpinKernelElementaryLiftStatement` (module `SpinKernelAssembly`) from two
statements:

* `CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement`: `SL₁(A)` is simply connected
  for every central simple algebra `A` of dimension 4 (written `hsc` below);
* `KneserThreeSpinSubgroupStatement` (module `KneserThreeSpinSubgroupStatement`): the binary
  action `SL₂ × SL₁(D) ⟶ O(q)` of a hyperbolic pair factors as `j ≫ c` through a simply
  connected group `C`, and the rational point `j(-1, -1)` lies in `C(K)⁺`.

It proves neither of them. This is internal content: a composition of Library results with no
new literature claim.

## Library results used

* `IsSpinCover.liftHom`, `liftHom_comp`, `liftHom_unique` (module `BinaryQuaternionSpinLift`): a
  homomorphism `f : C ⟶ O(q)` from a simply connected `C` has a unique lift `a : C ⟶ S` through
  a spin cover `π : S ⟶ O(q)`, with `a ≫ π = f`.
* `BinarySpinLift.specialLinear`, `BinarySpinLift.normOne`, `BinarySpinLift.scalar` (same module):
  the lifts of the two factors of the binary action, and the diagonal cocharacter
  `upperCocharacter ≫ specialLinear`. `BinarySpinLift.specialLinear_simplyConnected` gives
  simple connectedness of `SL₂` from `hsc`.
* `isLeviLift_binarySpinLift` (module `SpinLeviLift`): under `hsc`, the pair
  `(BinarySpinLift.scalar, BinarySpinLift.normOne)` is a Levi lift (`IsLeviLift`).
* `IsLeviLift.scalar_eq` and `IsLeviLift.normOne_eq` (module `SpinLeviUniqueness`): two Levi
  lifts of the same hyperbolic pair into the same spin cover have the same scalar part, and the
  same norm-one part when `SL₁(D)` is connected reductive.
* `rationalCoeffEquiv_comp_hom` (module `SpinKernelDescent`) and
  `parabolicElementarySubgroup_map_le_of_hom` (module `Rational.ElementarySubgroupHom`): a
  homomorphism `a : C ⟶ S` of connected reductive groups maps `C(K)⁺` into `S(K)⁺`.

## Results

* `kernelPoint_comp_hom`: for `mu : 𝔾_m ⟶ C`, `psi : SL₁(D) ⟶ C` and `a : C ⟶ S`,
  `kernelPoint hdeg (mu ≫ a) (psi ≫ a) A w = kernelPoint hdeg mu psi A w ≫ a`. The kernel point
  is the product `mu(w) · psi(w · 1)` and `a` is multiplicative on points.
* `rationalCoeffEquiv_symm_comp_hom`: for `a : C ⟶ S` and a point `x` of `C` over the
  `K`-algebra `K`, the rational point of `S` given by `x ≫ a` is the image under `a` of the
  rational point of `C` given by `x`.
* `kernelPoint_negOne_mem_of_subgroup` (one spin cover). Assumptions: `[Infinite K]`, `D` central
  of dimension 4 with `σ` and `hsym` as in `BinarySpinLift`, a hyperbolic pair `h`, a spin cover
  `π : S ⟶ O(q)`, `hsc`, a simply connected `C`, `c : C ⟶ O(q)` and
  `j : SL₂ × SL₁(D) ⟶ C` with `j ≫ c = AmbientBinaryScheme.isometryHom σ hdim hsym h`, the
  rational point `z_C(-1)` of `C` with
  `z_C = kernelPoint hdeg (upperCocharacter ≫ firstFactor ≫ j) (secondFactor ≫ j)` in `C(K)⁺`,
  and a Levi lift `(mu, psi)` of `h` into `π`. Conclusion: the rational point
  `z(-1) = kernelPoint hdeg mu psi K (-1)` of `S` lies in `S(K)⁺`.

  Proof. Let `a = liftHom π c : C ⟶ S`, so `j ≫ a ≫ π = isometryHom`.
  1. `psi = secondFactor ≫ j ≫ a`. By `normOne_eq`, applied to `(mu, psi)` and the binary Levi
     lift (the norm-one group is connected reductive because `hsc` makes it simply connected),
     `psi = BinarySpinLift.normOne`. This is `liftHom` of `secondFactor ≫ isometryHom`, and
     `secondFactor ≫ j ≫ a` has the same composite with `π`, so `liftHom_unique` identifies
     them.
  2. `mu = upperCocharacter ≫ firstFactor ≫ j ≫ a`. By `scalar_eq`,
     `mu = BinarySpinLift.scalar = upperCocharacter ≫ specialLinear`, and
     `specialLinear = firstFactor ≫ j ≫ a` by `liftHom_unique` for the simply connected `SL₂`.
  3. By `kernelPoint_comp_hom`, `z(-1) = z_C(-1) ≫ a`. So the rational point `z(-1)` is the image
     under `a` of the rational point `z_C(-1)` (`rationalCoeffEquiv_symm_comp_hom`).
  4. `C` and `S` are simply connected, hence semisimple and connected reductive, so
     `parabolicElementarySubgroup_map_le_of_hom` maps `z_C(-1) ∈ C(K)⁺` into `S(K)⁺`.
* `negOneRoot_eq_one`: if `(2 : K) = 0` then `negOneRoot = 1` in `μ₂(K)`, since `-1 = 1`.
* **`spinKernelElementaryLift_of_kneserThreeSpinSubgroup`**: `hsc` and
  `KneserThreeSpinSubgroupStatement` imply `SpinKernelElementaryLiftStatement`. Given the data of
  `SpinKernelElementaryLiftStatement`:
  - if `(2 : K) = 0`, then `z(-1) = z(1) = 1` (`negOneRoot_eq_one`, `kernelPoint_one`), and `1`
    lies in every subgroup;
  - otherwise, take the `Infinite K` instance from
    `Langlands.LocalField.infinite_of_isNonarchimedeanLocalField`, obtain `C`, `c`, `j` from
    `KneserThreeSpinSubgroupStatement` (which assumes `(2 : K) ≠ 0`), and apply
    `kernelPoint_negOne_mem_of_subgroup`.

Together with `SpinKernel.localSpinKneserTits_of_spinKernel` (module `SpinKernelAssembly`) and
`spinLeviLift_of_degreeTwoNormOneSimplyConnected` (module `SpinLeviLift`), this reduces
`LocalSpinKneserTitsStatement` to `hsc`, `SpinKernelGeneratorStatement` and
`KneserThreeSpinSubgroupStatement`.
