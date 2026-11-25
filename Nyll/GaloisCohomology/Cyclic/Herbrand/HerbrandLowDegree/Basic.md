# Concrete Tate groups in degrees 0 and −1

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group `G` acting on a commutative group `A` written multiplicatively (`MulDistribMulAction`), the file builds the library's models of Tate cohomology in degrees 0 and −1: `Ĥ⁰ = A^G / N_G A` and `Ĥ⁻¹ = ker N_G / I_G A`, where `I_G A` is the image of `a ↦ σ • a · a⁻¹` for a chosen `σ : G`. It supplies their interface, vanishing criteria, transport along isomorphisms, vanishing for the right-regular induced module, and the equality of the two orders for finite `A`.

## Main definitions

- `tateNorm G A a = ∏ g, g • a` and `sigmaMinusOne G A σ a = σ • a * a⁻¹`, with homomorphism versions `tateNormHom` and `sigmaMinusOneHom`.
- `fixedSubgroup`, `tateNormSubgroup` (image of the norm), `normKernelSubgroup`, and `augmentationSubgroup G A σ` (image of `σ − 1`).
- `HerbrandH0 G A` and `HerbrandHMinusOne G A σ`: the two quotients, commutative groups, finite when `A` is. Interface: `mk`, `mk_surjective`, `mk_eq_one_iff`, `mk_eq_mk_iff_div_mem`, `inductionOn`, `liftOn`, `lift`, `equiv`.
- `rightRegularFunctionMulDistribMulAction`: `G` acting on `G → B` by `(g • f) x = f (x * g)`, with `rightRegularFunctionHerbrandH0` and `rightRegularFunctionHerbrandHMinusOne`.

## Main results

- `augmentationSubgroup_le_normKernelSubgroup` and `tateNormSubgroup_le_fixedSubgroup`, so that both quotients are defined.
- `sigmaMinusOneHom_ker_eq_fixedSubgroup`: if `σ` generates `G`, the kernel of `σ − 1` is `A^G`.
- `herbrandH0_subsingleton_iff_fixed_le_tateNormSubgroup` and `herbrandHMinusOne_subsingleton_iff_normKernel_le_augmentationSubgroup`: the vanishing criteria.
- `herbrandH0_subsingleton_of_mulEquiv`, `herbrandHMinusOne_subsingleton_of_mulEquiv`: vanishing transported along a `G`-equivariant isomorphism.
- `rightRegularFunction_herbrandH0_subsingleton` (any finite `G`) and `rightRegularFunction_herbrandHMinusOne_subsingleton` (`σ` generates `G`): both groups of `G → B` vanish. Variants cover modules isomorphic to `G → B`, also additive ones wrapped in `Multiplicative`.
- `herbrand_finite_module_card_eq`: for finite `A` and `σ` generating `G`, `#Ĥ⁰ = #Ĥ⁻¹`.

## Proofs

For finite `A`, the first isomorphism theorem for `N_G` and for `σ − 1` gives `#A^G · #I_G A = #ker N_G · #N_G A`; writing `#A^G = #Ĥ⁰ · #N_G A` and `#ker N_G = #Ĥ⁻¹ · #I_G A` and cancelling gives the equality. For `G → B`, a fixed function is constant and is the norm of the function supported at `1`; a function with product `1` is a coboundary, built from partial products along `1, σ, σ², …` indexed through `rightRegularCyclicIndex`.

## Points to watch

- `HerbrandH0` and `HerbrandHMinusOne` are the library's own quotient groups, not Mathlib's group cohomology.
- `G` is only assumed finite. Cyclicity enters as the hypothesis `hgen : ∀ g, g ∈ Subgroup.zpowers σ` where it is needed; `I_G A`, hence `Ĥ⁻¹`, is defined from the single element `σ`.
- In the right-regular model `G` acts on `G → B` by translation alone; no action of `G` on `B` is used.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `7a21891f0446f93c8577c146b13681ba1dac31f1c9bf381f00d36341883038f2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
