# Archimedean norm images and approximation by local norms

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field and L/K a finite extension. This file shows that at every infinite place the positive units are norms from the local algebra K_v ⊗_K L. It then combines this with weak approximation at finitely many finite places: when L/K is Galois, an idele can be corrected by a principal idele so that it becomes a local norm at those finite places and at all infinite places.

## Main definitions and results

- `exists_infinitePositiveSubgroup_nthRoot`: at an infinite place v and for n > 0, every element of `RayClass.infinitePositiveSubgroup v` has an n-th root in the units of the completion K_v. At a real place this subgroup consists of the positive reals and the root is a real power. At a complex place every unit qualifies and the root comes from algebraic closedness.
- `infiniteTensorDetNorm v`: the determinant norm (`Algebra.norm`) from the units of K_v ⊗_K L to K_vˣ. `infiniteTensorNormSubgroup v` is its image.
- `infinitePositiveSubgroup_le_infiniteTensorNormSubgroup`: the positive subgroup is contained in this image. Write x = yⁿ with n = [L : K]; then x is the norm of the scalar y.
- `chosenFinitePlaceLocalNormSubgroup_eq_top_of_splitsCompletely`: for L/K Galois, if a finite place v splits completely (`FinitePlaceSplitsCompletely`), the chosen local norm subgroup at v is all of K_vˣ, because the local degree is 1.
- `exists_principal_quotient_mem_localNormSubgroups`: for L/K Galois, a finite set S of finite places and an idele a, there is x ∈ Kˣ such that a·x⁻¹ lies in the chosen local norm subgroup at every v ∈ S and in `infiniteTensorNormSubgroup` at every infinite place. The proof applies the imported approximation theorem `IdeleGroup.exists_principal_quotient_mem_openAllLocalSubgroups_finset` to these open subgroups and the open positive subgroups.
- `exists_principal_quotient_locallyNormEverywhere_of_splitsOutside`: if moreover every finite place outside S splits completely, the same x makes a·x⁻¹ a local norm at every finite and every infinite place.

## Points to watch

- The two kinds of places use different local norms. At infinite places the norm comes from the algebra K_v ⊗_K L. At finite places it comes from the single completion L_w chosen in `chosenFinitePlaceLocalNormSubgroup`.
- At infinite places the file proves only that the positive subgroup is contained in the norm image, not a description of the image.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/NormApproximation/InfinitePlaces.lean`: the Lean file is the source byte for byte (SHA-256 `5edb4f3ef6e4b5687573dc2acc028d7daee43508c85dd77fd92f61161d325f22`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
