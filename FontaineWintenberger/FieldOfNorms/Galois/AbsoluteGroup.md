# The absolute Galois groups of an APF extension and of its field of norms

Module `FontaineWintenberger.FieldOfNorms.Galois.AbsoluteGroup`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy the library's class `IsPerfectResidueLocalField`, and let `L/K` be an infinite separable APF extension, with field of norms `X = FieldOfNorms K L`. The file constructs an isomorphism of topological groups, for the Krull topologies, between the absolute Galois group of `L` and that of `X`. The file presents this as Wintenberger's Corollary 3.2.3.

## Definitions

- `krullAutCongr e`: for an isomorphism `e : A ≃ₐ[F] B` of field extensions of `F`, conjugation by `e` as an isomorphism of topological groups `(A ≃ₐ[F] A) ≃ₜ* (B ≃ₐ[F] B)`.
- `separableClosureEquiv K L Ω`: for a separable closure `Ω` of `K` containing `L`, an `L`-isomorphism `SeparableClosure L ≃ₐ[L] Ω`.
- `RelFieldOfNorms.separableClosureEquiv`: an `X`-isomorphism from `RelFieldOfNorms K L Ω` to `SeparableClosure X`.
- `RelFieldOfNorms.absoluteGaloisEquiv`: `(Ω ≃ₐ[L] Ω) ≃ₜ* (SeparableClosure X ≃ₐ[X] SeparableClosure X)`.
- `FieldOfNorms.absoluteGaloisEquivOfSepClosure`: the same with `SeparableClosure L` on the left, computed through a chosen `Ω`.
- `FieldOfNorms.absoluteGaloisEquiv`: `(SeparableClosure L ≃ₐ[L] SeparableClosure L) ≃ₜ* (SeparableClosure X ≃ₐ[X] SeparableClosure X)`, obtained by taking `Ω = SeparableClosure L`.

## Results

- `autCongr_mem_fixingSubgroup_iff`: `e.autCongr σ` fixes an intermediate field `D` of `B/F` exactly when `σ` fixes the image of `D` under `e⁻¹`.
- `continuous_autCongr_krull`: `e.autCongr` is continuous for the Krull topologies; no normality is assumed.
- `krullAutCongr_toMulEquiv`, `krullAutCongr_apply`: the underlying group isomorphism is Mathlib's `autCongr`, with `krullAutCongr e σ x = e (σ (e⁻¹ x))`.
- `closure_isSepClosure`: a separable closure `Ω` of `K` containing `L` is a separable closure of `L`.
- `RelFieldOfNorms.absoluteGaloisEquiv_apply`, `FieldOfNorms.absoluteGaloisEquivOfSepClosure_apply`: under the identification `RelFieldOfNorms.separableClosureEquiv`, the image of `σ` acts as `RelFieldOfNorms.mapEquiv` of `σ`.

## Proof

The main input comes from two imported files: `RelFieldOfNorms.isSepClosure`, which says that the relative field of norms `RelFieldOfNorms K L Ω` is a separable closure of `X`, and `RelFieldOfNorms.krullEquiv`, the isomorphism of topological groups between `Ω ≃ₐ[L] Ω` and the automorphism group of `RelFieldOfNorms K L Ω` over `X`. The present file composes `krullEquiv` with conjugation by comparison isomorphisms of separable closures, which are homeomorphisms by `continuous_autCongr_krull`.

## To watch for

- The comparison isomorphisms of separable closures (`IsSepClosure.equiv`) are chosen, not canonical, so the resulting isomorphism of Galois groups depends on these choices up to conjugation.
- `SeparableClosure` is Mathlib's; `RelFieldOfNorms` is the library's own construction.
- `L/K` must be infinite (`Fact (¬ Module.Finite K L)`) and APF, as instances.
- `FieldOfNorms.absoluteGaloisEquiv` has no accompanying formula in this file; the formulas are stated for the versions with a chosen `Ω`.

## Reference

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3; Corollary 3.2.3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Galois/AbsoluteGroup.lean` (SHA-256 of the source file `e8aaa9aa5ed36606e278dda0546b25dbad616c7d93644874d6b8aa7aae61e751`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
