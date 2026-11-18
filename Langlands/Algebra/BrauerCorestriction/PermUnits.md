# Permutation units in tensor powers of central simple algebras

Let `B` be a finite-dimensional central simple algebra over a field `K`, with `K` and `B` in the same universe, and let `E` be a finite type. Write `C = ⨂_K (σ : E), B`. This module constructs a group homomorphism

`permUnits K B E : Equiv.Perm E →* Cˣ`

such that conjugation by `permUnits K B E π` permutes the tensor factors of `C` along `π` (`permUnits_conj`). The automorphisms permuting the factors are thus inner, and the implementing units can be chosen compatibly with composition. This is the key input for the formula `Cor ∘ Res = [L : K]`. There is no restriction on the characteristic.

## Public declarations

Everything is in the namespace `Langlands.BrauerCorestriction`.

**Permuting tensor factors.**

- `permAlgEquiv K E B π` is the `K`-algebra automorphism of `⨂_K (σ : E), B` that reindexes the factors along `π`. It sends `⨂ b_σ` to `⨂ b_{π⁻¹ σ}` (`permAlgEquiv_tprod`).
- `finrank_piTensor_const` computes `finrank K (⨂_E B) = (finrank K B)^|E|`.

**The split model.**

- `SF K B` is the Library's finite Galois splitting field `finiteGaloisSplittingField K B`, with chart `χ : SF ⊗_K B ≃ M_d(SF)`, where `d = reducedDegree K B`.
- `MatB K B` and `MatE K B E` are the matrix types of sizes `d` and `E → Fin d`.
- `chartLin K B : B →ₗ[K] M_d(SF)` is `b ↦ χ(1 ⊗ b)` (`chartLin_apply`). It is unital and multiplicative (`chartLin_one`, `chartLin_mul`).
- `splitRep K B E : C →ₐ[K] M_{E→Fin d}(SF)` is `⨂ b_σ ↦ Kronecker(χ(1 ⊗ b_σ))` (`splitRep_tprod`).
- `splitTheta K B E : SF ⊗_K C →ₐ[SF] M_{E→Fin d}(SF)` is its `SF`-linear extension (`splitTheta_tmul`).
- `splitTheta_bijective` and `splitThetaEquiv K B E` give the resulting isomorphism (`splitThetaEquiv_apply`). The instance The imported `Langlands.CentralSimple.reducedDegree_neZero` records `d ≠ 0`.

**Permutations in the split model.**

- `splitRep_perm` and `splitRep_perm_eq_conj` describe permuting the factors in the split model: it is reindexing rows and columns by `(indexPerm π)⁻¹`, that is, conjugation by the permutation matrix `permMatrix K B E π`.
- `permMatrix_mul` and `permMatrix_one` say that these permutation matrices are multiplicative.

**Galois action.**

- `galTensor K B E h` is the action `h ⊗ 1` of `h ∈ Gal(SF/K)` on `SF ⊗_K C` (`galTensor_tmul`).
- `chartTwist K B h` is the `SF`-algebra automorphism `χ ∘ (h ⊗ 1) ∘ χ⁻¹ ∘ (h⁻¹ on entries)` of `M_d(SF)`.
- `chartUnit K B h` is a unit `a_h` implementing `chartTwist K B h`, chosen with the Library's matrix Skolem–Noether theorem `Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv`. It satisfies `χ((h ⊗ 1) y) = a_h · h(χ y) · a_h⁻¹` (`chart_galois`).
- `kronUnit K B E h` is the Kronecker power of `a_h`.
- `kronecker_map_galois`, `splitRep_galois` and `splitTheta_galois` say that the transported Galois action on `M_{E→Fin d}(SF)` is `X ↦ A_h · h(X) · A_h⁻¹`, where `A_h` is `kronUnit K B E h`.
- `permMatrix_galois`: permutation matrices are fixed by this transported action.

**Descent of the units.**

- `galTensorAction K B E` packages `h ↦ h ⊗ 1` as a semilinear action by ring automorphisms, in the sense of `GaloisDescent`.
- `tmul_one_injective` says that `c ↦ 1 ⊗ c` is injective.
- `exists_tmul_eq_of_fixed`: every Galois-fixed element of `SF ⊗_K C` is `1 ⊗ c` for some `c ∈ C`.
- `permMatrix_preimage_fixed`: the preimage of each permutation matrix is Galois-fixed.
- `permUnitVal K B E π ∈ C` is the element with `1 ⊗ permUnitVal π = splitTheta⁻¹(permMatrix π)` (`tmul_permUnitVal`). `one_tmul_mul` records `1 ⊗ (a b) = (1 ⊗ a)(1 ⊗ b)`.
- `permUnitHom K B E : Equiv.Perm E →* C` is the resulting monoid homomorphism. `permUnits K B E` is the corresponding homomorphism into units (`permUnits_val`).
- `permUnits_conj` states `permUnits π · c · (permUnits π)⁻¹ = permAlgEquiv K E B π c`.

## Implemented proof

**The split model is an isomorphism.** `C` is central simple (`CentralSimple`), so `SF ⊗_K C` is a simple ring (Library `isSimpleRing_baseChange`) and `splitTheta` is injective. Both sides have dimension `(d²)^|E|`, using the Library identity `finrank K B = d · d`, so `splitTheta` is bijective.

**Permutations and Galois action in the split model.** Both are checked on pure tensors with the Kronecker lemmas of `PiMatrixKronecker`, then extended by additivity and `K`-linearity.

- *Permutations.* Permuting tensor factors becomes reindexing rows and columns (`kroneckerMultilinear_reindex`), which is conjugation by a permutation matrix (`permUnit_conj`).
- *Galois action.* The automorphism `chartTwist` is the composite of `χ⁻¹`, `h ⊗ 1` on `SF ⊗ B`, `χ` and `h⁻¹` on matrix entries (`AlgEquiv.ofRingEquiv`). It is `SF`-linear, hence inner by matrix Skolem–Noether. Since `(h ⊗ 1)(1 ⊗ b) = 1 ⊗ b`, each Kronecker factor `χ(1 ⊗ b)` equals `a_h · h(χ(1 ⊗ b)) · a_h⁻¹`. Applying `h` to entries commutes with the Kronecker map, and the Kronecker map is multiplicative, so the pure-tensor case follows.

**Fixed permutation matrices.** A permutation matrix has entries `0` and `1`, so `h` fixes it entrywise. It also commutes with the Kronecker power `A_h`: conjugating `A_h` by `permMatrix π` reindexes the constant family `σ ↦ a_h`, which leaves it unchanged. Hence `A_h · h(P) · A_h⁻¹ = P`, and the preimage under `splitTheta` is fixed by every `h ⊗ 1`.

**Descent.** By `GaloisDescent`, the fixed subalgebra of `galTensorAction` has `K`-dimension `finrank SF (SF ⊗_K C) = finrank K C`. The image of `C` under `c ↦ 1 ⊗ c` lies in it and has the same dimension, because the map is injective (`Algebra.TensorProduct.includeRight_injective`). So the two subspaces coincide (`Submodule.eq_of_le_of_finrank_eq`). This produces `permUnitVal`.

**Group law and conjugation.** Both are checked after applying the injective map `c ↦ 1 ⊗ c` and the bijective `splitThetaEquiv`. They become `P_{πρ} = P_π P_ρ`, `P_1 = 1` and `P_π · splitRep(c) · P_π⁻¹ = splitRep(permAlgEquiv π c)`.

## Sources and scope

That the permutation automorphisms of a tensor power of a central simple algebra are inner, compatibly with composition, is the ingredient behind the norm (corestriction) property `N_{K/F}(A_K) ∼ A^{⊗[K:F]}`. M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), Proposition (3.13)(5), printed p. 37 / PDF p. 60, with proof on printed pp. 38–39 / PDF pp. 61–62, treats the quadratic case. There the switch map of `A ⊗ A` is inner by the Goldman element `g` with `g² = 1` (Proposition (3.6)). For arbitrary degree they refer to Draxl.

The construction here is an internal derivation for an arbitrary finite index set. The units are the permutation matrices of a split model over the Library's finite Galois splitting field, descended to `K` with Galois descent and the Library's matrix Skolem–Noether theorem. No Goldman element, reduced trace or presentation of the symmetric group is used.
