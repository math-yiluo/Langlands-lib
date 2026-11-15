# Assembly of the field case of Popescu's theorem

This module contains the final step in the field case of Popescu's theorem,
following the Stacks Project, *Smoothing ring maps*, Theorem 12.1 (tag 07GC).
The resolution lemmas and Lemma 2.8 enter as hypotheses.

## `RegularAlgebra.geometricallyRegular_of_field`

Let `k` be a field and let `Λ` be a regular `k`-algebra (`RegularAlgebra k Λ`:
flat with geometrically regular fibres). Then `Λ` is geometrically regular over
`k` (`GeometricallyRegular k Λ`).

Proof. `RegularAlgebra` asserts geometric regularity of the fibre over the prime
`⊥` of `k`, namely `κ(⊥) ⊗[k] Λ` over `κ(⊥)`.

- The structure map `k → κ(⊥)` is an isomorphism (`Ideal.algEquivResidueFieldOfField`).
  So the fibre is isomorphic to `Λ`, and Noetherianity transfers.
- Let `k'/k` be finite and purely inseparable. Make `k'` a `κ(⊥)`-algebra through
  the inverse isomorphism. Then `k'` is finite over `κ(⊥)`
  (`Module.Finite.of_restrictScalars_finite`) and purely inseparable over it
  (`IsPurelyInseparable.tower_top`). Hence `k' ⊗[κ(⊥)] (κ(⊥) ⊗[k] Λ)` is regular.
  This ring is isomorphic to `k' ⊗[k] Λ` (`Algebra.TensorProduct.cancelBaseChange`),
  and regularity transfers along ring isomorphisms (`IsRegularRing.of_ringEquiv`).

## `fieldCase_of_resolutions`

`SingularIdealFactorizationStatement` (Stacks 07EU), `CharZeroResolutionStatement`
(Stacks 07FE, characteristic zero) and `CharPResolutionStatement` (Stacks 07FJ)
together imply `PopescuFieldCaseStatement`.

Proof (Stacks 07GC, field case). Let `k` be a field, `Λ` Noetherian and regular
over `k`, and `f : A → Λ` a `k`-algebra map with `A` finitely presented.

1. By the previous lemma, `Λ` is geometrically regular over `k`, and in particular
   a regular ring. So every `Λ_q` is a regular local ring.
2. Consider the set of ideals `h_B = √(H_{B/k} Λ)` (`singularRadical k h`) that
   arise from factorizations `A → B → Λ` of `f` with `B` finitely presented over
   `k`. The set contains `h_A`, so it is nonempty. Since `Λ` is Noetherian, it has
   a maximal element `h_B` (`set_has_maximal_iff_noetherian`).
3. Suppose `h_B = Λ`. Then `H_{B/k} Λ = Λ` (`Ideal.radical_eq_top`). Lemma 2.8
   gives a factorization `B → C → Λ` with `C` smooth over `k`, and `A → B → C → Λ`
   is the required factorization.
4. Otherwise choose a minimal prime `q` over `h_B`
   (`Ideal.exists_le_maximal` and `Ideal.exists_minimalPrimes_le`). By
   `CharP.exists'`, `k` has characteristic zero or prime characteristic `p`.
   Lemma 10.3 (characteristic zero, using that `Λ_q` is regular) or Lemma 11.4
   (characteristic `p`, using geometric regularity) resolves `k → B → Λ ⊃ q`. This
   gives `B → C → Λ` with `C` finitely presented and `h_B ⊆ h_C ⊄ q`. Since
   `h_B ⊆ q`, we get `h_C ≠ h_B`, so `h_B < h_C`. The ideal `h_C` comes from the
   factorization `A → C → Λ`, which contradicts the maximality of `h_B`.
