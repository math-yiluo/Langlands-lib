# Prime localization of the composite tower transition

This module proves the composite prime-localization condition of a synchronized tower from
the two adjacent ones. The result holds for every `LocalAlgebraTowerSystem`, not only for the
tower built in `Langlands.Algebra.LocalAlgebraTowerConstruction`. Stacks 00R7 states the
three localization conditions separately. The published `LocalAlgebraTowerSystem.IsApproximation`
keeps the composite condition `D.rt.IsPrimeLocalization` as a separate clause, and this
module derives it.

## Abstract pasting lemma

`LocalAlgebraTowerApproximation.isLocalization_atPrime_tensor_comp`. All tensor products here
are of commutative rings. Let `A, A', B, B', C, C'` be commutative rings with `C'` local, and
suppose the following:

- algebra maps `A → A'`, `A → B`, `B → C`, `A → C` with `IsScalarTower A B C`, and
  `A' → B'`, `B → B'`, `B' → C'`;
- `hB`: the two composites `A → B → B'` and `A → A' → B'` agree;
- a ring map `fC : C →+* C'`;
- a ring map `φ₁ : B ⊗[A] A' →+* B'` with `φ₁ (b ⊗ a) = b * a`, the factors being taken in
  `B'`;
- a ring map `φ₂ : C ⊗[B] B' →+* C'` with `φ₂ (c ⊗ b) = fC c * b`, with `b` taken in `C'`;
- a ring map `φ₃ : C ⊗[A] A' →+* C'` with `φ₃ (c ⊗ a) = fC c * a`, where `a` is mapped to
  `C'` through `B'`;
- submonoids `M` of `B ⊗[A] A'` and `N` of `C ⊗[B] B'`;
- `hM`: `B'` is the localization of `B ⊗[A] A'` at `M`, with the algebra given by `φ₁`;
- `hN`: `C'` is the localization of `C ⊗[B] B'` at `N`, with the algebra given by `φ₂`.

Then, with the algebra structure given by `φ₃`, `C'` is the localization of `C ⊗[A] A'` at the
prime ideal `(maximalIdeal C').comap φ₃`.

### Proof

The proof introduces two ring maps:

- `ψPX : B ⊗[A] A' → C ⊗[A] A'`, the tensor product of `B → C` with the identity;
- `ψXY : C ⊗[A] A' → C ⊗[B] B'`, which sends `c ⊗ a` to `c ⊗ a`, with `a` mapped to `B'`. It
  is well defined by `hB`.

The proof checks the scalar towers relating these maps, `φ₁`, `φ₂` and `φ₃` on pure
tensors, and then argues as follows:

1. The square formed by `B → C`, `B → B ⊗[A] A'` and `C → C ⊗[A] A'` is a pushout, by
   `Algebra.IsPushout.tensorProduct_tensorProduct`. The large square formed by `B → C` and
   `B → B' → C ⊗[B] B'` is also a pushout. Pasting with `Algebra.IsPushout.comp_iff` shows
   that the square formed by `B ⊗[A] A' → B'` and `C ⊗[A] A' → C ⊗[B] B'` is a pushout.
2. `Algebra.isLocalization_iff_isPushout` and `hM` then make `C ⊗[B] B'` the localization of
   `C ⊗[A] A'` at the image of `M`.
3. By `IsLocalization.localization_localization_isLocalization` and `hN`, `C'` is a
   localization of `C ⊗[A] A'` at some submonoid, with the algebra given by `φ₃`.
4. Since `C'` is local, the project lemma `isLocalization_atPrime_of_local_target`
   (`Langlands.Algebra.PrimeLocalizationCriterion`) turns this into the localization at
   the inverse image of the maximal ideal.

## Tower result

`LocalAlgebraTowerSystem.rt_isPrimeLocalization D h hrs hst`. Let `D` be any synchronized
tower and let `i ≤ j`. If `D.rs.IsPrimeLocalization h` and `D.st.IsPrimeLocalization h`, then
`D.rt.IsPrimeLocalization h`. The composite locality instance is
`LocalAlgebraTowerSystem.composite_local R S T`.

The proof applies the pasting lemma with the following data:

| Pasting lemma | Tower data |
| --- | --- |
| `A`, `A'` | `D.rs.base i`, `D.rs.base j` |
| `B`, `B'` | `D.rs.alg i`, `D.rs.alg j` |
| `C`, `C'` | `D.top i`, `D.top j` |
| `fC` | `D.topMap i j h` |
| `φ₁` | the actual `D.rs.ringBaseChangeMap h` |
| `φ₂` | the actual `D.st.ringBaseChangeMap h` |
| `φ₃` | the actual `D.rt.ringBaseChangeMap h` |
| `M`, `N` | the prime complements supplied by `hrs` and `hst` |

`hB` is `D.rs.map_comm`. The three pure-tensor formulas hold by `rfl`. The prime that
witnesses `D.rt.IsPrimeLocalization h` is the inverse image of the maximal ideal of `D.top j`
under `D.rt.ringBaseChangeMap h`.
