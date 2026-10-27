# Proof of forward propagation of component flatness

`Langlands.Algebra.localApproximationFlatnessPropagation` proves the published
proposition `Langlands.Algebra.LocalApproximationFlatnessPropagationStatement`
with exactly its type. The theorem has the seven universe parameters
`uI,uA,uB,uN,uR,uS,uM`, in that order, and they stay independent. It applies
the auxiliary theorem
`LocalModuleSystem.flat_of_isPrimeLocalization_of_bijective` to the quantified
data. The only transition hypotheses used are `D.IsPrimeLocalization h` and
`Function.Bijective (E.moduleBaseChangeMap h)`. The base actions on `E.obj i`
and `E.obj j` are the `Module.compHom` restrictions bound in the statement.
No other hypothesis is added. The proof depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Write `Rᵢ = D.base i`, `Sᵢ = D.alg i`, `Mᵢ = E.obj i`, the same for `j`, and
`A = D.RingBaseChange h = Sᵢ ⊗[Rᵢ] Rⱼ`. Here `Rⱼ` is an `Rᵢ`-algebra through
`D.baseMap i j h`.

## Generic lemma: localization over an auxiliary algebra

`Langlands.Algebra.flat_of_isLocalizedModule_of_flat` takes the following
data:

- a commutative `R`-algebra `A`;
- `A`-modules `P` and `Q` that are also `R`-modules with scalar towers
  `R → A → P` and `R → A → Q`;
- a submonoid `T` of `A`;
- an `A`-linear map `g : P → Q` with `IsLocalizedModule T g`.

If `P` is flat over `R`, the lemma proves that `Q` is flat over `R`. The base
ring `R` does not change; the localization is taken over `A`.

The proof uses Mathlib's criterion `Module.Flat.iff_lTensor_injectiveₛ`. Let
`N' ⊆ N` be an `R`-submodule with inclusion `ι`. It suffices to show that
`ι.lTensor Q` is injective. Write that map as the `A`-linear
`AlgebraTensorModule.lTensor A Q ι`. By `IsLocalizedModule.map_lTensor`,
this map equals `IsLocalizedModule.map T` applied to
`AlgebraTensorModule.lTensor A P ι`. The two localization maps involved are
`g ⊗ N'` and `g ⊗ N`. Flatness of `P` makes `ι.lTensor P` injective.
`IsLocalizedModule.map_injective` then shows that the localized map is
injective.

## Main argument

`LocalModuleSystem.flat_of_isPrimeLocalization_of_bijective` takes
`hloc : D.IsPrimeLocalization h` and `hbij`, the bijectivity of
`E.moduleBaseChangeMap h`. It assumes `Module.Flat Rᵢ Mᵢ`, using the
statement's `Module.compHom` action, and proves `Module.Flat Rⱼ Mⱼ`. The proof
goes as follows.

1. **Structures.** The proof installs these local structures:
   - the algebras `Rᵢ → Rⱼ` from `D.baseMap i j h` and `Sᵢ → Sⱼ` from
     `D.algMap i j h`;
   - the right `Rⱼ`-algebra structure `Algebra.TensorProduct.rightAlgebra` on
     `A`;
   - the algebra `A → Sⱼ` given by the actual `D.ringBaseChangeMap h`. This is
     the algebra structure that `D.IsPrimeLocalization h` uses.

   Destructuring `hloc` gives a prime `p` of `A` and
   `IsLocalization.AtPrime Sⱼ p`. On `Mⱼ` the proof restricts the actual
   `Sⱼ`-action along `D.algMap i j h` and along `D.ringBaseChangeMap h`.
   Scalar towers are proved for the following triples:
   - `Rᵢ → Sᵢ → Mᵢ`, which holds definitionally;
   - `Sᵢ → A → Sⱼ`, `Sᵢ → A → Mⱼ` and `Rⱼ → A → Mⱼ`, from
     `LocalAlgebraSystem.ringBaseChangeMap_tmul`, which gives
     `s ⊗ r ↦ algMap(s) · fⱼ(r)`, with `r = 1` or `s = 1`;
   - `Sᵢ → Sⱼ → Mⱼ` and `A → Sⱼ → Mⱼ`, which hold definitionally.

2. **The localization map.** `F : Mᵢ →ₗ[Sᵢ] Mⱼ` is the actual transition
   `E.map i j h` viewed as an `Sᵢ`-linear map. It uses the same construction
   as inside `E.moduleBaseChangeMap h`. Then
   `g = F.liftBaseChange A : A ⊗[Sᵢ] Mᵢ →ₗ[A] Mⱼ`, so
   `a ⊗ m ↦ a • E.map i j h m`.

3. **`g` is a base change.** The composite `m ↦ g (1 ⊗ m)` is identified
   with `E.moduleBaseChangeMap h` precomposed with `m ↦ 1 ⊗ m`. This uses
   `moduleBaseChangeMap_tmul` and `liftBaseChange_tmul`. Hence
   `IsBaseChange.of_equiv`, applied to `LinearEquiv.ofBijective` of the
   comparison map, makes this composite an `Sⱼ`-base change of `Mᵢ`.
   `TensorProduct.isBaseChange` makes `m ↦ 1 ⊗ m` an `A`-base change.
   `IsBaseChange.of_comp` then gives `IsBaseChange Sⱼ g`.

4. **`g` is a localization.** Since `Sⱼ` is the localization of `A` at
   `p.primeCompl`, `isLocalizedModule_iff_isBaseChange` turns step 3 into
   `IsLocalizedModule p.primeCompl g`.

5. **The source is `Rⱼ`-flat.**
   `Algebra.IsPushout.cancelBaseChange Rᵢ Rⱼ Sᵢ A Mᵢ` is an `Rⱼ`-linear
   equivalence `A ⊗[Sᵢ] Mᵢ ≃ Rⱼ ⊗[Rᵢ] Mᵢ`. The target of this
   equivalence is `Rⱼ`-flat by Mathlib's base-change instance, using the
   hypothesis on `Mᵢ`. `Module.Flat.of_linearEquiv` transfers flatness to
   `A ⊗[Sᵢ] Mᵢ`.

6. **Conclusion.** The generic lemma, applied with base `Rⱼ`, auxiliary
   algebra `A`, `T = p.primeCompl` and the map `g`, proves that `Mⱼ` is
   `Rⱼ`-flat. The `Rⱼ`-action on `Mⱼ` used here is the statement's
   `Module.compHom` restriction along `algebraMap Rⱼ Sⱼ`.

The ring map `D.ringBaseChangeMap h` is never assumed or proved bijective.
Only the prime-localization property is used. No approximation, colimit,
finiteness, Noetherian, injectivity or transition-flatness property is used.

## Provenance

This is an internal proof of the internal proposition described in the
statement's Markdown. That Markdown cites Stacks 00QX clauses (5) and (6) as
the source of the two transition conditions. The route is the derived argument
outlined there. The Lean proof realizes the localization step by the generic
lemma above instead of by a filtered-colimit description of module
localization. It identifies `A ⊗[Sᵢ] Mᵢ` with `Rⱼ ⊗[Rᵢ] Mᵢ` by Mathlib's
`IsPushout.cancelBaseChange`, with no explicit tensor associativity. All
other ingredients are existing Mathlib results at the pinned commit and the
published `LocalApproximationSystem` interface.
