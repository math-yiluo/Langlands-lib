# Prime-localization preservation for the actual upper residue-fibre transition: proof

`Langlands.Algebra.localTowerResidueFiberRingBaseChange` proves the published
proposition `Langlands.Algebra.LocalTowerResidueFiberRingBaseChangeStatement`.
Its complete type is exactly that proposition, with the seven independent
universe parameters `uI uA uB uC uR uS uT` in the statement's order. The
statement pair and all of its imports are unchanged. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

The module imports the statement, the published package
`Langlands.Algebra.LocalTowerResidueFiberSystem` (for the instance
`LocalAlgebraTowerSystem.upperFiberRing_isLocalRing`, which says that `G_j` is
local), and `Langlands.Algebra.PrimeLocalizationCriterion` (for
`isLocalization_atPrime_of_local_target`).

## What is proved

Notation as in the statement: `R_i = D.rs.base i`, `S_i = D.rs.alg i`,
`T_i = D.top i`, `κ_i = ResidueField R_i`, `F_i = D.rs.FiberRing i =
S_i ⊗[R_i] κ_i` and `G_i = D.UpperFiberRing i = T_i ⊗[R_i] κ_i`, with `G_i` an
`F_i`-algebra by the published scoped instance `ResidueFiberTensor.upperAlgebra`.

For every nonempty directed preorder `ι`, local rings `R → S → T` with local
structure maps, every `D : LocalAlgebraTowerSystem ι R S T` and `h : i ≤ j`:
if `D.st.IsPrimeLocalization h` holds, then, with `F_j` an `F_i`-algebra by
`(D.rs.fiberRingMap h).toAlgebra` and `G_j` an algebra over
`G_i ⊗[F_i] F_j` by `(D.upperFiberBaseChangeMap h).toAlgebra`, the prime

```text
p = (maximal ideal of G_j).comap (D.upperFiberBaseChangeMap h)
```

satisfies `IsLocalization.AtPrime G_j p`. The map is the actual published
`D.upperFiberBaseChangeMap h`; no comparison isomorphism replaces it. The only
hypothesis used is `D.st.IsPrimeLocalization h`. No other hypothesis is added.

## Provenance and relation to the source

The source is the passage of the proof of Stacks Lemma 10.128.8, tag
**00R7**, recorded in the statement's Markdown: registered source
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, file
`00R7.html`, lines 224–236. The source states without detail that the fibre
transition `S'_λ/𝔭_λS'_λ ⊗_{S_λ/𝔭_λS_λ} S_μ/𝔭_μS_μ → S'_μ/𝔭_μS'_μ` is a
localization, because `S'_λ ⊗_{S_λ} S_μ → S'_μ` is one. The proof here supplies
that step for the published tensor presentation of the fibres. It follows the
route suggested in the statement's Markdown: the fibre transition is a base
change of the original transition along `S_j → F_j`, a base change of a
localization is a localization, and the locality of `G_j` upgrades the result
to a localization at a prime. The identification with a base change is made
by pasting pushout squares (Mathlib's `Algebra.IsPushout`), not by explicit
tensor cancellation isomorphisms, and it is checked against the actual map on
generators.

## Structure of the module

### 1. A generic pasting lemma

`ResidueFiberRingBaseChangeProof.isLocalization_atPrime_of_pushout_squares`
works with abstract commutative rings `S₀ T₀ F₀ G₀ S₁ T₁ F₁ G₁ A Q` and assumes:

- `G₀` is a pushout of `T₀` and `F₀` over `S₀`, and `G₁` is a pushout of `T₁`
  and `F₁` over `S₁` (`Algebra.IsPushout S₀ T₀ F₀ G₀` and
  `Algebra.IsPushout S₁ T₁ F₁ G₁`);
- `A` is a pushout of `S₁` and `T₀` over `S₀`, and `Q` is a pushout of `F₁`
  and `G₀` over `F₀`;
- algebra structures `S₀ → S₁`, `F₀ → F₁`, `A → T₁` and `Q → G₁`, with `T₁`
  the localization of `A` at a submonoid `M`, and `G₁` local;
- four equations on generators: `F₀ → F₁` and `S₀ → S₁` are compatible
  (`hSF`), `A → T₁` restricts to `S₁ → T₁` (`hS`), `Q → G₁` restricts to
  `F₁ → G₁` (`hF`), and on `T₀` the composite `T₀ → G₀ → Q → G₁` equals
  `T₀ → A → T₁ → G₁` (`hT`).

The conclusion is that `G₁` is the localization of `Q` at the inverse image of
its maximal ideal under `Q → G₁`.

The proof installs the composite algebra structures `S₀ → F₁`, `S₀ → Q`,
`T₀ → Q` and `S₁ → Q` with their scalar towers. It defines the comparison
`A → Q` as `Algebra.pushoutDesc` of `S₁ → Q` and `T₀ → Q` out of the pushout
`A`, and records its scalar towers from `Algebra.pushoutDesc_left`,
`Algebra.pushoutDesc_right` and `AlgHom.commutes`. Then three applications of
Mathlib's pasting law `Algebra.IsPushout.comp_iff` give:

1. `Q` is a pushout of `F₁` and `T₀` over `S₀` (paste the `G₀` square with the
   `Q` square);
2. `Q` is a pushout of `F₁` and `A` over `S₁` (cancel the `A` square from
   step 1);
3. `G₁` is a pushout of `T₁` and `Q` over `A` (cancel the square of step 2
   from the `G₁` square).

Step 3 needs the scalar tower `A → Q → G₁`, that is, the two maps `A → G₁`
through `T₁` and through `Q` agree. This is proved by induction over the
pushout `A` (`IsBaseChange.inductionOn`): on `T₀` it is `hT`, on scalars from
`S₁` it follows from `hS` and `hF`, and it is additive. Mathlib's
`Algebra.isLocalization_iff_isPushout` turns step 3 into the statement that
`G₁` is the localization of `Q` at the image of `M`. Finally the published
`isLocalization_atPrime_of_local_target` of `PrimeLocalizationCriterion`
replaces this submonoid by the complement of the inverse image of the maximal
ideal, since `G₁` is local.

### 2. The component pushout squares

Two short lemmas in the same namespace treat the published upper tensor-ring
map `ResidueFiberTensor.upperMap R S K T : S ⊗[R] K → T ⊗[R] K` for any
algebras `R → S → T` and `R → K`:

- `upperMap_isScalarTower`: with the published `upperAlgebra`, the left
  `S`-actions give `IsScalarTower S (S ⊗[R] K) (T ⊗[R] K)` (by `rfl` on
  elements);
- `upperMap_isPushout`: the square `S → T`, `S → S ⊗[R] K` with corner
  `T ⊗[R] K` is a pushout. This is Mathlib's
  `Algebra.IsPushout.tensorProduct_tensorProduct`, whose hypothesis is that
  `upperMap` fixes `1 ⊗ a`.

They are made local instances only inside this module.

### 3. The concrete theorem

`localTowerResidueFiberRingBaseChange` introduces the data and the hypothesis,
installs the two algebra structures of the statement, and takes the
`S_i`-algebra structure `(D.rs.algMap i j h).toAlgebra` on `S_j`, which is the
one used in `D.st.RingBaseChange h`. From `D.st.IsPrimeLocalization h` it
obtains a prime `p'` of `T_i ⊗[S_i] S_j` with `T_j` the localization of
`T_i ⊗[S_i] S_j` at `p'.primeCompl`, for the algebra
`(D.st.ringBaseChangeMap h).toAlgebra`. It then applies the generic lemma
with

```text
S₀ = S_i, T₀ = T_i, F₀ = F_i, G₀ = G_i,
S₁ = S_j, T₁ = T_j, F₁ = F_j, G₁ = G_j,
A = D.st.RingBaseChange h = T_i ⊗[S_i] S_j,
Q = G_i ⊗[F_i] F_j,    M = p'.primeCompl.
```

The algebra structures are the published ones: `F_i → F_j` is
`D.rs.fiberRingMap h`, `F_k → G_k` is `upperAlgebra` (the map `D.fiberHom k`),
`A → T_j` is `D.st.ringBaseChangeMap h`, and `Q → G_j` is
`D.upperFiberBaseChangeMap h`. The remaining structures are Mathlib's tensor
product algebras (left, base and right algebras). The pushout hypotheses for
`G_i` and `G_j` are `upperMap_isPushout`; those for `A` and `Q` are found by
instance inference (Mathlib's `TensorProduct.isPushout'`). Locality of `G_j` is the
published instance `upperFiberRing_isLocalRing`.

The four generator equations are checked with the published pure-tensor
formulas:

- `hSF`: `D.rs.fiberRingMap h (s ⊗ 1) = D.rs.algMap i j h s ⊗ 1`, by
  `fiberRingMap_tmul` and `map_one` for the residue map;
- `hS`: `D.st.ringBaseChangeMap h (1 ⊗ s) = algebraMap S_j T_j s`, by
  `ringBaseChangeMap_tmul`;
- `hF`: `D.upperFiberBaseChangeMap h (1 ⊗ f) = D.fiberHom j f`, by
  `upperFiberBaseChangeMap_tmul`;
- `hT`: `D.upperFiberBaseChangeMap h ((t ⊗ 1) ⊗ 1)` and
  `D.st.ringBaseChangeMap h (t ⊗ 1) ⊗ 1` both equal `D.topMap i j h t ⊗ 1`, by
  `upperFiberBaseChangeMap_tmul`, `upperFiberRingMap_tmul` and
  `ringBaseChangeMap_tmul`.

The witness prime is the inverse image of the maximal ideal of `G_j` under
`D.upperFiberBaseChangeMap h`; its primality is found by instance inference
(Mathlib's `Ideal.comap_isPrime`).
