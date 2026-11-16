# The lifting argument over the one-dimensional points of a chart

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteStar`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.CompleteLocal`. This module supports the proof of
Step 2a of Murre's induction (`MurreCompleteLocalStepStatement`, Bourbaki exp. 294, Case I,
Step 2a). It contains the step where condition (F7) is used: it controls the chart `Spec B` at
the points `w` with `dim L/P_w = 1`, which are the closed points of the part of `Spec B` over the
punctured spectrum.

## Two-point local rings (section `TwoPoint`)

Let `A` be a local ring and `P` a prime. Suppose `P` is not maximal, is contained in every prime,
and every prime other than `P` is maximal.

* `twoPoint_ringKrullDim`: `ringKrullDim A = 1`. Use `Order.krullDim_le_one_iff` (each point is
  minimal or maximal) and `Order.one_le_krullDim_iff` (`P < m`).
* `twoPoint_associatedPrimes`: suppose `A` is noetherian and the elements outside `P` are
  non-zero-divisors. Then `associatedPrimes A A = {P}`. An associated prime is `ann(x)` for some
  `x` (`isAssociatedPrime_iff`). If it were `m`, it would contain an element of `m \ P`, forcing
  `x = 0`. The set of associated primes is nonempty (`associatedPrimes.nonempty`).
* `twoPoint_isGenericPoint`: `P` is the generic point of `Spec A`.

## Helpers

* `homR_injective`: `homR` is injective on `R`-algebra maps (`Spec` is faithful).
* `algHomOver_towerIso'`: `algHomOver` of an `A`-algebra map, transported by `towerIso`, is
  `homR` of the same map viewed as an `R`-algebra map.
* `isLocalHom_of_finite`: a finite algebra over a local ring that is itself a local ring has
  local structure map (`Ideal.IsMaximal.under`).
* `liftsTo_of_tower`: (F7)'s hypothesis `LiftsTo` for an element pulled back from `ovR` along
  `towerIso`, restated with `ovR` and `homR`.
* `ProRep F ξB`: pro-representability of `ξB ∈ F(Spec B)` on complete local noetherian
  `R`-algebras, in the form proved by `chart_lift_complete`.

## The lifting argument (section `Star`)

Let `R` be complete local noetherian and `L` a local noetherian `R`-algebra, finite and formally
unramified over `R`. Let `π : L → B` be surjective with kernel `I`. Let `ξB ∈ F(Spec B)` be a
monomorphism and pro-representable. Let `A` be a local artinian `R`-algebra and `β : L → A` an
`R`-algebra map, with `P = β⁻¹(m_A)`. Assume:

* `P ≠ m_L`, and every prime strictly containing `P` is `m_L`;
* every `a ∈ A` satisfies `a β(s) = β(r)` with `β(s)` a unit;
* `I ⊆ P`.

Let `v ∈ F(Spec A)` and `βb : B → A/IA` with `βb ∘ π = mk ∘ β` and `v|_{A/IA} = ξB ∘ βb`.

* `star_step`: if moreover `β(p) β(i) = 0` for `p ∈ P` and `i ∈ I`, then `I ⊆ ker β`.

  Proof. Put `A1 = L/ker β`. It embeds into `A` by `ι` (`Ideal.kerLiftAlg`). Let
  `P1 = ι⁻¹(m_A)`.
  * Primes of `A1`: `P1` is nilpotent, so it lies in every prime. A prime other than `P1` pulls
    back to a prime of `L` strictly above `P`, so it is maximal. Elements outside `P1` are
    non-zero-divisors, since `ι` is injective and they map to units. So `A1` has dimension `1`,
    its only associated prime is `P1`, and `P1` is its generic point.
  * Completeness: `A1` is finite over `R` and formally unramified. So `m_{A1} = m A1`
    (`Algebra.FormallyUnramified.map_maximalIdeal`), and `A1` is complete
    (`isAdicComplete_map_of_finite`).
  * The ideal `I1 = I A1`: `nilradical A1 · I1 ⊆ P1 · I1`, which is the image of `P I`, hence
    zero. Since `I1 ⊆ P1 ⊆ nilradical A1`, also `I1² = 0`.
  * The element: `ξ'` is `ξB` restricted along `β1 : B → A1/I1`
    (`AlgHom.liftOfSurjective`, with `β1 ∘ π = mk ∘ mk`).
  * Localization: the localization of `A1` at `P1` is `A`
    (`isLocalization_iff`, using the hypothesis on `a β(s) = β(r)`). So `v`, transported to
    `(A1)_{P1}`, lifts the restriction of `ξ'`. The required identity reduces, by `hv` and a
    computation of maps out of `B` (checked after composing with the surjection `π`), to
    `liftsTo_of_tower`.
  * Condition (F7) (`OneDimensionalLifting`) then gives `ζ ∈ F(Spec A1)` lifting `ξ'`.
  * By `ProRep`, applied with the residue map of `A1/I1`, `ζ = ξB ∘ ψ` for some `ψ : B → A1`.
  * Since `ξB` is a monomorphism, `mk ∘ ψ = β1` (`homR_injective`).
  * So `ψ ∘ π` and `mk : L → A1` agree modulo the nilpotent `I1`. As `L` is formally unramified,
    they are equal (`Algebra.FormallyUnramified.lift_unique`). Hence `I ⊆ ker(L → A1) = ker β`.

* `star`: without the extra hypothesis, `β(I) = 0`. By induction on `k`, `β(I) A ⊆ m_A^k`. For
  the step, apply `star_step` to `A/m_A^(k+1)` and `mk ∘ β`. The prime is still `P`, and the
  remaining hypotheses pass to the quotient. The product condition holds because
  `β(P) β(I) ⊆ m_A · m_A^k`. Finally `m_A` is nilpotent.

The proof reuses `ArtinianBase.homR_injective` from `ArtinianBaseSpec` for the injectivity of the map on algebra homomorphisms.
