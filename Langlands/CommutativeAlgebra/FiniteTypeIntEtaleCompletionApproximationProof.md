# Etale approximation over finite-type integer algebras: proof

`Langlands.CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation.{u}`
proves the unchanged statement
`Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}`
for every universe `u`. Let `S : Type u` be a commutative finite-type
`ℤ`-algebra and `𝔪` a maximal ideal of `S`. Write `P = Localization.AtPrime 𝔪`
and `P̂` for the adic completion of `P` at its maximal ideal `𝔫`. Let `C` be
a finite-type `P`-algebra, `f : C → P̂` a `P`-algebra map and `N` a natural
number. The theorem supplies an etale `P`-algebra `E : Type u` and
`P`-algebra maps `g : C → E` and `ι : E → P̂` whose composite agrees with `f`
after the canonical projection `P̂ → P / 𝔫^N`.

The route is that of Stacks Project, *Smoothing ring maps*, Theorem 13.2
(tag 07QZ): Popescu factorization through a smooth algebra, followed by etale
specialization of the smooth algebra. All rings and witnesses stay in the
universe `u`.

## Published inputs

The proof uses four Library theorems. It adds no hypothesis.

| Library theorem | Module | Content |
| --- | --- | --- |
| `finiteTypeIntGRing` | `Langlands.CommutativeAlgebra.FiniteTypeIntGRingProof` | Every finite-type `ℤ`-algebra is a G-ring (`IsGRing`). |
| `Popescu.popescuFactorization` | `Langlands.CommutativeAlgebra.Popescu.PopescuFactorizationProof` | Popescu's theorem (Stacks 07GC), finite-type factorization form (`PopescuFactorizationStatement`). |
| `smoothEtaleCompletionApproximation` | `Langlands.CommutativeAlgebra.SmoothEtaleCompletionApproximationProof` | The target property for a smooth source algebra (`SmoothEtaleCompletionApproximationStatement`). |
| `AdicCompletion.isNoetherianRing_of_isNoetherianRing` | `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing` | The adic completion of a Noetherian ring at an ideal is Noetherian. |

## Proof

The module first proves the auxiliary theorem
`etaleCompletionApproximation_of_regularAlgebra_completion`. Let `R : Type u`
be a commutative Noetherian local ring, with maximal ideal `I`. Assume the
canonical map from `R` to its adic completion `R̂` at `I` is regular
(`RegularAlgebra`). The theorem proves `EtaleCompletionApproximation R`.

1. `AdicCompletion.isNoetherianRing_of_isNoetherianRing` shows that `R̂` is
   Noetherian. Popescu's theorem needs this hypothesis on its target.
2. Fix a finite-type `R`-algebra `C`, a map `f : C → R̂` and an order `N`.
   Apply `Popescu.popescuFactorization` to the regular map `R → R̂` and to
   `f`. It gives a smooth `R`-algebra `B : Type u` and `R`-algebra maps
   `g : C → B` and `h : B → R̂` with `h ∘ g = f`.
3. Apply `smoothEtaleCompletionApproximation` to `B`, `h` and `N`. It gives
   an etale `R`-algebra `E : Type u` and maps `g_E : B → E` and
   `ι : E → R̂`. The two maps `ι ∘ g_E` and `h` agree after projection to
   `R / I^N`.
4. The witnesses are `E`, `g_E ∘ g : C → E` and `ι`. Let `x ∈ C`. By step 3
   at `g x`, the projection of `ι (g_E (g x))` equals the projection of
   `h (g x)`. By step 2, `h (g x) = f x`. The two algebra maps therefore
   agree pointwise (`AlgHom.ext`). This gives the required equation.

The main theorem fixes `S` and `𝔪`. `finiteTypeIntGRing S` proves that `S` is
a G-ring. Its first component shows that `S` is Noetherian. Mathlib's
localization instance then makes `P = Localization.AtPrime 𝔪` a Noetherian
ring. It is local because `𝔪` is prime. The second component,
`IsGRing.regularAlgebra_completion` at `𝔪`, proves that `P → P̂` is regular.
The auxiliary theorem applied to `P` proves the statement.

The theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
