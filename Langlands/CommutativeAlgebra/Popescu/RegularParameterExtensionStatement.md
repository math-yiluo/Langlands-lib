# Adding variables that map to a regular system of parameters of the closed fibre

`Langlands.CommutativeAlgebra.Popescu.RegularParameterExtensionStatement` (universe `u`). Let `k` be a
field, `Λ` a Noetherian `k`-algebra, `q ⊂ Λ` a prime, `t, r ∈ ℕ`, and
`φ : k[y₁, …, y_t, z₁, …, z_r] → Λ` a `k`-algebra map. In Lean the ring is
`MvPolynomial (Fin (t + r)) k`, with `y_i = X (Fin.castAdd r i)` and `z_j = X (Fin.natAdd t j)`.
Let `φ₀ = φ ∘ rename (Fin.castAdd r) : k[y] → Λ` and `𝔭₀ = φ₀⁻¹(q)`. Assume:

1. `k[y]_{𝔭₀} → Λ_q` is flat (`Localization.localRingHom 𝔭₀ q φ₀ h₀`);
2. `R₁ = Λ_q/𝔭₀Λ_q` is a regular local ring (instance argument);
3. every `φ(z_j)` lies in `q`;
4. the images of `φ(z₁), …, φ(z_r)` in `R₁` form a regular system of parameters:
   `(maximalIdeal R₁).spanFinrank = r` and they generate `maximalIdeal R₁`.

Then, for `𝔭 = φ⁻¹(q)`, the map `k[y, z]_𝔭 → Λ_q` is flat and `𝔭Λ_q = qΛ_q`
(`𝔭.map ((algebraMap Λ Λ_q).comp φ) = maximalIdeal Λ_q`).

## Source

Stacks Project, Smoothing Ring Maps, proof of Lemma 16.11.2 (Tag 07FH; source
`stacks-artin-axioms-approximation-2026-11-06`, smoothing.pdf, printed p. 27). After obtaining from
More on Algebra, Lemma 15.36.2 that `k[y₁, …, y_t]_{𝔭'} → Λ_q` is flat and `Λ_q/𝔭'Λ_q` is regular,
it says: "Thus we can choose further elements `λ_{t+1}, …, λ_m ∈ Λ` … which map to a regular system
of parameters of `Λ_q/𝔭'Λ_q`. We obtain `φ : k[y₁, …, y_m] → Λ` having property (1)". Property (1)
of Lemma 16.11.2 is "setting `𝔭 = φ⁻¹(q)` we have `qΛ_q = 𝔭Λ_q` and `k[y₁, …, y_m]_𝔭 → Λ_q` is
flat". This statement isolates that step.

The expected proof uses the fibrewise criterion of flatness (Algebra, Lemma 10.99.15; Library
`Langlands.Algebra.NoetherianFiberwiseFlatnessStatement`) over `k[y]_{𝔭₀} → k[y, z]_𝔭`. On the
closed fibre, `κ(𝔭₀)[z]_{(z)} → Λ_q/𝔭₀Λ_q` sends the regular system of parameters `z` to a regular
system of parameters, which is a regular sequence (Algebra, Lemma 10.106.3, Tag 00NQ), so it is flat
(Algebra, Lemma 10.128.2, Tag 07DY).

## Encoding

- "Regular system of parameters of `R₁`" is encoded as a family of `r` elements generating the
  maximal ideal, with `r` equal to the minimal number of generators (`Submodule.spanFinrank`),
  in a regular local ring.
- The source requires the `λ_j` (`j > t`) to map into the subalgebra `A`, which is irrelevant to
  property (1) and is not part of this statement. Condition 3 holds there because these `λ_j` map
  into the maximal ideal.
- All types are in one universe `u`; `k` may be any field.
