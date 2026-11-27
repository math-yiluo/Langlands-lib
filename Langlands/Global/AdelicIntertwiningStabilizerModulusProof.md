# The normalized Haar factor of the intertwining quotient

Module `Langlands.Global.AdelicIntertwiningStabilizerModulusProof` contains one theorem,
`Langlands.Global.intertwiningStabilizerModulus`, which proves
`IntertwiningStabilizerModulusStatement` (module `AdelicIntertwiningStabilizerModulusStatement`)
at every universe `u`, with all of its hypotheses.

## Statement proved

For the data of the statement (a connected reductive `G` over a number field `F`, parabolics
`p : P → G`, `q : Q → G` with geometric unipotent radicals `iU`, `iV` and rational Levi subgroups
`l : M → P`, `l' : M' → Q`, and a Weyl conjugation `(w, c)`) and every `m ∈ M'(𝔸)`, the Haar
factor `mulEquivHaarChar α / mulEquivHaarChar αH` of conjugation `α` by `l'(m)` on `V(𝔸)` and
its restriction `αH` to the closed stabilizer equals

`l'(m)^{ρ_Q} · (c ≫ l)(m)^{-ρ_P}`,

where `x^λ` is `parameterPower` and `ρ_Q`, `ρ_P` are `halfModulusParameter F Q` and
`halfModulusParameter F P`.

## Proof

1. The left side of the statement is, by definition, the Library's
   `intertwiningLeviHaarFactor iU iV hw hUn hVn hi hVu m` (module
   `AdelicIntertwiningNormalizedLevi`); the proof records this with `change`.
2. `intertwiningLeviHaarBalance_of_parabolics` (module `AdelicIntertwiningLeviHaarBalance`),
   applied to the same parabolics, Levi subgroups and Weyl conjugation, gives

   `intertwiningLeviHaarFactor … m · l(c(m))^{ρ_P} = l'(m)^{ρ_Q}`.

   That theorem uses the proofs of normality, closedness and unipotence derived from the
   parabolic and radical hypotheses, while the statement takes them as separate arguments
   `hUn`, `hVn`, `hi`, `hVu`. These are proofs of propositions, so by proof irrelevance the two
   Haar factors are the same term and the identity applies.
3. `map_comp_apply_of_hom` (module `AdelicIwasawaHeight`) rewrites the point
   `(c ≫ l)(m)` of `P(𝔸)` on the right side of the statement as `l(c(m))`.
4. Substituting the identity of step 2 for `l'(m)^{ρ_Q}` turns the right side into
   `intertwiningLeviHaarFactor … m · l(c(m))^{ρ_P} · l(c(m))^{-ρ_P}`. Since
   `x^λ = exp ⟨λ, H(x)⟩` (`parameterPower` is the exponential of the pairing with
   `characterLog`), the pairing is linear in `λ` and `exp(a) exp(-a) = 1`, the last two factors
   multiply to `1`, which leaves the left side.

## Provenance

The statement is the modulus identity behind Bernstein–Lapid (6.5), as explained in the Markdown
of `AdelicIntertwiningStabilizerModulusStatement`. The mathematical content of this proof is the
Haar balance `intertwiningLeviHaarBalance_of_parabolics`; the steps above only convert its form.
