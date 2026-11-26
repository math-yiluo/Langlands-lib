# The finite-image Weil–Galois orbit dictionary

Let \(K\) be a nonarchimedean local field of arbitrary characteristic
with separable closure \(\Omega\). Write \(G_K\) for \(\operatorname{Aut}_K(\Omega)\)
with its Krull topology. The module uses the Weil group \(W_K\), degree
and projection \(W_K\to G_K\) of `Langlands.Weil.Local.SepClosed` and the
absolute inertia of `Langlands.LocalGalois.SepClosed`. The field, closure
and complex representation carriers have independent universe levels.
The numerical predicates use rank \(k+1\) for \(k:\mathbb N\).

## Galois classes and twists

The following definitions are in `Langlands.Henniart.LocalNumerical`.

- `galoisUnramifiedCharacters K Ω` is the subgroup of continuous homomorphisms
  \(G_K\to\mathbb C^\times\) whose values on absolute inertia are all \(1\).
  These characters have finite order because continuous complex characters of
  a profinite group have finite image. This is the character group used on
  the complex Galois side in Henniart 1988, §4.2.
- `IrreducibleGaloisClass K Ω n` is `FiniteRepresentation.ContinuousIrreducibleClasses`
  for \(G_K\) at positive rank \(n\). Its definition asks for continuity and
  irreducibility at that rank. Finite image follows from continuity by
  `Langlands.Weil.continuous_compact_nonarchimedean_representation_finite_range`
  for the profinite group \(G_K\), in accordance with Henniart 1980, §2.1.
- `galoisUnramifiedTwist K Ω k χ` applies
  `FiniteRepresentation.continuousIrreducibleTwistEquiv` to the underlying
  continuous character of \(\chi\). It is an equivalence of the rank-\(k+1\)
  class space, given by scalar twisting as in Henniart 1988, §4.2.
- `galoisTorsionNumber K Ω ρ` is the `Nat.card` of the characters in
  `galoisUnramifiedCharacters K Ω` whose twist fixes \(\rho\) as an isomorphism
  class. It is the Galois version of the stabilizer cardinality in the
  numerical route note, §2.2. Henniart 1988, Proposition 2.2(a), gives
  the determinant argument for finite order of self-twists.
- `GaloisUnramifiedOrbitClasses K Ω` is the orbit quotient of
  `Langlands.VirtualRepresentation.Weil.IrreducibleBasis` for \(G_K\).
  This basis is the disjoint union of the classes over all positive ranks.
  The action is `Weil.twistAction` restricted along the inclusion of the
  unramified character subgroup. `galoisUnramifiedOrbitClass K Ω` sends a
  rank-tagged class to its orbit. The quotient implements the finite-order
  unramified orbits of Henniart 1988, §4.2.

## Pullback and numerical strata

- `IsGaloisPullback K Ω σ ρ` says that `weilClassForget K Ω σ` is the
  isomorphism class obtained by restricting the underlying class of \(\rho\)
  along \(W_K\to G_K\). `FiniteRepresentation.restrictClass` descends
  precomposition to classes, so the equality expresses the representative
  formulation of Henniart 1980, §2.1.
- `HasGaloisSwan K Ω ρ s` means that some \(\sigma\) of the same rank
  satisfies `IsGaloisPullback K Ω σ ρ` and `HasWeilSwan K Ω σ s`.
  This transports the Swan exponent through restriction as in the
  external-inputs plan, §4.3. It inherits the natural subtraction convention
  for the Weil Swan exponent, including Swan exponent zero for the
  unramified rank-one case of Henniart 1988, §2.1.
- `galoisRefinedStratum K Ω k s f` consists of the orbits containing a
  rank-\(k+1\) class with Swan exponent \(s\) and torsion number \(f\).
  It has the same membership form as `weilRefinedStratum` and uses the
  refined strata of the numerical route note, §2.2.

## Dictionary statements

The `Prop`-valued definitions below are in `Langlands.Henniart`.

- `WeilGaloisTypeTwistStatement` asserts that each irreducible Weil class
  of rank \(k+1\) has an unramified scalar twist that is the pullback of a
  Galois class of the same rank. Henniart 1980, §2.3, Corollary 3 writes
  the original representation as the twist of one of Galois type.
  Twisting by the inverse character gives the direction used here. This
  is the class-level general-field form of the reduction in
  `Langlands.Weil.Local.LocalWeilIrreducibleReductionFor`.
- `GaloisPullbackBijectionStatement` asserts that each Galois class has
  exactly one Weil pullback class of its rank, and that a Weil class
  related to two Galois classes determines their equality. The class
  formulation comes from precomposition and density in Henniart 1980,
  §2.1. An intertwiner on the dense Weil image is an intertwiner of the
  continuous Galois representations. These are the class-level consequences
  of the extension and uniqueness underlying
  `Langlands.Weil.Local.LocalWeilGaloisTypeFor`.
- `GaloisPullbackTwistStatement` asserts that two pullbacks at the same
  rank differ by a Weil unramified twist exactly when their Galois classes
  differ by a Galois unramified twist. It also asserts equal torsion numbers
  for each pullback pair. For the provenance, the ratio of the two
  finite-order determinants is the \(n\)th power of the twisting character
  in rank \(n\), so the character itself has finite order. It extends
  uniquely from the integer degree group to the profinite residue quotient.
  For a self-twist the same determinant comparison gives \(\chi^n=1\),
  as in Henniart 1988, Proposition 2.2(a). Restricting and extending
  finite-order characters therefore compares the two stabilizers.
- `WeilGaloisOrbitDictionaryStatement` asserts an equivalence from the
  unramified-twist orbits of \(W_K\) to the unramified-twist orbits of
  \(G_K\). It sends the orbit of \(\sigma\) to that of \(\rho\) for
  each pullback pair and sends `weilRefinedStratum K Ω k s f` onto
  `galoisRefinedStratum K Ω k s f` for every \(k,s,f\). The external-inputs
  plan, §4.3, uses this comparison to pass from Weil orbits to the finite-image
  Galois data in the close-fields argument. The numerical route note,
  §5.4, uses finite-image representatives in the proof of `cor:Laumon`.
  Its proof of `prop:LD` compares the corresponding strata directly using
  filtered Weil quotients with compatible degree maps.
- `WeilGaloisDictionaryStatement` is the conjunction of these four
  statements.

## Sources

- Guy Henniart, *Représentations du groupe de Weil d'un corps local*,
  L'Enseignement Mathématique (2) 26 (1980), 155–172.
  `henniart-1980-weil-representations`, SHA-256
  `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
  §§2.1–2.3, including Corollary 3, printed p. 158 (PDF p. 5).
  [Journal record](https://doi.org/10.5169/seals-51064)
- Guy Henniart, *La conjecture de Langlands locale numérique pour GL(n)*,
  Ann. Sci. ÉNS (4) 21 (1988), 497–544.
  `henniart-1988-numerical`, SHA-256
  `3de93884b6c4b26106d614e648cfb7f293f9f40a66ef352c0751e222a602f25c`.
  §§2.1–2.2 and Proposition 2.2(a), printed pp. 503–504 (PDF pp. 8–9),
  give the Swan convention, Galois types and determinant identity.
  §4.2, printed p. 510 (PDF p. 15), uses finite-order unramified orbits in
  the complex-to-\(\ell\)-adic comparison.
  [Numdam](https://www.numdam.org/item/ASENS_1988_4_21_4_497_0/)
- *Formalizing the large external inputs of the local Langlands correspondence
  for GL_n*, 16 November 2026.
  `operator-external-inputs-plan-2026-11-16`, directory SHA-256
  `c429afd5b4f28270a0619b3292f8825a9bfa77c3d842ac3a2a81fc2042cc0463`.
  `external-inputs-plan.tex`, SHA-256
  `816bb31b7194dea7eb38a661bf53ae670c17a2ec0bd7d1e7e4bcfa2c94aad03a`.
  §4.3, lines 575–576, and the table at line 1058 describe the orbit comparison.
- *The numerical local Langlands correspondence for GL_n: counts on the two
  sides and the recommended route of proof*, 16 November 2026.
  `operator-numerical-llc-route-2026-11-16`, directory SHA-256
  `faece16e4d4722c37c1ba0e7ebba30a11d94b64639f20f19a6aa7ccff3faba3f`.
  `numerical-LLC-route.tex`, SHA-256
  `b57ba9428a0d664d0c6beed75bbc2a2d0d73638718a8080c2f913b75acbbb3c8`.
  §2.2 defines the refined strata. §5.4, line 801 in the proof of
  `cor:Laumon` and line 828 in the proof of `prop:LD`, gives the uses
  of the orbit comparisons in the count.
