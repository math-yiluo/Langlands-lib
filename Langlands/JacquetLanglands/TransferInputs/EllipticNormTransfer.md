# The elliptic norm of a square-integrable character, computed on `Dˣ`

The module `Langlands.JacquetLanglands.TransferInputs.EllipticNormTransfer`
states one proposition, `EllipticNormTransferStatement`, and does not prove it.
If the character of an irreducible square-integrable representation of
`GL_n(F)` is, on corresponding regular elements, a linear combination of the
characters of pairwise inequivalent irreducible representations of `Dˣ`, then
the squared absolute values of the coefficients sum to `1`. This is the
orthogonality relation of elliptic characters on `GL_n(F)`, read on `Dˣ`.

## Notation

- `F` is a nonarchimedean local field of characteristic zero and `D` a
  finite-dimensional central division algebra over `F` with its `F`-module
  topology, both in `Type u`; `n` satisfies `Module.finrank F D = n ^ 2`.
  `Dˣ` carries the units topology; the `haveI` lines supply the Hausdorff,
  locally compact, totally disconnected group structures of `GL_n(F)` and
  `Dˣ` (`Langlands.JacquetLanglands.DivisionUnits`).
- `IsSquareIntegrable π` (`Langlands.JacquetLanglands.EssentiallySquareIntegrable`):
  `π` is admissible, has a unitary central character and square-integrable
  matrix coefficients on `GL_n(F)/Z`.
- `Representation.IsIrreducible` means that the lattice of subrepresentations
  is simple; `IsAdmissible` is the Library's admissibility; `(τ i).Equiv (τ j)`
  is the type of equivalences of representations.
- `Corresponds F D g g'` (`Langlands.JacquetLanglands.RegularElliptic`): `g` is
  regular elliptic, `g'` is regular (separable reduced characteristic
  polynomial), and the characteristic polynomial of `g` is the reduced
  characteristic polynomial of `g'`.
- `HasCharacterValue ρ hρ g c` (`Langlands.JacquetLanglands.LocalCharacter`):
  the distribution character of `ρ` equals `c` times Haar measure near `g`.

## The statement

`EllipticNormTransferStatement` says the following. Let `F`, `D`, `n` be as
above. Let `π` be a representation of `GL_n(F)` on `V : Type uV` with
`hπ : IsSquareIntegrable π` and `π` irreducible. Let `J` be a finite type and,
for `j : J`, let `τ j` be a representation of `Dˣ` on `W j : Type uW`, admissible
(`hτ j`) and irreducible, with `τ i` and `τ j` inequivalent for `i ≠ j`. Let
`a : J → ℂ`. Assume that for every `g : GeneralLinear n F` and `g' : Dˣ` with
`Corresponds F D g g'` there are `c` and `d : J → ℂ` with

- `HasCharacterValue π hπ.isAdmissible g c`,
- `HasCharacterValue (τ j) (hτ j) g' (d j)` for every `j`,
- `c = ∑ j, a j * d j`.

Then `∑ j, ‖a j‖ ^ 2 = 1`.

The universes `u`, `uV`, `uW` are free; the index type `J` is in `Type`.

## Why the statement is true

Write `Θ_π` for the character function of `π` and `Θ_j` for that of `τ j`.
Irreducible admissible representations of `Dˣ` are finite-dimensional, because
`Dˣ/Fˣ` is compact, so `Θ_j(g') = trace τ_j(g')`; it is locally constant.
Let `ω` be the unitary central character of `π` and `ω_j` the central character
of `τ j` (Schur's lemma).

1. *Terms with another central character have coefficient zero.* If `g ↔ g'`
   correspond, so do `z g ↔ z g'` for every `z ∈ Fˣ` (both characteristic
   polynomials become `z^n P(X/z)`), and `Θ_π(z g) = ω(z) Θ_π(g)`,
   `Θ_j(z g') = ω_j(z) Θ_j(g')`. Applying the hypothesis at `(z g, z g')` and
   subtracting `ω(z)` times the hypothesis at `(g, g')` gives
   `∑_j a_j (ω_j(z) − ω(z)) Θ_j(g') = 0` at every regular `g'` (every regular
   `g'` has a partner `g`). The `Θ_j` are locally constant and the regular set is
   dense in `Dˣ`, so the identity holds on all of `Dˣ`, hence for the
   distribution characters; their linear independence (Bernstein–Zelevinsky,
   in the Library `Langlands.Character.finiteFamilyLinearIndependence`) gives
   `a_j (ω_j(z) − ω(z)) = 0` for all `j` and `z`. So `a_j = 0` unless
   `ω_j = ω`, and it remains to treat a family with the common central
   character `ω`.
2. *Elliptic orthogonality on `GL_n(F)`.* For irreducible square-integrable
   `π` with unitary central character `ω`, the elliptic self-pairing
   `∑_T |W(G, T)(F)|⁻¹ ∫_{T/Z} |D(t)| |Θ_π(t)|² dt`, the sum running over the
   conjugacy classes of elliptic maximal tori `T`, with `W(G, T)(F)` the
   rational Weyl group, `D` the Weyl discriminant and the probability Haar
   measure on each `T/Z`, equals `1` (Clozel, Theorem 3; DKV §A.3 for the
   normalization). The function `|Θ_π|²` is invariant under `Z`, since `ω`
   is unitary. The Library states the orthogonality relations, with a common
   measure on `GL_n(F)/Z`, as
   `Langlands.BaseChange.EllipticCharacterOrthogonalityStatement`.
3. *Weyl integration on `Dˣ/Fˣ`.* The elliptic maximal tori of `GL_n(F)` are
   the groups `Lˣ` of the degree-`n` field extensions `L/F`; each such `L`
   embeds in `D`, uniquely up to conjugacy (Skolem–Noether), and the maximal
   tori of `Dˣ` are these `Lˣ`. The rational Weyl groups on both sides are
   `Aut_F(L)`, the Weyl discriminants agree at corresponding elements, and
   `g ↔ g'` matches the regular elliptic conjugacy classes of `GL_n(F)` with
   the regular conjugacy classes of `Dˣ`. For the probability Haar measure on
   the compact group `Dˣ/Fˣ` and the probability Haar measures on the `T/Fˣ`,
   the Weyl integration formula writes the integral over `Dˣ/Fˣ` of a function
   invariant under conjugation and under `Fˣ` as the same sum over tori. Hence
   the self-pairing of step 2 equals `∫_{Dˣ/Fˣ} |∑_j a_j Θ_j|²`: the function
   `|∑_j a_j Θ_j|²` is invariant under `Fˣ` because all `τ j` now have the
   central character `ω`, and it agrees with `|Θ_π|²` at corresponding
   regular elements; the non-regular elements of `Dˣ` form a null set.
4. *Schur orthogonality on `Dˣ/Fˣ`.* For pairwise inequivalent irreducible
   `τ i`, `τ j` with the common central character `ω`, the product
   `Θ_i · conj(Θ_j)` descends to `Dˣ/Fˣ` and
   `∫_{Dˣ/Fˣ} Θ_i conj(Θ_j) = δ_{ij}` for the probability Haar measure.

Together, `1 = ∫_{Dˣ/Fˣ} |∑_j a_j Θ_j|² = ∑_j |a_j|²`. This is the
orthogonality step of Deligne–Kazhdan–Vignéras §B.1.f ("les formules
d'orthogonalité des caractères (vraies pour G'_S, vraies pour G_S si les
caractères sont localement L¹)"), there applied after the central character
has been fixed in §B.1.a–b.

The Jacquet–Langlands correspondence also implies the statement: there the
hypothesis forces exactly one coefficient to be `(-1)^(n-1)` and the others to
vanish. Deriving this statement from the correspondence would make the
derivation of the correspondence from it circular
(`Langlands.JacquetLanglands.TransferInputs.UnitaryDivisionReduction` uses it
for that purpose).

## Derived content and differences from the sources

- The sources state orthogonality as an identity of inner products. This
  statement is its consequence for one character expanded in characters of
  `Dˣ`; it involves no measure, because both inner products are normalized to
  give square-integrable characters norm `1`.
- Coefficients and character values are taken only at corresponding regular
  elements (`Corresponds`), where the Library's character values
  (`HasCharacterValue`) are evaluated.
- The family `τ` need not share the central character of `π`; the members
  with another central character have coefficient zero (step 1 above).

## Sources

- P. Deligne, D. Kazhdan, M.-F. Vignéras, *Représentations des algèbres
  centrales simples p-adiques*, in J. N. Bernstein, P. Deligne, D. Kazhdan,
  M.-F. Vignéras, *Représentations des groupes réductifs sur un corps local*,
  Hermann, 1984, pp. 33–117. Registered as
  `bdkv-1984-representations-local-field` (printed page = PDF page − 4):
  - §A.3, "Formules d'orthogonalité des caractères", printed pp. 50–60: for a
    fixed unitary central character `ω`, the Schur relations, coefficients and
    the orthogonality of characters, with the Weyl integration computation on
    pp. 55–56 and §A.3.h on p. 59 (rational Weyl group factor, probability
    Haar measures on the tori);
  - §B.1.f, printed p. 81: orthogonality on `G_S` and on `G'_S` and the
    Schwarz inequality reduce the comparison formula to one term.
- L. Clozel, *Invariant harmonic analysis on the Schwartz space of a reductive
  p-adic group*, in W. Barker, P. Sally (eds.), *Harmonic Analysis on
  Reductive Groups*, Progr. Math. 101, Birkhäuser, 1991, pp. 101–121.
  Registered as
  `provided-698170812a35ff43dbc4156af9f67a8384f95d97d5836529575e646643af617b`:
  §3, Theorem 3, printed pp. 110–111 (elliptic orthogonality of the characters
  of square-integrable representations with the same central character).
