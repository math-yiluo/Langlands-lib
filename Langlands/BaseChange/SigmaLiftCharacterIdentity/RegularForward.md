# From the regular σ-lift identity to the Shintani identity

`SigmaLiftCharacterIdentity.isShintaniLift_of_isRegularSigmaLift` is a theorem at universe
parameters `u, v, uV, uW`. It assumes the five premises of
`SigmaLiftCharacterIdentityForwardStatement`:

1. `TwistedCharacterRegularValuesStatement.{u, u, uV}`, used for ordinary character values
   through `ordinary_regular_values`;
2. `TwistedCharacterRegularValuesStatement.{u, v, uW}`, for twisted character values;
3. `RegularTransferStatement.{u, v}`;
4. `ConcordantIntegralEqualityStatement.{u, v}`;
5. `SigmaLiftCharacterIdentity.SigmaRegularOpenStatement.{u, v}`.

Its setting is that of `SigmaLiftCharacterIdentityForwardStatement`. `F : Type u` is a
nonarchimedean local field of characteristic zero. `E : Type v` is a commutative
topological `F`-algebra with its module topology, and `hE : IsCyclicAlgebra σ l`. The
representations `π` of `GL_n(F)` and `τ` of `GL_n(E)` are irreducible and admissible,
`A : SigmaIntertwiner σ n τ`, and `c : ℂ`. The theorem concludes

```lean
IsRegularSigmaLift σ l π hπ τ hτ A c → IsShintaniLift σ l π hπ τ hτ A c
```

so it replaces the hypothesis `IsSigmaLift` of `sigmaLiftCharacterIdentityForward` by
the weaker `IsRegularSigmaLift`.

## Proof

The proof is that of `sigmaLiftCharacterIdentityForward` (module
`Langlands.BaseChange.SigmaLiftCharacterIdentity.Forward`) with two changes. It keeps the
regular support of the transferred function, and it cuts that function by the norm
condition on the determinant before applying the trace identity.

Fix an associated pair `(δ, γ)` with `γ` regular semisimple. Premises 1 and 2 give an
ordinary value `a` at `γ` and a twisted value `b` at `δ`, with open neighborhoods `U`
of `γ` and `Wδ` of `δ` on which the distributions are these values times the Haar
integral. Premise 5 gives a compact open `K` with `δ ∈ K ⊆ Wδ` inside the σ-regular set.
The indicator `φ` of `K` is σ-regularly supported. Premise 3 gives a concordant `f` that
is regularly supported (`IsRegularSupported f`).

As in the Forward proof, both functions are cut by a clopen neighborhood `B` of the
characteristic polynomial coefficients of `γ`. The parameters are the coefficients of
`cyclicNorm σ l` on `GL_n(E)` and of `baseChange F E n` on `GL_n(F)`. The cut
(`ConcordanceLocalization.exists_cutoff_support` and
`ConcordanceLocalization.concordant_cutoff`) gives a concordant pair `(φB, fB)` with the
support of `fB` in the conjugacy saturation of `U`.

The ordinary function is then cut once more, by the clopen preimage under
`GeneralLinear.determinant` of the norm image `(Units.map (Algebra.norm F : E →* F)).range`.
That subgroup is clopen by `isClopen_normUnitsRange`, since `finrank F E = l > 0`. Call
the result `fN`. By `ConcordanceLocalization.concordant_cutoff_ordinary`, `φB` and `fN`
are still concordant. The determinant is invariant under conjugation, and
`IsNormAssociated.norm_determinant_units_eq` puts \(\det\gamma'\) in the norm image for
every associated `γ'`. Now:

- `φB` is σ-regularly supported, since its support lies in `K`;
- `fN` is regularly supported, since its support lies in that of `f`;
- `det g` lies in the norm image wherever `fN g ≠ 0`;
- the support of `fN` lies in the conjugacy saturation of `U`, and that of `φB` in `Wδ`.

So `IsRegularSigmaLift` applies to `(φB, fN)` and gives
`twistedDistribution μE τ hτ A.toLinearMap φB = c * Character.distribution μF π hπ fN`. The local values
turn this into `b * ∫ φB = c * (a * ∫ fN)`. The ordinary side uses
`SigmaLiftCharacterIdentity.evaluate_saturation` on the saturation of `U`. Premise 4
gives `∫ φB = ∫ fN`. The function `φB` is the indicator of a compact open set containing
`δ`, since the coefficient parameter of `δ` equals that of `γ` by
`coefficients_associated`. Its integral is therefore nonzero. Cancelling it gives
`b = c * a`, and the values `a` and `b` give the Shintani identity at `(δ, γ)`.

The lemma `characteristic_integral_ne_zero` proves that the integral of the
indicator of a nonempty compact clopen set is nonzero for a measure that is finite on
compacts and positive on open sets. It restates a private lemma of the Forward module.

## Sources

Henniart–Lemaire (2011), II.2.9 (printed pp. 69–71, PDF pp. 77–79), relates the
Shintani identity, the σ-lift and the trace identity on regularly supported concordant
pairs. In II.6.13 (printed pp. 129–130, PDF pp. 137–138), the auxiliary ordinary
functions \(f_v\) reused from II.6.8 at the places \(v \in S \setminus \{v_0, v_1\}\) are
supported in \(G(F_v)_r \cap N_v(G(E_v))\). The local trace identity at \(v_0\) is
obtained there for every concordant pair with σ-regular and regular support.

The norm condition on determinants is the one in the Library definition
`IsRegularSigmaLift`: the trace identity is assumed only for ordinary test functions
whose determinant lies in \(N_{E/F}(E^\times)\) on their support. The determinant-norm
cutoff is a derived step. It adapts the forward character argument of II.2.9 to that
restricted class of test functions. Arthur–Clozel (1989), Chapter 1, §6.3 (printed p. 57,
PDF p. 71), gives context for this restriction. The representations on the right of (6.5)
are determinant twists of one another, and their local characters coincide on the image
of the norm.

- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe pour
  GLₙ en caractéristique non nulle*, Mém. SMF 124 (2011). Source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`.
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced Theory
  of the Trace Formula*, Annals of Mathematics Studies 120 (1989). Source ID
  `arthur-clozel-1989-base-change`.
