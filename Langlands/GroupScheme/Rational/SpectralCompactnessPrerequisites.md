# Spectral prerequisites for anisotropic local-field compactness

This derived statement unit separates two missing algebraic inputs to the reverse
implication of `Langlands.GroupScheme.AnisotropicCompactnessStatement`. It also
implements the reduction from those inputs to compactness using published
embedding and affine-point topology theorems. Neither spectral input is proved
here, and this unit does not prove the unconditional compactness equivalence.

All fields have arbitrary universe `u`. They carry the existing
`IsNonarchimedeanLocalField` structure, with its given valuation and topology.
There is no characteristic restriction. The groups are actual group schemes over
`Spec F`, with the existing `IsConnectedReductive` witness. Anisotropy means the
existing `IsAnisotropic`, namely split rank zero; central split tori count.

## Statements and coefficient convention

For an actual representation `ρ : MatrixRepresentation G (Fin N)`,
`MatrixRepresentation.HasIntegralCharacteristicPolynomials ρ` says that for
every actual rational point `g` and every natural number `i`, coefficient `i` of
the characteristic polynomial of `ρ.rationalMatrix g` satisfies `coeff ≤ᵥ 1`.
Thus the coefficients belong to the valuation ring of the given valuative
relation. The rational matrix uses the published global-section comparison
`Γ(Spec F, O) ≅ F`; it is not an independently chosen point homomorphism.
The index `N` includes zero. Coefficients beyond the degree are also quantified.

`ReductiveSpectralBoundednessStatement` says that integrality of all these
coefficients for a representation which is a closed immersion implies
`IsAlgebraicallyBounded F G.X Set.univ`. Affineness is installed from the same
reductivity witness as in the final compactness target. No anisotropy premise is
used in this input. This is the coefficient version of the contrapositive of
KP Lemma 2.2.11, restricted to the whole rational-point group. Its intended
derivation also needs rational-point Zariski density for connected reductive
groups over local fields, the equivalence between integral coefficients and
integral roots in a valued algebraic closure, and boundedness transport.
These remain proof obligations, not consequences supplied by this declaration.

`AnisotropicSpectralIntegralityStatement` says that anisotropy forces the
coefficient property in every actual representation. The representation need
not be faithful. This isolates the algebraic part of the proof of KP
Theorem 2.2.9: semisimple replacement of a point, containment in a maximal
rational torus, and the Galois sum of a weight detecting a nonzero valuation.
A nonzero rational character of that torus yields a nontrivial split subtorus
of the original group, contradicting anisotropy. The published finite-Galois
splitting and character/cocharacter results are possible inputs, but the
pointwise eigenvalue and descent bridges still need proofs. In positive
characteristic a power of the point is used; perfectness of the local field
itself is not a premise.

`SpectralCompactnessPrerequisitesStatement` is the conjunction of these two
individually named universal targets. `AnisotropicPointsCompactnessStatement`
names the reverse implication of the existing compactness equivalence, with
precisely the reductivity-derived affine instances and canonical
`rationalPointTopology F G.X`. It adds no boundedness, representation, splitting,
or quotient hypothesis.

## Implemented conditional reduction

`anisotropicPointsCompactness_of_spectral` assumes the two universal spectral
statements. For a given anisotropic connected reductive group it installs
affineness from `hG.isAffineHom` and smoothness from `hG.smooth`. Smoothness gives
local finite type. The published
`affineLinearEmbeddingStatement_viaCorepresented` supplies a closed faithful
representation on `Fin N`. The integrality input applies to that representation,
and the boundedness input then bounds every regular function on all rational
points. Finally, `localFieldAffineBoundedCompactness_proof` applied to the closed
set `Set.univ` gives compactness in the exact canonical topology.

This is a conditional helper, not a proof discharging either spectral target.
An eventual proof of the original equivalence must consume proofs of those
targets and the forward implication; it may not retain them as extra premises.
The faithful representation is supplied internally. The adjoint representation
alone would not suffice to detect central split directions because its kernel
need not be finite.

## Provenance

The coefficient interface and decomposition are derived formalization choices,
not verbatim statements from the source.

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
  registered as `kaletha-prasad-2023-bruhat-tits-new-approach`,
  SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:
  Definition 2.2.1, Remark 2.2.2, Fact 2.2.3 (printed p.70 / PDF p.101);
  Lemma 2.2.7 (printed p.71 / PDF p.102);
  Lemmas 2.2.10–2.2.11 and proof of Theorem 2.2.9
  (printed pp.72–73 / PDF pp.103–104).
- The authors' 1 November 2024 corrections, registered as
  `kaletha-prasad-2024-corrections`,
  SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`:
  §2.2 corrections, PDF p.24. Henselianity is a standing hypothesis;
  Lemma 2.2.5 additionally requires a separable extension or discrete valuation.
  The actual local-field scope satisfies these restrictions.
