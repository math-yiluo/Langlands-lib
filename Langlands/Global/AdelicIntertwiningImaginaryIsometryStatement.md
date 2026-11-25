# Isometry of intertwining operators at imaginary points of holomorphy

Module `Langlands.Global.AdelicIntertwiningImaginaryIsometryStatement` states
`Langlands.Global.IntertwiningImaginaryIsometryStatement` as a proposition
definition. It supplies no proof. It is stated for
`IntertwiningImaginaryUnitarityStatement` (module
`Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement`). This
statement is the first of the two steps of the source proof of that target;
the second step, holomorphy on the imaginary axis, is what separates the two
statements (see "Relation to the unitarity statement" below).

## Sources

- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
  series*, Cambridge Tracts in Math. 113 (1995), registered as
  `moeglin-waldspurger-1995-spectral-decomposition`, IV.3.12, p.161
  (chapter file `08.3_pp_149_164_The_case_of_relative_rank_1.pdf`), proof of
  IV.1.11 in relative rank one: from the adjunction relation
  `⟨φ', M(w, λ)φ⟩ = ⟨M_w(w⁻¹, -wλ̄)φ', φ⟩` and the functional equation, "we
  obtain `⟨M(w, λ)φ, M(w, λ)φ⟩ = ⟨φ, φ⟩` for every `φ ∈ A(M, π)_𝔉`, say for
  every `λ ∈ Im X_M^G` where `M(w, .)` is holomorphic". The holomorphy of
  `M(w, ·)` on all of `Im X_M^G` (part (b)) is deduced afterwards from this
  identity. For the discrete spectrum of `M`, VI.2.3 (p.264, chapter file
  `9.4.2_pp_259_272_Spectral_decomposition.pdf`): "The intertwining operators
  are holomorphic on the unitary axis since these operators are unitary there,
  and defined on an open dense set."
- E. Lapid, *On Arthur's asymptotic inner product formula of truncated
  Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
  `lapid-2011-asymptotic-inner-product-truncated-eisenstein` (PDF page =
  printed page + 9), §2, p.312: "The functional equations of the intertwining
  operators immediately imply that for `λ ∈ i𝔞_P^*`, `M(w, λ)` is unitary,
  hence holomorphic". Here `M(w, λ) : A^2_P → A^2_Q` for `w ∈ Ω(P, Q)`.

## Statement

The data and hypotheses are exactly those of
`IntertwiningImaginaryUnitarityStatement`, in the same order (see its
Markdown): a number field `F`, connected reductive `G`, the parabolic `P = MU`
with presentation `r`, the parabolic `P' = M'U'` with rational Levi `l'`,
`M' ⋉ U' ≅ P'` and Levi projection `π'`, a presentation `(w, cw)` of an
element of `W(P, P')`, a maximal compact `K` with `P(𝔸)K = P'(𝔸)K = G(𝔸)`,
a closed matrix embedding `rho` and the smooth-structure data, Haar measures
`μM`, `μM'` compatible with the Iwasawa decompositions, coordinates `e` and
`e' = w ∘ e`, weights `β`, `β'` with integral `1`, forms `v j ∈ A^2_P` and
`ψ j i ∈ A^2_{P'}`, and coefficients `coeff j i`, meromorphic in linear
coordinates with one domain of holomorphy `DM`, such that
`M(w, λ)(v j)(g) = ∑ i, coeff j i λ · ψ j i g` for `Re λ` sufficiently
regular (`r.IsRegularParameter hA hT R λ` for some `R`), where `M(w, λ)` is
`hK.intertwiningOperator hK' iU l iU' cw π' w`.

Then, for all coefficients `coeff' j i` and every set `DM'` such that

1. every `coeff' j i` is meromorphic in linear coordinates with domain of
   holomorphy `DM'` (`IsMeromorphicInCoordinatesOn (coeff' j i) DM'`), and
2. `∑ i, coeff' j i λ · ψ j i g = ∑ i, coeff j i λ · ψ j i g` for all `j`,
   all `λ ∈ DM ∩ DM'` and all `g`,

and for every `μ ∈ X^*(P) ⊗ ℝ` with `λ = imaginaryParameter F P μ ∈ DM'` and
all `j`, `j'`:

`∑ i, ∑ i', coeff' j i λ · conj (coeff' j' i' λ) · (ψ j i, ψ j' i')_{P'} = (v j, v j')_P`,

with `(·,·)_P = inducedInnerProduct K hK.isCompact p l μM e β` and
`(·,·)_{P'} = inducedInnerProduct K hK'.isCompact p' l' μM' e' β'`.

## Correspondence with the source

- "Where `M(w, ·)` is holomorphic". The continuation of `λ ↦ M(w, λ)(v j)`
  is the function `λ ↦ ∑ i, coeff j i λ · ψ j i`; it is determined on the
  open dense set `DM` by its values for regular `λ`. A family `coeff'` as in 1
  and 2 represents the same continuation (2 says the two representations
  agree on the open dense set `DM ∩ DM'`), and `∑ i, coeff' j i λ · ψ j i` is
  holomorphic on `DM'`. So the points of `DM'` are points at which the
  continuation of `M(w, ·)(v j)` is holomorphic, and every such point is in
  the domain `DM'` of some such family. The conclusion is MW's identity at
  these points. A second family is needed because `DM` is only some open dense
  set on which the given coefficients are holomorphic: it can miss the whole
  imaginary axis, which has empty interior, although the continuation is
  holomorphic there.
- The identity. Since `(·,·)_{P'}` is linear in the first and
  conjugate-linear in the second variable on `A^2_{P'}`, the left side is
  `(∑ i, coeff' j i λ · ψ j i, ∑ i', coeff' j' i' λ · ψ j' i')_{P'}`, that is,
  `(M(w, λ)(v j), M(w, λ)(v j'))_{P'}` at the point `λ`. MW state it for
  `φ' = φ`; the form for two vectors is its polarization, and it is what their
  argument gives directly: the adjunction relation with the functional
  equation `M(w⁻¹, wλ) M(w, λ) = 1` and `-wλ̄ = wλ` for imaginary `λ` gives
  `(M(w, λ)φ, M(w, λ)φ')_{P'} = (φ, φ')_P`.
- Cuspidal and discrete data. MW IV.3.12 treats cuspidal data in relative
  rank one (section IV.3); VI.2.3 states
  unitarity on the unitary axis for the discrete spectrum of `M`, and Lapid
  states it for all of `A^2_P`. The statement is for arbitrary `v j ∈ A^2_P`,
  as in Lapid.
- Normalizations of measures, of `K` and of the parabolics are those of
  `IntertwiningImaginaryUnitarityStatement`; its Markdown explains them.

## Relation to the unitarity statement

`IntertwiningImaginaryUnitarityStatement` asserts the existence of a family
`coeff'` with domain `DM'` containing the whole imaginary axis, satisfying 1
and 2 and the identity above at every imaginary point. This statement asserts
the identity for every such family at the imaginary points of its domain, and
does not assert that any family has a domain containing an imaginary point.
The step from this statement to holomorphy on the whole imaginary axis is MW's
second step (a pole on `Im X_M` would make `‖M(w, λ)φ‖` unbounded for nearby
imaginary `λ`), which uses that the singularities of `M(w, ·)` lie on root
hyperplanes; see the Markdown of the unitarity statement.

## Scope

The statement does not assert the adjunction formula, the functional equation
or the holomorphy of `M(w, ·)` at any point.
