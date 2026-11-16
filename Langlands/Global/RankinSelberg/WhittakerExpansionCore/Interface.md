# Interface of the analytic core of the Whittaker expansion

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.Interface`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. This helper module only fixes definitions and
one Prop-valued statement. It proves nothing. The analytic proof of the Whittaker expansion of a
cusp form (Cogdell 2004, *Analytic theory of L-functions for GL_n*, §1, Theorem 1.1,
printed p.200; Shalika 1974, §5, Theorem 5.9) is split into two independent halves:

* **(S)** summable majorants for the Whittaker terms (statement `WhittakerMajorantsStatement`
  below, proved in module `WhittakerStep`);
* **(E)** the expansion itself, given summability of the Whittaker terms at every level (proved
  directly as `hasSum_whittaker_of_levelPropsB` in module `ExpansionInduction`, without an
  interface statement).

The split itself is internal to this project. Cogdell states convergence and the identity together.
Here the decay estimates go into (S) and the Fourier inversion into (E).

## Definitions

* `whittaker F r ψ f` is the Library's `generalLinearWhittakerFunction F r ψ (fun _ => 1) f`. This
  is the `ψ`-Whittaker function `W_f(g) = ∫_{N(F)\N(𝔸)} f(n g) ψ⁻¹(n_{12} + ⋯ + n_{r,r+1}) dn` on
  `GL_{r+1}(𝔸)`, with all simple-root coefficients `1`. The Library's `cuspWhittaker` uses the
  same coefficients.
* `HasWhittakerMajorants F r ψ f` holds when, for every level `j ≤ r` and every compact set
  `C ⊆ GL_{r+1}(𝔸)`, there is a summable `b : N_j(F) \ GL_j(F) → ℝ` with
  `‖W_f(diag(γ_q, I_{r+1-j}) x)‖ ≤ b q` for all cosets `q` and all `x ∈ C`. Here `γ_q = q.out` is
  the chosen representative, padded into `GL_{r+1}(F)` by the Library's `padRational`. At `j = r`
  this gives absolute convergence of the expansion. Because `b` is uniform on `C`, the Weierstrass
  M-test also gives locally uniform convergence of the partial sums of the norms. The lower
  levels `j < r` are the induction hypotheses that (E) needs to justify its interchanges.
* `archPoint F n Z hZ`, for an archimedean matrix `Z` with `Z * Z = 0`, is the adelic point whose
  archimedean component is `1 + Z` (the Library's `ArchimedeanGL.squareZeroElement`) and whose
  finite component is `1`.
* `finitePoint F n l` is the adelic point with archimedean component `1` and finite component `l`.
* `WhittakerDecayClass F r V R` is a predicate on a complex subspace `V` of functions on
  `GL_{r+1}(𝔸)`, together with a real-linear map `R` from archimedean matrices to complex-linear
  endomorphisms of `V`. It holds when every `f ∈ V`:
  - is continuous;
  - is left invariant under `GL_{r+1}(F)`;
  - is right invariant under some open subgroup `L` of `GL_{r+1}(𝔸_f)` (finite level);
  - is bounded on every band `lo ≤ |det x|_𝔸 ≤ hi` with `0 < lo` (the Library's `detNorm`);
  - satisfies `d/dt f(x (1 + t Z))|_{t=0} = (R Z f)(x)` for square-zero `Z` and every `x`.
  So `V` is closed under the archimedean derivatives along square-zero directions, and every
  derivative is again bounded on bands. The class is designed so that the functions of an actual
  cuspidal realization, and their duals `g ↦ φ(w ᵗg⁻¹)`, can be shown to form one. Boundedness on
  bands follows from the rapid decay of cusp forms on Siegel sets.

## Statement

The statement assumes a number field `F` with `CompactSpace (AdeleQuotient F)`. The target
statement `CuspidalWhittakerExpansionStatement` carries the same hypothesis.

* `WhittakerMajorantsStatement F` (half S): for every `r`, every decay class `(V, R)`, every standard
  additive character `ψ` (`IsStandardAdditiveCharacter`) and every `f ∈ V`,
  `HasWhittakerMajorants F r ψ f`.

## Proof routes (not part of this module)

* (S): induction on the level `j`, with bounds polynomial in heights of the rational factor. An
  iterated derivative along the last column turns `W_f` into `(2πi λ(ξ·v))^K W_f`, where `ξ` is the
  last row of the representative. Finite level confines the nonzero `ξ` to a lattice with
  controlled denominators. Lattice sums of `‖ξ‖^{-K}` converge, and good coset representatives
  have polynomially bounded heights.
* (E): upward induction along the columns of the unipotent radical, using Fourier uniqueness on
  `F^k \ 𝔸^k`. The zero coefficient vanishes by block cuspidality, and the summability of the
  Whittaker terms at every level (a consequence of (S)) justifies every interchange of sum and
  integral.
