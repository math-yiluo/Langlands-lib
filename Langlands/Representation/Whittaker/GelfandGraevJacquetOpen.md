# The open orbit piece of the Jacquet module of a Gelfand–Graev representation

Written by Worker 1832 for task `d7c75f29-8641-4f6e-9a08-aaa69f1db69c`. This module proves
`GelfandGraevOpenPieceStatement` (module `GelfandGraevJacquetOpenStatement`). Combined with
`gelfandGraevJacquet_of_openPiece` (module `GelfandGraevJacquet`), this gives
`RankinSelberg.SupercuspidalCompleteness.GelfandGraevJacquetStatement`.

## Setting

`B` is a block shape. `P = B.parabolic K` is the upper block parabolic with Levi
`M = B.Levi K`, Levi projection `r = B.leviProjection K`, Levi section
`s = B.leviInParabolic K` and unipotent radical `U = B.unipotentRadical K = ker r`. `N` is the
upper unipotent subgroup of `GL_n(K)`, `w = B.reverseMatrix K` is the block-reversal matrix, and
`H = orbitStabilizer N P w = {x ∈ P : w⁻¹ x w ∈ N} = P ∩ w N w⁻¹`. Since `N w⁻¹ x = N w⁻¹` if and
only if `w⁻¹ x w ∈ N`, `H` is the stabilizer of the coset `N w⁻¹` under right translation by
`P`. So `c-Ind_H^P (ψ_N ∘ Ad(w⁻¹))` is the Mackey piece of the double coset `N w⁻¹ P`, the open
one (module `GelfandGraevJacquetOrbits`). `N_M = leviUpperUnipotent B` is the product of the
block upper unipotent subgroups of `M`, and `ψ_M = leviWhittakerCharacter B ψ` is the product of
the blockwise entrywise characters.

## Results

Section `Stabilizer`, over any field `K`:
- `openPieceToOpenStabilizer`: the map `x ↦ w⁻¹ x w`, from `H` to the Library's open stabilizer
  `openStabilizer B K = N ∩ w⁻¹ P w`.
- `openPieceToOpenStabilizer_inducing`: conjugating back by `w` recovers `x`.
- `openStabilizerEquiv_openPieceToOpenStabilizer`: the Library equivalence
  `openStabilizerEquiv B K` from the open stabilizer to `∏ N_(B.size i)` sends the image of `x` to
  the blocks of `r x`.
- `openPiece_leviProjection_mem`: every block of `r x` is upper unitriangular for `x ∈ H`.
- `openPiece_eq_leviInParabolic`: every `x ∈ H` equals `s (r x)`. So `H ⊆ s(N_M)`.
- `leviInParabolic_mem_openPiece`: if every block of `l ∈ M` is upper unitriangular, then
  `s l ∈ H`. So `H = s(N_M)`.
- `openPiece_character`: for `x ∈ H` with block components `i j` of `r x`, the entrywise
  character satisfies `entrywiseCharacter ψ n (w⁻¹ x w) = ∏ j, entrywiseCharacter ψ (B.size j) (i j)`.

Section `Transport`, for general groups:
- `compactInducedCongrSubgroup`: compact induction from equal subgroups `K = K'` is equivalent
  when the coefficients are equivalent along the inclusion `K → K'`.
- `coinvariantsTrivialEquiv`: when every group element acts trivially, the coinvariants are
  linearly equivalent to the space itself. `coinvariantsTrivialEquiv_mk` says that the class of
  `v` goes to `v`.
- `characterRepresentationEquiv`: a linear equivalence `e : V ≃ ℂ` with
  `e (κ k v) = θ(k) • e v` for all `k` and `v` is an equivalence of `κ` with
  `characterRepresentation θ`.

Section `Normalized`, over a `p`-adic field with topological data `T`:
- `parabolicNormalizedJacquet_eq_twist`: `parabolicNormalizedJacquet T B ρ` equals the twist of
  `Parabolic.leviCoinvariants B ρ` (the Levi acting on the `U`-coinvariants through `s`) by
  `Jacquet.inverseHalfCharacter (T.leviModulus B)`, i.e. by `δ_P^(-1/2)`.
  `parabolicNormalizedJacquetTwistEquiv` is the same identity as an equivalence.
- `leviModulus_eq_one_of_upperUnipotent`: `T.leviModulus B l = 1` when every block of `l` is
  upper unitriangular.

Main results:
- `gelfandGraevOpenPiece : GelfandGraevOpenPieceStatement.{uF}`. For every `p`, `F` with its
  canonical topology, `ψ`, `n` and `B : BlockShape (n + 1)`, the normalized Jacquet module of
  `c-Ind_H^P (ψ_N ∘ Ad(w⁻¹))` is equivalent to `leviGelfandGraev B ψ.complex`, as
  representations of `M`.
- `gelfandGraevJacquet : GelfandGraevJacquetStatement.{uF}`, which is
  `gelfandGraevJacquet_of_openPiece gelfandGraevOpenPiece`.

## Proofs

- Stabilizer section. Conjugation by `w⁻¹` maps `H` into `N ∩ w⁻¹ P w`. The Library's
  `openStabilizerEquiv_apply_val`, `openStabilizerEquiv_symm_apply_val` and
  `openStabilizerEquiv_character` describe that stabilizer through the blocks of the Levi
  projection. Transporting these identities back along conjugation by `w` gives the statements
  about `H`.
- `parabolicNormalizedJacquet_eq_twist`: evaluate both sides on a class `[v]`.
  `Jacquet.normalizedActionOfModulus_mk` and `B.topModulus_leviToTop` turn the left side into
  `(√(δ_P(m)))⁻¹ • [ρ(s m) v]`. `Jacquet.inverseHalfCharacter_apply` turns the right side into
  the same expression.
- `leviModulus_eq_one_of_upperUnipotent`: every block has determinant norm `1`
  (`Derivative.TopLocalization.determinantNorm_upper`). So `l` lies in `T.normOneLevi B`, which is
  contained in the kernel of `T.leviModulus B` (`normOneLevi_le_ker_leviModulus`).
- `gelfandGraevOpenPiece`. Let `T = F.canonicalTopologicalData`, `σ = ψ_N ∘ stabilizerToInducing`
  and `Q = r⁻¹(N_M)`.
  1. Smoothness of `σ`. `stabilizerToInducing` is `x ↦ w⁻¹ x w`, which is continuous. The
     standard character is continuous, so its kernel is open.
  2. Subgroups. `N_M` is closed as a product of the closed subgroups `UpperUnipotent.isClosed`
     (`Subgroup.coe_pi`, `isClosed_set_pi`), so `Q` is closed. `ker r ≤ Q`. `H ≤ Q` by
     `openPiece_leviProjection_mem`. `H` is closed (`isClosed_orbitStabilizer`).
     `s l ∈ H` for `l ∈ s⁻¹(Q)` by `leviInParabolic_mem_openPiece`. Since `r ∘ s = id`,
     `s⁻¹(Q) = N_M`.
  3. Measure data on the kernel of the retraction `rP = splitStagesRetraction r s _ Q _` of `Q`
     onto `s⁻¹(Q)`. `splitStagesKernelContinuousEquiv` identifies `ker rP` with `U`, both
     topologically and as groups. This gives local compactness of `ker rP`. It also gives the two
     covering facts below, transported from `U`:
     - every element of `ker rP` lies in a compact open subgroup (`Parabolic.unipotentFiniteContainment`);
     - compact open subgroups form a neighborhood basis of `1` (`T.unipotentRadicalCompactOpen`).
     The intersection `I` of `ker rP` with `H` is closed. Hence regular Haar measures on `ker rP` and
     on `I` are right invariant (`Haar.compactOpenCoverUnimodularity`).
     `compatibleMeasureExists` supplies a compatible regular quotient measure on `I \ ker rP`.
     Compact open subgroups of `P` form a neighborhood basis (`T.parabolicCompactOpen`), and
     `ker r = U` is closed.
  4. `Induction.splitStagesCompactEquiv` (compact induction in stages through `Q`, then
     integration over the kernel) gives an equivalence of `M`-representations
     `E1 : ((c-Ind_H^P σ)_U as M-rep through s) ≅ c-Ind_{s⁻¹(Q)}^M κ`. Here
     `κ = χ · splitKernelCoefficientAction rP sP (H ∩ Q) _ σ_Q`, with `χ` the complex character of
     the Haar ratio `splitKernelHaarRatio`. The coefficient space is the coinvariants of `σ` on
     `I`.
  5. `I` is trivial. An element `i` of `I` lies in `H` and has `r i = 1`, so
     `i = s (r i) = 1` by `openPiece_eq_leviInParabolic`. Hence `σ` acts trivially on `I`, and
     `coinvariantsTrivialEquiv` identifies the coefficient space with `ℂ`.
  6. The Haar ratio is trivial on `s⁻¹(Q)`. By `splitKernelHaarRatio_apply` it is the quotient
     of two Haar characters. The numerator is the Haar character of an automorphism of the
     trivial, hence compact, group `I`, so it is `1` (`mulEquivHaarChar_eq_one_of_compactSpace`).
     The denominator is the Haar character of conjugation by `sP l` on `ker rP`. Along
     `splitStagesKernelContinuousEquiv` it is conjugate to `u ↦ s(l)⁻¹ u s(l)` on `U`
     (`Geometric.haarChar_eq_of_conjugacy`). As a map this is `B.leviAction F.Carrier l⁻¹`. By
     `glBlockModulusHaar` it scales Haar measure by `T.leviModulus B l⁻¹`, which is `1` by
     `leviModulus_eq_one_of_upperUnipotent`. So the map preserves Haar measure, and
     `mulEquivHaarChar_eq` with `haarScalarFactor_self` gives `1`.
  7. The normalizing character `δ' = Jacquet.inverseHalfCharacter (T.leviModulus B)` is trivial
     on `N_M`, since its kernel is the kernel of `T.leviModulus B`
     (`Jacquet.inverseHalfCharacter_ker`). It is smooth, since that kernel is open
     (`T.isOpen_ker_leviModulus`).
  8. On the class of `v ∈ ℂ`, an element `l ∈ s⁻¹(Q)` acts through `δ'(l) χ(l)` and
     `splitKernelCoefficientAction_mk` by `σ(s l) v`. By steps 6 and 7 the scalars are `1`.
     `σ(s l) = ψ_N(w⁻¹ s(l) w)`, which equals `ψ_M(l)` by `openPiece_character` and
     `leviWhittakerCharacter_apply`. So `characterRepresentationEquiv` gives an equivalence of
     `δ'|_{s⁻¹(Q)} · κ` with `ψ_M` restricted along `s⁻¹(Q) = N_M`.
  9. Assembly:
     - `parabolicNormalizedJacquetTwistEquiv` rewrites the normalized Jacquet module as
       `δ' · (U-coinvariants through s)`, and `twistEquiv δ' E1` carries this to
       `δ' · c-Ind_{s⁻¹(Q)}^M κ`;
     - `Induction.compactInductionTwistEquiv` moves the smooth character `δ'` inside the
       compact induction, giving `c-Ind_{s⁻¹(Q)}^M (δ'|_{s⁻¹(Q)} · κ)`;
     - `compactInducedCongrSubgroup`, applied with `s⁻¹(Q) = N_M` and step 8, identifies the
       result with `c-Ind_{N_M}^M ψ_M = leviGelfandGraev B ψ.complex`.

## Provenance

This is the classical computation of the open-cell contribution to the Jacquet module of a
Gelfand–Graev representation: the open double coset `N w⁻¹ P` has stabilizer
`P ∩ w N w⁻¹ = s(N_M)`, and the character `ψ_N ∘ Ad(w⁻¹)` restricts to `ψ_M`. The inverse
matters: block reversal need not be an involution when the block sizes differ, and `N w P` can
then be a different double coset with a different stabilizer. Integration over `U` identifies the
`U`-coinvariants of `c-Ind_{s(N_M)}^P` with `c-Ind_{N_M}^M`. The modulus and the Haar ratio are
trivial on the unipotent group `N_M`, so no twist survives. See Bernstein–Zelevinsky's geometric
lemma and Bushnell–Henniart's treatment of Whittaker models. The auxiliary transport,
coinvariant and normalization lemmas are internal.
