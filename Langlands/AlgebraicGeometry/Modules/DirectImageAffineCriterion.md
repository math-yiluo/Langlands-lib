# Direct-image rank and canonical base change from affine data

Let `f : X ⟶ S` be a morphism of schemes in a common arbitrary universe,
let `M` be an ordinary sheaf of modules on `X`, and let `r : ℕ`.
The derived property `DerivedSections.AffineSectionsData f M r` requires the
following data for every affine scheme `Spec R ⟶ S` and every Cartesian
presentation `XR = X ×_S Spec R`, with maps `p : XR ⟶ X` and
`fR : XR ⟶ Spec R`:

- The actual relative sections `Γ_R(XR, p* M)` form a finite projective
  `R`-module.
- Their `Module.rankAtStalk` equals `r` at every prime of `R`.
- For every ring homomorphism `φ : R ⟶ T` and every further Cartesian
  presentation over `Spec T`, the specified `scalarSectionsBaseChangeMap`
  for `p* M` is invertible.

Here relative sections are `relativeGlobalSections`, the composite of the
ordinary sheaf pushforward with `moduleSpecΓFunctor`. The scalar comparison
is the published canonical map, including extension of scalars along `φ`.
The property quantifies over all affine maps to `S`, not just affine open
charts. It is a hypothesis of the criterion, rather than a conclusion about
an arbitrary family.

The implemented consequences are:

- `AffineSectionsData.isLocallyFreeOfRank`: the actual sheaf `f_* M` has
  `Langlands.Scheme.Modules.IsLocallyFreeOfRank` equal to `r`.
- `AffineSectionsData.isIso_baseChange`: for every arbitrary scheme map
  `b : S' ⟶ S` and Cartesian square with upper map `p : X' ⟶ X` and
  vertical map `f' : X' ⟶ S'`, the specified ordinary sheaf morphism
  `pushforwardBaseChange b f f' p h.w M` is invertible.

These two general results need no additional quasi-coherence, finiteness,
compactness or separation assumption on `f` or `M`; their full hypothesis is
`AffineSectionsData`. The final theorem
`pushforward_isLocallyFreeOfRank_and_isIso_pushforwardBaseChange`
specializes to an actual `Picard.LineBundle`, spells out that affine
hypothesis inline, and includes `[QuasiCompact f] [QuasiSeparated f]` to
match its consumer interface. Those two typeclass hypotheses are not needed
by the proof once the stated affine data have been supplied.

For the proof, `AffineSectionsData.isQuasicoherent` first obtains
quasi-coherence of each affine-base direct image from its canonical scalar
comparisons for principal-open localizations. The previously constructed
affine criterion then identifies invertibility of its actual sheaf comparison
from invertibility of the scalar comparison. Quasi-coherence of the target
is transported along the canonical composition isomorphism for pullbacks.
This proves `AffineSectionsData.isIso_affineBaseChange`.

For arbitrary base change and a point `y : S'`,
`exists_affineOpenFactorization` chooses an affine open map `c : Spec T ⟶ S'`
through `y`, an affine open map `x : Spec R ⟶ S`, and `φ : R ⟶ T` such that
`c ≫ b = Spec.map φ ≫ x`. The construction restricts `b` to affine
neighborhoods and uses full faithfulness of `Spec` for the ring map.
The proof forms the Cartesian pullbacks over both charts. Pasting and
cancellation show that the induced intermediate square over `Spec.map φ`
is Cartesian. Its affine comparison and the open-base comparison for `x`
are invertible. The composition identity for the specified
`pushforwardBaseChange` identifies their composite with the comparison for
the outer square. Transport along the equal base and upper maps gives the
same outer comparison obtained from `b` and `c`. Cancelling the invertible
open-base comparison for `c` proves that `c*` of the comparison for `b` is
invertible. Finally `isIso_of_affineOpenPullbacks` passes through the
restriction/pullback natural isomorphism, the restriction stalk comparison,
and stalk detection of isomorphisms. Thus the result concerns the actual
published morphism, rather than a separately chosen isomorphism between its
endpoints.

For the rank conclusion, choose an affine open chart through a point of `S`.
The finite projective relative sections of its Cartesian pullback have
constant stalk rank `r`. The affine fixed-rank result produces a neighborhood
with a free sheaf on `ULift (Fin r)`. The open-base comparison identifies the
sheaf on the affine chart with the pullback, and hence the restriction, of
`f_* M`. Restrict this comparison to the free neighborhood and compose the
restrictions. The construction `freeChartOnOpensRange` transports such a
chart along the isomorphism between an open immersion's source and its open
image, using restriction composition and pullback of the free sheaf. This
gives an actual free neighborhood through the original point. The earlier
`isLocallyFreeOfRank_of_freeNeighborhoods` assembles these charts into local
generators with bases of exactly the prescribed size.

This is a derived sheaf-theoretic construction from the existing affine
sections, restriction, canonical base-change and fixed-rank modules, together
with Mathlib's affine charts, pullbacks, restriction adjunctions and free
sheaf pullback. It asserts no new external-source geometry theorem and has
no separate literature citation. It is the sheaf-level component of the
ordinary cubic direct-image proof: it does not supply the affine sections
hypothesis, fibre vanishing or the numerical value of the cubic rank, and
does not by itself prove `CubicDirectImageStatement`.
