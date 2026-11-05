# Iwasawa decomposition with the same available special compact witnesses

Author: Worker 1265. The shared existential formulation and dependent torus,
apartment and standard-Levi identifications are adapted from Worker 1249's
`SpecialCompact.AvailableExistenceStatement`.

`Langlands.BruhatTits.Iwasawa.IwasawaExistenceStatement` is a Prop-valued
statement target for the general connected reductive local-field
specialization of KP Theorem 5.3.4, together with the same special maximal
compact subgroup used by the sibling special-compact target. It concludes
existence of the geometric data and the required decompositions. It is not
a proof, and the sibling existence assertion is not a premise.

## Scope and witnesses

For every universe `u`, the only initial data are:

- `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]` and
  `[IsNonarchimedeanLocalField F]`;
- an actual `F`-group scheme `G` with `hG : IsConnectedReductive G`;
- an explicitly chosen commutative group scheme `S` and
  `i : S.toGrp ⟶ G` with `hi : IsMaximalSplitTorus i`;
- `ν : cocharacterLattice S` with `IsGenericCocharacter i ν`.

The affine and mono instances come from `hG.isAffineHom` and
`hi.isSplitSubtorus.mono`. Genericity fixes the positive relative roots, the
simple roots and the standard minimal parabolic `P_∅`. There is no
characteristic, splitness, quasi-splitness, tameness, residue-characteristic
or positive relative-rank restriction.

The conclusion supplies a single assignment
`𝔅 : KPBuildingAssignment.{u}`, apartment data
`D : KPApartmentData i (localFieldOrder F)` and a special apartment vertex
`x : D.Apartment`. Write `B := (𝔅.datum F G hG).base`. Required conclusions
include:

1. `𝔅.IsAvailableFor F G hG`;
2. `B.S = S`, `HEq B.i i` and `HEq B.apartment D`;
3. `D.IsSpecialApartmentVertex x`;
4. `SpecialCompactProperties F i ν (D.specialCompactSubgroup x)`.

Availability means all ten corrected Definition 4.1.26 axiom groups:
4.1.1, 4.1.2, 4.1.4, 4.1.6, 4.1.8, 4.1.9, 4.1.16, 4.1.17, 4.1.20 and
4.1.22. This includes the comparisons across groups and valued-field
isomorphisms. Neither partial apartment axioms nor a one-group validity
predicate replaces it. The target requires availability at `G` and its
specified standard Levis, without requiring the stronger global `𝔅.IsValid`.
The assignment may depend on the chosen inputs, including the torus.

The equality and heterogeneous equalities identify the dependent triple
`(B.S, B.i, B.apartment)` with `(S, i, D)`. The data defining the compact
subgroup are therefore the available data themselves. In particular, one
cannot supply an unrelated apartment or an unrelated compact subgroup.

## The same parahoric and compact factor

The compact subgroup is the existing geometric object

\[
K_0=D.\mathrm{specialCompactSubgroup}(x)
   =G(F)^1\cap\mathrm{Stab}(D.\mathrm{apartmentMap}(x)).
\]

`SpecialCompactProperties` retains the sibling's full package for this
one subgroup: algebraic boundedness, openness, maximality among all
bounded subgroups, compactness, maximality among all compact subgroups,
relative Weyl representatives and the literal standard-parabolic
intersection factorizations.

The conclusion also supplies `xB : B.Apartment` with `HEq xB x` and the
explicit equality
`B.apartment.specialCompactSubgroup xB = D.specialCompactSubgroup x`.
This identifies the chart point at which the actual parahoric is evaluated.
For the actual subgroup `P_x := B.parahoricAt xB`, the target states

\[
G(F)=P(F)P_x=P_xP(F),\qquad
P_x\leq K_0,\qquad
G(F)=P(F)K_0=K_0P(F).
\]

The point witness is an identification of existing geometric objects,
not an assumption of a decomposition. The parahoric uses the published
construction `Z(F)^0 · G(F)^♯_x`. It is not the full reduced fixer or the
compact stabilizer. In particular, the target does not equate `P_x` and
`K_0`. KP's discussion after Definition 4.1.3, printed p.158 / PDF p.189,
explicitly allows the zero fixer to be smaller than the norm-one fixer.
Remark 7.4.2, PDF p.286, concerns the separate sharp-fixer/parahoric
distinction.

For every `y : B.ReducedBuilding` with `B.IsSpecialPoint y` and
`B.IsVertex y`, and every actual `Q` with `B.IsParahoricAt y Q`, a further
conjunct states both product orders for `Q`, the inclusion
`Q ≤ B.compactStabilizer y`, both products for that same stabilizer, and
its compact-open maximality. `IsParahoricAt` is the published relation
obtained by conjugating an apartment parahoric and translating its point.
Thus the general-group target retains every special vertex of the whole
constructed reduced building, in addition to the distinguished witness `x`.

Each product assertion is `ParabolicPointProductFamily i ν K`, with `K`
fixed across all six families from `Iwasawa.PointProducts`: every actual
algebraic parabolic inclusion, every `Dynamic.parabolic`, every standard
`P_J` for `J ⊆ simpleRelativeRoots i ν`, and each of the three rationally
conjugated families. Its two equalities use literal pointwise products
of subsets of `rationalPoints G`; no subgroup join replaces multiplication.
Empty and full `J`, improper parabolics and relative rank zero are included.

The imported `Rational.ParabolicPointConjugation` gives the actual
rational-point conjugation adapters. The standard conjugate uses pullback
along `(G.innerIso g).inv`, giving `g P_J(F) g⁻¹`; pullback along the
forward map would have the opposite orientation. No conjugation
certificate is an added premise.

## Every standard Levi retains these witnesses

For every `J ⊆ simpleRelativeRoots i ν`, set
`M_J := Standard.leviScheme i ν J` and
`iM := Standard.leviTorusHom i ν J`. The target supplies:

- `hM : IsConnectedReductive M_J`;
- `DM : KPApartmentData iM (localFieldOrder F)` and
  `𝔅.IsAvailableFor F M_J hM` in the same assignment;
- the same dependent torus and apartment identifications for this Levi;
- `xM : DM.Apartment` with `SpecialLeviRestriction F ν D x J DM xM`.

These are exactly the inherited geometric and special-compact obligations
of `SpecialCompact.AvailableSpecialMaximalCompactExistence`. Reductivity is
existential because the current Library has no unconditional theorem
providing it for the actual standard Levi representative. It is not an
extra initial assumption.

`SpecialLeviRestriction` says that `xM` is a special vertex obtained by
restricting the root-datum valuation at `x`, its compact subgroup has
`SpecialCompactProperties`, and

\[
K_{0,M}=DM.\mathrm{specialCompactSubgroup}(x_M)
       =D.\mathrm{specialCompactLeviSubgroup}(\nu,J,x).
\]

This is the preimage of the original `K_0` under the actual inclusion
`M_J(F) → G(F)`. The published `specialCompactLeviSubgroup_map`
identifies its image with the literal subgroup `K_0 ∩ M_J(F)`.
The target then adds a point `xBM` in the available Levi apartment with
`HEq xBM xM`, equality of the compact stabilizers, both product orders
for the actual Levi parahoric at `xBM`, its inclusion in `K_{0,M}`, and
both product orders for this same `K_{0,M}`. These products range over
all six actual-parabolic families inside `M_J(F)` using `iM` and the
original `ν`.

No subgroup is chosen after the parabolic, and no fresh ambient `x` or
`K_0` is chosen for a different `J`. Forgetting the added Iwasawa and
parahoric conjuncts leaves the sibling's existential package with the same
witnesses. This is a statement-level strengthening; no Lean implication or
existence proof is claimed here.

## Canonical topology and Renard consumer

The topology is
`Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F G.X`,
and the analogous topology on each actual `M_J`. The imported
`SpecialCompactProperties` and `IsCompactOpenMaximal` install those
topologies locally, using the affine instances supplied above.
Maximality uses Mathlib's
`Maximal (fun L : Subgroup (rationalPoints G) => IsCompact (L : Set _)) K_0`;
it compares all compact overgroups. Algebraic boundedness is the separate
KP Definition 2.2.1 notion. The bounded/compact comparison is a result to
prove from KP Fact 2.2.3, not a hidden premise.

Renard V.5.1(1), row S19(1) in
`notes/renard/chapter-v-structural-inputs.md`, follows at the statement
level by taking `J = ∅` in the ambient standard family:
`G(F) = K_0 P_∅(F) = P_∅(F) K_0`. The subgroup is the very same
open maximal compact subgroup that has the sibling's Weyl and factorization
properties. The per-Levi clause supplies these Iwasawa products for
`K_0 ∩ M_J(F)` inside the actual Levi, as required for the Iwasawa part of
V.5.1(5). The source's minimal-parabolic intersection comparison is the
separate published statement target
`Langlands.GroupScheme.StandardLeviMinimalParabolicCompatibilityStatement`
in `Langlands.Geometry.Building.SpecialCompactLeviMinimalParabolicStatement`;
its proof is a separate obligation.

## Sources and provenance

This packages the sibling's source-backed existence target with the
conditional `Iwasawa.AvailableIwasawaStatement`, rather than assuming
either proposition.

- Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered
  `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
  `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
  Chapter 5 standing hypotheses, printed p.186 / PDF p.217, and
  Theorem 5.3.4, printed pp.190–191 / PDF pp.221–222, supply the
  parahoric products for every special vertex and every parabolic.
  Theorem 4.2.15(1), PDF pp.204–205, supplies maximal bounded
  stabilizers; Fact 2.2.3, PDF p.101, gives the local-field
  bounded/compact comparison. Definition 7.4.1(4), PDF p.286, defines
  the parahoric. The discussion after Definition 4.1.3, PDF p.189,
  distinguishes it from the norm-one stabilizer. Lemma 6.7.1 and
  §6.7.2, PDF pp.264–265, restrict the apartment valuations and
  preserve special points, whose images are vertices.
  Chapter 9, PDF p.354, assumes a discrete valuation with Henselian
  valuation ring and perfect residue field; every nonarchimedean local
  field satisfies these hypotheses. Theorem 9.2.7, PDF p.360, with
  its proof in §9.5, PDF pp.394–395, supplies the general availability
  source. The book's displayed axiom list is shorter than the corrected
  definition; §9.5 also verifies 4.1.2 and 4.1.8 but does not name
  4.1.16. As in the sibling target, this target requires the entire
  corrected ten-axiom conclusion, including 4.1.16.
- *Corrections and additions*, 1 November 2024, registered
  `kaletha-prasad-2024-corrections`, SHA-256
  `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.
  PDF p.27 replaces Definition 4.1.26 with the ten-axiom list used
  by `IsAvailableFor`. PDF p.30 corrects the proof of 5.3.3 and
  replaces 5.3.5, without changing 5.3.4. PDF p.33 requires AS 5
  in Chapter 7. None of these neighboring results is a premise of
  this Iwasawa target.
- Renard, *Représentations des groupes réductifs p-adiques*, 9 July 2026
  edition, registered
  `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
  V.5.1, printed p.122 / PDF p.128: (1) is Iwasawa, (2),(3)
  are the sibling compact-subgroup properties, and (5) is inheritance
  by the standard Levis.

The existential packaging and dependent point identifications are
internal formulation choices. Dynamic, standard and conjugate products
specialize the algebraic-parabolic source through the current Library's
actual constructions. General building construction, the corrected
Chapter 9 verification, Iwasawa proofs, Cartan decomposition and
compactness of `G/P` remain separate proof obligations.
