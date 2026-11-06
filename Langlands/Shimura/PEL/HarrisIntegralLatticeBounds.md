# Integer bounds for carried Harris Tate submodules

Author: Worker 344.

This internal construction proves that the submodule carried by an original
Harris fixed level is compact and open in the existing rational Tate topology,
and constructs a positive integer giving both commensurability inclusions
with the full integral Tate rationalization image. These facts are proved
from the actual compatible frame and existing geometric finite-level inputs.
No Tate-rank or normalized-model existence hypothesis is introduced.

## Exact inputs and carriers

The arithmetic types, schemes and point fields have universe zero. The
arithmetic data retain the displayed totally real number field `E`, totally
complex quadratic extension `F`, central simple unitary datum `D` on `A`,
Harris signature charts `C`, and algebra and scalar-tower instances. There
is no division or CM-section specialization. The source is
`Vf = (Global.FiniteAdeles ℚ) ⊗[ℚ] A` with its canonical finite-adelic
`moduleTopology`. Write `Af` for this actual finite-adele ring, `Rf` for its
actual subring `Global.integralFiniteAdeles ℚ`, and `Λf` for the existing
`D.harrisHodgePELIntegralAdeleSpan C`.

The target constructions take `P : Prerequisites`, a quasi-separated base
scheme `S`, the relative finite Weil-transition statement, and the rational
profinite-integer/finite-adele comparison `h`. A point
`s : Spec Ω ⟶ S` is supplied for an arbitrary field `Ω`. Compatible frames
use the unchanged positive auxiliary involution, rational action and Harris
form of a supplied `PositivePolarizedAction X`. The target topology is the
existing `Tate.rationalTopology` on the full rational Tate carrier, with
index predicate `fun _ => True`. It is not a topology transported by fiat
through the frame.

The frame compactness theorem needs no finite-fibre or torsion assumptions.
The frame openness and integer-bound theorems additionally take `hs`, finite
fibres at `s` for every finite-etale cover of `S`; the torsion finite-etale
statement `htor`; and `hu`, invertibility on `S` of every positive torsion
index. These are the inputs to the existing local compactness of the actual
rational Tate carrier. Algebraic closedness, connectedness and local
Noetherianity are not required here.

The fixed-level declarations also retain finite and etale roots-of-unity
instances for every positive index, as required by the existing
`PolarizedWeilLevel.levelTower`. They take a level `K`, a proof that
`K.toSubgroup ≤ harrisIntegralAdeleStabilizer D C`, and an original fixed
level orbit `x`. They use exactly the existing `harrisIntegralLevelLattice`
and original right action; no normalization condition is assumed.

## Compact source and continuity of the actual frame

The private source helpers prove the topological ingredients explicitly.
The finite-adele ring is sigma-compact because it is a countable union of
rational multiples of its compact integral subring. To obtain that covering,
`adele_sigmaCompact` applies the existing rationalization chart theorem to
`h.rationalEquiv.symm z` and uses the coupled integral/rational comparison
formula. Each multiple is compact by continuity of multiplication by the
fixed rational adele. The rational coefficient varies only as a countable
covering index; no continuity from a real-topologized rational field is used.

A finite integer basis of the existing integer Harris pairing lattice extends
to a rational basis of `A`. Its finite-adelic base change gives a basis of
`Vf`. Reconstruction from the finite product of `Af` through that basis is
continuous for the canonical module topology and surjective, so `Vf` is
sigma-compact.

`sourceSpan_fg` identifies `Λf` with the `Rf`-span of the finitely many tensors
`1 ⊗ b_i` from that integer basis. Expansion in the integer basis proves one
inclusion using closure under integer multiplication; the other is generator
membership in the original source span. Thus the source span is finitely
generated over the actual compact ring `Rf`. Restriction of its continuous
`Af` scalar action to `Rf` and `Submodule.isCompact_of_fg` prove compactness
in `sourceSpan_compact`.

The private `frameFiniteAdeleMap` bundles the underlying compatible frame as
`Af`-linear. It specializes its original tensor-algebra linearity to
`1 ⊗ r`. The public source scalar identity and the actual target tensor
algebra action identify this with finite-adelic scalar linearity; the order
action of one and finite-adelic action of one are their original identity
operators. The target's existing finite-adele scalar action is jointly
continuous by `Tate.finiteAdeleModule_continuousSMul`, and its addition is
continuous in `rationalTopology`. Therefore the module-topology universal
property proves `frame_continuous` for the actual underlying frame map.

## Compactness and openness of carried submodules

`harrisIntegralFrameLattice_isCompact` applies that continuity to the compact
source span. Its image is literally the existing carried frame submodule,
by its `Submodule.map` definition.

`harrisIntegralFrameLattice_isOpen` uses the additive-group open mapping
theorem `AddMonoidHom.isOpenMap_of_sigmaCompact` on the actual frame. Its
source is the sigma-compact topological additive group just constructed.
Its target is the existing Hausdorff rational Tate topological additive
group. The displayed geometric finite-level inputs supply local compactness,
hence the Baire property. Frame surjectivity is part of the supplied linear
equivalence. This proves the underlying frame is open. Applying it to the
already published openness of `Λf` proves openness of the carried submodule.
No inverse continuity assumption or Tate-rank statement enters the proof.

`harrisIntegralLevelLattice_compactOpen` takes any representative of the
original fixed orbit, rewrites the already descended submodule with
`harrisIntegralLevelLattice_eq_frame`, and applies these two frame theorems.
The properties consequently concern the submodule attached to that original
orbit. The representative is used only to prove the properties.

## Both integer inclusions and the chosen bound

The private `compact_open_bound` is an additive-group argument. If `J` is a
compact subgroup and `K` is an open subgroup of a topological additive
commutative group, the pullback of `K` to `J` is open. Its quotient in the
compact group `J` is discrete and compact, hence finite. The quotient has a
positive cardinality because it is inhabited. Multiplication by that index
sends every element of `J` into `K`, by `AddSubgroup.nsmul_index_mem`.

The full integral Tate rationalization image is the actual additive subgroup
range of `GroupScheme.Tate.toRational ... (fun _ => True)`.
`Tate.rationalFull_compactOpen_integral` supplies its compactness and openness
under `hs`, `htor` and `hu`. Apply the preceding argument first with this
integral image as `J` and the carried submodule as `K`, and then in the
opposite order. Multiplying the two positive bounds gives one bound for both
inclusions, using additive-subgroup closure under natural multiplication.
This is `harrisIntegralFrameLattice_integerBounds`.

`harrisIntegralLevelLattice_integerBounds` transfers that result through the
original representative evaluation formula. The definition
`harrisIntegralLevelLatticeBounds X K hK x` chooses a member of the resulting
subtype. Its value is a natural number `m` with proofs of `0 < m` and exactly
these two assertions:

- For every member `y` of the full actual integral Tate group of `X` at `s`,
  `m • toRational y` belongs to the original level's carried submodule.
- For every rational Tate vector `w` in that carried submodule, some member
  `y` of the full actual integral Tate group satisfies
  `toRational y = m • w`.

Natural multiplication here is repeated addition on the existing rational
Tate carrier. The output is a chosen bound and its proved inclusions, not an
optimal bound or a claim of naturality of this choice under pullback. The
original orbit determines the submodule being bounded. The definition takes
no chosen representative as an argument.

## Provenance and remaining construction

The provenance is internal. The proofs derive these properties from the
existing Harris integer lattice and source span, the coupled actual scalar
comparison, canonical module topology, actual Tate topology and scalar
continuity, and published general compactness and open mapping results.
They introduce no external geometric existence assertion or new axiom.

The result discharges the two boundedness hypotheses for the carried lattice
in the planned generic commensurable invariant lattice realization interface.
It does not construct an isogenous model, identify any abelian scheme's full
integral Tate image with this submodule, or reflect rational morphisms to
actual integral morphisms. Model realization, order and polarization descent,
the determinant condition, normalized-model existence and the exact division
representability theorem remain separate obligations.
