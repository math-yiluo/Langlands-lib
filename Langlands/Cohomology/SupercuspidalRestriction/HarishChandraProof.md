# Harish-Chandra's theorem for supercuspidal representations of `GL_n(F)`

Module `Langlands.Cohomology.SupercuspidalRestriction.HarishChandraProof`.

## Theorem proved

`Langlands.Cohomology.SupercuspidalRestriction.glHarishChandraStatement_proof
(F : PadicField.{0} p) (n : ℕ) : GLHarishChandraStatement F n`, for a natural
number `p` with `[Fact p.Prime]`. The prime `p` is implicit; `F` and `n` are
explicit. The theorem has no universe parameters: the field lives in `Type`, and
the target statement fixes `π : SmoothRep.{0, 0, 0} ℂ (GeneralLinear n F.Carrier)`.
There are no hypotheses beyond those of the statement.

The target statement `GLHarishChandraStatement F n` (module
`Langlands.Cohomology.SupercuspidalRestriction.Statement`, unchanged) uses the
canonical topologies `F.canonicalTopologicalData.topology` on `F.Carrier` and
`F.canonicalGeneralLinearTopology n` on `GeneralLinear n F.Carrier`. It says that
every smooth complex representation `π` with
`GeneralLinear.IsSupercuspidal π.representation` satisfies
`HasCompactSmoothCoefficientsModCenter π.representation`. Supercuspidal means
admissible, with zero Jacquet coinvariants for every proper block parabolic and
every conjugate of its unipotent radical. The conclusion means: for every smooth
dual vector `ℓ` and every vector `v` there is a compact set
`C ⊆ GeneralLinear n F.Carrier ⧸ Subgroup.center _` that contains the image of
every `g` with `matrixCoefficient π.representation ℓ v g ≠ 0`. Irreducibility is
not assumed.

This is the direction (1) ⇒ (3) of Harish-Chandra's theorem in Bernstein–Zelevinsky
1976, Theorem 3.21, printed pp. 34-35 (source
`bernstein-zelevinsky-1976-representations-gln`), with the subgroup `G°` and its
properties from 3.20, printed p. 34. Bernstein and Zelevinsky state 3.21 for
quasi-cuspidal representations, which need not be admissible. The Library's
supercuspidal predicate includes admissibility, and the proof below uses it.

## Auxiliary lemma

`exists_isCompact_mk_of_central_orbit_finiteDimensional` holds for any group `G`
in any universe `uG` with a topological group structure, and any complex vector
space `V` in any universe `uV`. Its hypotheses:

- `ρ : Representation ℂ G V`;
- a normal subgroup `H` such that `H ⊔ Subgroup.center G` has finite index;
- a linear form `ℓ : Module.Dual ℂ V` such that for every vector `w` the function
  `h ↦ ℓ (ρ h w)` on `H` has compact support;
- a vector `v` and a finite-dimensional submodule `W` containing `ρ z v` for every
  central `z`.

The conclusion is a compact `C ⊆ G ⧸ Subgroup.center G` containing the image of
every `g` with `ℓ (ρ g v) ≠ 0`.

Proof as implemented. Let `N = H ⊔ Z`, let `r j = j.out` choose a representative
of each of the finitely many cosets `j ∈ G ⧸ N`, and let `b` be the basis
`Module.finBasis ℂ W`, indexed by `Fin (finrank W)`. For each `j` and `i`, let
`S j i ⊆ H` be the closed support (`tsupport`) of `h ↦ ℓ (ρ h (ρ (r j) (b i)))`,
which is compact by hypothesis. The set
`K = ⋃ j, ⋃ i, {h * r j | h ∈ S j i}` is compact because it is a finite union of
continuous images of compact sets. Take `C` to be the image of `K` in `G ⧸ Z`,
which is compact because the quotient map is continuous.

Given `g` with `ℓ (ρ g v) ≠ 0`, write `r j = g * n₀` with `n₀ ∈ N`, for
`j` the coset of `g`. Since `H` is normal, `n₀⁻¹ = h * z` with `h ∈ H` and `z`
central (`Subgroup.mem_sup_of_normal_right`). Then `g = h' * r j * z` for the
`H`-element `h' = r j * h * (r j)⁻¹`. Expanding `ρ z v ∈ W` in the basis as
`ρ z v = ∑ i, c i • b i` (`Basis.sum_repr`) gives
`ℓ (ρ g v) = ∑ i, c i * ℓ (ρ h' (ρ (r j) (b i)))`. Some summand is nonzero
(`Finset.exists_ne_zero_of_sum_ne_zero`), so `h' ∈ S j i` for some `i` and
`h' * r j ∈ K`. Since `z` is central, `g` and `h' * r j` have the same image in
`G ⧸ Z` (`QuotientGroup.mk_mul_of_mem`), so that image lies in `C`.

This lemma replaces the central character in the Library's
`GodementJacquet.matrixCoefficient_mem_compactCentralSupportFunctions`, which
needs irreducibility, by a finite-dimensional space containing the central orbit.
It follows the coset argument of that lemma.

## Canonical topologies as named local instances

In the section `GeneralLinearGroup`, the file declares three local instances in
namespace `Langlands.Cohomology.SupercuspidalRestriction`, with the same values
as the first three of the five unnamed local instances of `Statement.lean`:

- `harishChandraCarrierTopology : TopologicalSpace F.Carrier`, equal to
  `F.canonicalTopologicalData.topology`;
- `harishChandraGLTopology n : TopologicalSpace (GeneralLinear n F.Carrier)`,
  equal to `F.canonicalGeneralLinearTopology n`;
- `harishChandraGLTopologicalGroup n : IsTopologicalGroup (GeneralLinear n
  F.Carrier)`, equal to `F.canonicalGeneralLinearTopologicalGroup n`.

They have explicit, module-specific names because Lean names an unnamed instance
from its type. The unnamed local instances of `Statement.lean` already have the
names `instTopologicalSpaceCarrier`, `instTopologicalSpaceGeneralLinearCarrier`
and `instIsTopologicalGroupGeneralLinearCarrier`. Unnamed copies here would get
the suffix `_1`. `UnitDeterminantProof` declares unnamed copies of the first two,
named `instTopologicalSpaceCarrier_1` and
`instTopologicalSpaceGeneralLinearCarrier_1`. So in the earlier version of this
file, which had unnamed instances, a module importing both proof modules failed
with a duplicate-declaration error. With the explicit names, this module can be
imported in one module together with
`Langlands.Cohomology.SupercuspidalRestriction.UnitDeterminantProof` and
`Langlands.Cohomology.SupercuspidalRestriction.CompactModCenterProof`. The
`instance` attribute is local to the section. Importing modules see the three
declarations only as ordinary definitions, not as instances. The theorem and its
proof are unchanged from that earlier version.

## Proof of the theorem

Fix `π`, a supercuspidality proof `hπ`, a smooth dual vector `ℓ` and a vector `v`,
and split on `n`.

- `n = 0`. Every element of `GeneralLinear 0 F.Carrier` is central, since two
  `0 × 0` matrices are equal (`Matrix.ext` with `Fin.elim0`). So every `g` has the
  image of `1` in the quotient by the center (`QuotientGroup.mk_mul_of_mem`), and
  the compact set is the singleton of that image.
- `n = d + 1`. Let `T = F.canonicalTopologicalData` and `H = (T.determinantNorm
  (d + 1)).ker`, the matrices with `|det| = 1`. The Library theorem
  `GodementJacquet.determinantNorm_ker_sup_center_finiteIndex` gives finite index
  of `H ⊔ Z`. Smoothness of `π` gives an open subgroup `K` fixing `v`. For central
  `z`, the vector `ρ z v` is again `K`-fixed because `k z = z k`. So all central
  translates of `v` lie in `W = fixedVectors π.representation K`, which is finite
  dimensional by admissibility (`hπ.1.2 K`). The Library theorem
  `GodementJacquet.hasCompactSupport_determinantUnit_coefficient` (applied with
  `0 < d + 1`, supercuspidality, and the smoothness of `ℓ`) gives compact support
  on `H` of `h ↦ ℓ (π h w)` for every vector `w`. The auxiliary lemma with
  `ℓ` the evaluation `smoothDualPairing π.representation ℓ` then gives the
  required compact set. Its condition `ℓ (ρ g v) ≠ 0` is definitionally the
  condition `matrixCoefficient π.representation ℓ v g ≠ 0` of the statement.

The topologies used by the two Library theorems agree definitionally with the
canonical topologies of the statement: `F.canonicalGeneralLinearTopology n`
unfolds to the matrix-unit topology induced by `F.canonicalTopologicalData.topology`.

## Comparison with the source route

Bernstein and Zelevinsky prove (1) ⇔ (2) from Lemma 3.22, and (2) ⇒ (3) by
taking supports of matrix elements (printed p. 35). The implemented proof
instead uses the Library's product-Levi Harish-Chandra theorem through
`hasCompactSupport_determinantUnit_coefficient`. That is compact support on `G°`,
the conclusion of 3.21 (4) for the one-block Levi. It passes from `G°` to `G`
modulo the center with the finite representatives of `G / G° · Z` (3.20 b)),
close to the source's argument for (4) ⇒ (2), but controls the center by
admissibility instead of Hecke projections.
