# Isogeny classes of polarized actions with actual Weil levels

This derived construction assembles actual abelian schemes, faithful rational
algebra actions, geometric polarizations and Weil-compatible level orbits. It
constructs their polarized-isogeny quotient and its compact-open transporter
level tower. The definitions are in
`Langlands.Shimura.PEL.PolarizedWeilLevel`.

The original source is Harris–Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Printed p.18 (PDF p.26) defines a rational isogeny as an invertible element of
`Hom(A,A') ⊗ ℚ` and a polarization by its geometric fibres. Section III.1,
printed pp.90–91 (PDF pp.98–99), defines the pointed moduli problem with
faithful action, polarization, involution compatibility and a monodromy-invariant
orbit of compatible adelic frames. Page 91 defines equivalence by rational
isogeny, with polarizations compared up to a rational unit, and the right level
action by precomposition of frames. This module implements those components
for a general rational module and a fixed field-valued base point. The full
Harris specialization requires the additional conditions described below.

Fix a scheme `S : Scheme.{u}`, a ring `D : Type v` with `Algebra ℚ D` and
`StarRing D`, and a rational `D`-module `V : Type w` with compatible scalar
tower. Fix a rational bilinear form `ψ` on `V`. No finite-dimensionality,
alternation, nondegeneracy or specific number-field datum is imposed here.
The polarized object type has universe `max (u + 1) v`; the dependent
level-data and quotient types have universe `max (u + 1) v w`. The level
orbits at a fixed object have universe `max u w`.

The named tensor comparison, composition, unit, associativity, left-unitor
and symmetry statements, Picard-zero pullback stability, Mumford-bundle
Picard-zero statement and Picard-zero universal base-change statement remain
explicit theorem inputs. No proof of these inputs is supplied by this module.
It also retains an explicit finite Weil transition statement, the coupled
rational profinite-integer/finite-adele scalar comparison, the torsion
finite-étaleness statement, invertibility on `S` of every selected positive
torsion order, finite-étaleness of the corresponding root-of-unity group
schemes, and quasi-separatedness of `S`.

`PolarizedAction` consists of the following actual data and properties:

- An object of `RationalAlgebraAction S D`, whose underlying object is an
  actual abelian scheme and whose action is a unital rational algebra map into
  its actual rationalized endomorphism algebra; the map is required to be
  injective.
- Representability data for the existing Picard-zero dual, its actual
  abelian-scheme geometry, and an inverse Poincaré line bundle with evaluation.
  The dual abelian scheme is constructed from these data by the imported API.
- An actual homomorphism `polarization` to that constructed dual, together with
  `IsPolarization`. This predicate includes `IsIsogeny` and an ample Mumford
  presentation after a possible field extension at every algebraically closed
  geometric fibre.
- Additivity of the constructed dual endomorphism map and the actual equation
  `λ ∘ i(b) = i(star b)ᵛ ∘ λ`, interpreted in the actual rational Hom groups.

These fields assert geometric polarization and compatibility; they are not
arbitrary output schemes or arbitrary pairing data. The extra dual witnesses
are retained explicitly as part of a representative. No existence or uniqueness
of all this data is inferred.

Fix `s : Spec Ω → S` with `[Field Ω]` and finiteness of the fibres of all finite
étale covers at `s`. Lean does not require `Ω` to be algebraically closed in
this construction. The intended geometric-point use can additionally impose
that condition. `levelTower X` is the existing
`weilAdelicCompactOpenLevelTower` for the actual action and polarization of
`X`. Its index is `FiniteAdelicScalarExtensionLevel D V ψ`, the compact-open
transporter category of `ScalarExtensionSimilitudePoints D V (FiniteAdeles ℚ) ψ`
with its existing operator topology.

At a level `K`, the tower object is the set of `K`-orbits of actual
`D ⊗[ℚ] FiniteAdeles ℚ`-linear frames from `FiniteAdeles ℚ ⊗[ℚ] V` to the
actual rationalized torsion inverse limit. Compatibility means that some linear
trivialization of the actual Tate twist takes `ψ.baseChange` to the actual
Poincaré Weil pairing pulled back by `λ` in the second variable. Such a
trivialization is existential, rather than retained in a frame. The orbit must
be fixed by the actual automorphism group of the finite-étale fibre functor.
Its representative need not be fixed. The geometric transport theorem
`rationalWeilGeometricTransport` is installed using its published proof.

`LevelData K` is the dependent pair of `X : PolarizedAction` and an element of
this actual tower at `K`. `PairAdditivity` explicitly requires additivity of
the constructed dual map for every ordered pair of these objects. It is a
proposition about the existing geometric construction. It supplies the
rational dual map on every actual Hom group used in the relation.

For an actual action-category isomorphism `e : X.actionObj ≅ Y.actionObj` and
`q : ℚˣ`, `Multiple X Y q e` is the equation

`eᵛ ∘ λ_Y ∘ e = (q : ℚ) • λ_X`.

Here `e` has an actual rational inverse, both actions are intertwined, and the
dual and both compositions are those of the constructed rational Hom API.
The relation supplies this geometric equation, rather than a replacement
pairing-preservation assumption. `multiple_refl`, `multiple_trans` and
`multiple_symm` follow from the imported actual rational dual-pullback identity,
composition and inverse laws; multipliers compose as `q * r` and invert as
`q⁻¹`. The multiplier is a rational unit. No additional positivity assertion
about its sign is proved here.

`levelIso X Y K q e he` is the existing actual isogeny equivalence of the two
fixed-orbit level sets. It postcomposes compatible frames with the map of actual
rational Tate modules induced by `e`. The proofs
`rationalWeilFunctoriality` and `rationalWeilGeometricTransport` are installed
from their published proof modules. The imported geometric multiplier theorem
derives preservation of compatibility from `he` and those proofs.
`levelIso_refl`, `levelIso_trans` and `levelIso_symm` specialize the existing
identity, composition and inverse coherence laws. `levelIso_map` specializes
the proved commutation of actual isogeny transport with right translation.

`isogenySetoid K` relates `x` and `y` exactly when there exist `q`, `e` and
`he` as above such that `levelIso` takes `x`'s fixed orbit to `y`'s fixed
orbit. Its reflexivity, symmetry and transitivity are proved using those
multiplier and transport laws. `IsoClass K` is its quotient, `classOf` is the
actual quotient constructor, and `classOf_eq_iff` characterizes equality by
exactly this relation. `classOf_surjective` proves that every class has an
actual representative. It asserts no nonemptiness without a given class.
`forgetAction` descends to the existing rational algebra-action quotient,
using the same actual equivariant rational isomorphism as witness;
`forgetAction_classOf` computes this map on representatives.

For a transporter arrow `f : K → L`, `mapData f` retains the actual polarized
object and applies its actual level-tower map to its fixed orbit. If `g` is
the arrow's element, its transporter condition is `g⁻¹ K g ≤ L`, and on
frames this map sends `η` to `η ∘ g`. `mapData_related` proves preservation
of the polarized-isogeny relation by `levelIso_map`. Hence `Quotient.map`
defines `classMap f`. Its representative formula is definitional; quotient
induction and the original level-tower laws prove identity and composition.
These maps constitute `isoClassTower`. The forgotten rational action class
is invariant under every arrow. `forgetActionNatTrans` packages that law as a
natural transformation to the constant action-class type, with `ULift.{w}`
only to match the universe of the level-class tower.

`forgetLevel` is the class map for an inclusion `K ≤ L`; its representative
formula identifies it with the existing actual Weil-level forgetting map.
For the Hecke span additionally assume `Module.Finite ℚ V`, which supplies
the topological-group instance needed for the compact-open intersection
`H = K ∩ g L g⁻¹`. `heckeLeft` and `heckeRight` are the tower maps on the
existing transporter arrows from `H` to `K` and `L`. Their class formulas
are definitional. The two `_representative` theorems identify them with the
existing actual compatible-level forgetting and right-translation maps.
Thus both legs are well-defined on actual polarized-isogeny classes.

This is fixed-base, pointed, full-adelic quotient infrastructure. No prescribed
relative dimension, Harris Lie compatibility or determinant condition is
imposed here. The general rational module and similitude group have not yet
been identified in this module with the exact Harris arithmetic datum and
its source group. There is no assertion of nonemptiness, level smallness,
canonical independence of the base point, base-scheme pullback, a sheaf
condition or representability. The locally noetherian and connected source
restrictions and extension over disconnected schemes are not imposed.
The full Harris PEL functor, its precise representability theorem, actual
scheme levels and coefficient descent remain further construction obligations.
The provenance of this unit is the explicit assembly and quotient descent of
the existing geometric APIs using the source's polarized rational-isogeny
relation and right level action.
