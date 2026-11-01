# Mixed point and base change for normalized CM polarized Harris towers

Author: Worker 57.

This derived construction proves that actual normalized CM polarized pullback
commutes with point transport. It constructs the path-independent diagonal
map of the existing numerical Harris class towers and its canonical geometric
version. The namespace is
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Retained objects and hypotheses

The arithmetic types and schemes have universe zero. The arithmetic inputs
are the totally real number field `E`, its quadratic CM extension `F`, the
central simple unitary datum `D` with algebra `A`, an imaginary quadratic CM
field `L` mapping into `F`, the displayed embedding `τ₀ : L →+* ℂ`, and
charts `C` on exactly `harrisCMSection E (algebraMap L F) τ₀`.
For an arbitrary actual map `b : T ⟶ S` and `p : S ⟶ Spec F`, the two reflex
structures are the existing `D.harrisTaylorReflexStructure C p` and
`D.harrisTaylorReflexStructure C (b ≫ p)`. They retain the existing conjugated
normalization, positive auxiliary left involution and actual regular source
form.

The towers are exactly `HarrisNumericalWeilLevel.isoClassTower` at these
structures. They use the original `HarrisLevel D` transporter category and
`hodgeLevelFunctor D C`. Their two subtype layers retain the determinant image
inside the actual polarized quotient and the image of one representative
satisfying both the positive determinant and numerical object conditions.
The imported normalized comparison identifies that image with one normalized
determinant-compatible representative of geometric relative dimension
`[E : ℚ] * n²`. No dimension invariance under arbitrary rational isomorphism
is asserted. All actual objects and quotient relations are unchanged.

The tensor comparison, composition, unit coherence, associativity, unitor
comparison and symmetry statements, Picard-zero stability, Mumford membership
and universal base-change statements, dual base-change naturality and
polarization stability remain explicit inputs. So do finite Weil transition
compatibility, rational profinite-integer/finite-adele comparison, torsion
finite-etaleness, invertibility of every positive full-tower order on both
bases, finite-etaleness of their roots-of-unity schemes, quasi-separatedness
of both bases, and positive ordered-pair additivity on both bases. The source
`LieBaseChangeNaturalityStatement S` is also explicit: it concerns the actual
Lie base-change maps, not the mixed square to be proved.

The family `dualData` is exactly `PositivePullbackDualData` indexed by each
actual source positive polarized action. It supplies constrained dual and
evaluation data on that object's actual abelian-scheme pullback along `b`.
The same family is used in both routes of the mixed square. No compatibility
with a separately chosen target polarized object or class is assumed.

The supplied-path portion has field-valued points `s : Spec Ω ⟶ T` and
`t : Spec Ω' ⟶ T`, finite fibres of every finite-etale cover at both points
and at `s ≫ b`, `t ≫ b`, and an actual isomorphism
`epath : fiberFunctor s hs ≅ fiberFunctor t ht`. It requires no algebraic
closedness, connectedness or local Noetherianness. In particular `b` has no
flatness, reducedness or smoothness restriction; nilpotent bases remain
within the theorem's stated assumptions.

## Mixed square and diagonal

`classBaseChange_pointMap` proves equality of two actual maps on a normalized
class. One route transports along the existing `pathPushforward b` and then
pulls back at `t`; the other pulls back at `s` and then transports on `T`.
Applying subtype extensionality twice reduces this to the already proved
`HarrisTaylorLieWeilLevel.ambientClassBaseChange_pointMap` on the actual
polarized quotient. The normalized class pullback and point comparison have
exactly those underlying ambient values. The proof arguments for duality and
polarization propositions are identified by proof irrelevance. The ambient
square itself was proved on actual representatives using the actual Weil
level transport/base-change square and then descended to the quotient; its
conclusion is reused here, not assumed as an additional input.

`classTowerBaseChange_pointTransport` packages this equality as a commuting
square of natural transformations over the entire original Harris level
category. `classTowerBaseChangeAlongPath` defines its diagonal: actual
normalized pullback at `s`, followed by actual target point comparison to `t`.
The component formula is reflexivity, the alternative pushed-path route
follows from the mixed square, and independence from the auxiliary path
follows from the normalized point-comparison independence theorem.

`classTowerBaseChangeAlongPath_forgetCMAction` proves that forgetting the
polarization and level gives the existing actual joint CM action-class
pullback. It combines point comparison's forgetful equality with the existing
normalized pullback forgetful square. Its action-class map uses actual
rational-action pullback and the same source Lie-naturality input.
`classTowerBaseChangeAlongPath_arrow` exposes naturality for every original
Harris transporter, including subgroup forgetting and both existing Hecke
legs.

## Canonical geometric version and scope

For connected locally Noetherian `T` and algebraically closed endpoint fields,
`classTowerGeometricBaseChange` chooses a path using proved
`geometricPathExists`. Its equality with the diagonal from every supplied
path is proved. It is definitionally pointed pullback followed by canonical
target comparison; its joint CM action forgetful square and naturality for all
original Harris transporters are proved. No connectedness or local
Noetherianness of `S` is needed for those assertions. If `S` is additionally
connected and locally Noetherian, the final theorem identifies this map with
canonical comparison on `S` followed by pointed pullback at `t`. The proof
uses the pushed path and the comparison's equality with every supplied path.

The provenance is internal: reuse the constructed actual ambient mixed square,
restrict through the existing two subtype layers, compose the constructed
normalized tower maps, and use proved path independence and geometric path
existence. The original context retained in the imported paired modules is
Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.89–91 / PDF pp.97–99, especially p.91,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
This module makes no new comparison between geometric isogenies and all
invertible rational morphisms.

The result compares pointed presentations over a fixed actual base arrow. It
does not yet construct an unpointed varying-base moduli functor, prove its
identity or composition laws for arbitrarily selected geometric points, or
assert universal availability of the named geometric inputs. Representability,
scheme levels, canonical models and coefficient descent remain obligations
of the larger geometry task.
