# Geometric-point lifts and original represented CM transition surjectivity

This module constructs actual geometric-field lifts through every original
represented normalized Harris CM transporter and proves surjectivity on
scheme points. It uses the existing exact representing equivalences, together
with the explicitly named relative dual existence and geometry propositions.
It derives the lifting and surjectivity conclusions; neither is a premise.
The existing CM classes, test category, level category and scheme maps are
unchanged.

The entry definition is
`HarrisTaylorCMWeilLevel.representedCMGeometricPointLift`. Fix an exact family
`R` of `CMLevelRepresentation` witnesses and an original small-level arrow
`k : U ⟶ V`. For an algebraically closed field Ω and an actual map
`a : Spec Ω ⟶ (representedCMSchemeTower R).obj V`, it constructs an actual
map to the level U scheme. Its companion
`representedCMGeometricPointLift_comp` proves that composing this lift with
the original transition gives a. The reassociation companion is also
generated. The choice need not be natural and does not define a scheme
section over the entire target.

`representedCMSchemeTower_map_surjective` proves surjectivity of that
original transition on underlying scheme points.
`cmSchemeTower_map_surjective` specializes this result to exactly the chosen
representations defining the existing `cmSchemeTower`, from a proof of the
existing `CMRepresentabilityStatement`.

## Original source and the derived result

The source is Harris–Taylor, *The Geometry and Cohomology of Some Simple
Shimura Varieties* (2001), III.1, printed pp.90–91, one-based PDF pp.98–99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Page 90 specifies the connected-component product and the level smallness
condition. Page 91 defines the polarized moduli classes with algebra action
and monodromy-invariant, pairing-compatible adelic frame orbits. It states
independence of the geometric point, smooth projective representability,
finite étale level forgetting and the normal-level Galois-cover assertion.
It defines right translation by composition on the frame. The supplied
five-page author publication and errata list was read; it has no correction
to this passage. This observation concerns that supplied list.

The source's imaginary quadratic field E, CM field F and totally real field
F⁺ are the present L, F and E respectively. The imported determinant test
uses `harrisCMSection E (algebraMap L F) τ₀` and the existing normalized
Harris–Taylor reflex structure. The positive auxiliary involution, numerical
dimension test, polarized-isogeny equivalence and opposite-group
conventions remain the imported ones.

The proof here is derived from the preceding identity-point class lift,
the existing geometric-family evaluation isomorphisms and the exact
representing equivalences. Algebraic closures of residue fields then detect
surjectivity on scheme points. This route is not asserted to be the book's
proof of its stronger geometric theorem. In particular this module proves
neither étaleness nor the normal-level Galois-cover assertion.

## Transfer to the actual field-test presheaf

The private `map_surjective_of_naturalIso` lemma transfers surjectivity of
one functor's map to the other side of a natural isomorphism. Apply the
isomorphism to the target element, take a preimage, and apply the inverse
isomorphism. Naturality and the inverse equation prove the required equality.

For `unpointed_identityPoint_map_surjective`, let `p : Spec Ω ⟶ Spec F`
with Ω algebraically closed, and assume precisely the existing
`AdmissibleCMBase (Over.mk p)`. The actual geometric point used for evaluation
is `⟨Ω, 𝟙 _⟩`. The admissibility evidence supplies finite étale roots of
unity, invertible positive indices and positive-pair additivity; the existing
point supplies finite fibers. The preceding
`identityPoint_classMap_surjective` applies to the original pointed
class transition. The existing natural isomorphism
`unpointedClassTowerEvaluationIso` transfers it to the unpointed tower map
at the same actual base. Its compatible geometric families and all their
pullback conditions are those already defined in the imported presheaf.

`disconnected_identityPoint_map_surjective` also assumes the existing
componentwise admissibility evidence for that same base. A field spectrum
is connected and nonempty. Choose its component using any actual point.
The existing `disconnectedClassTowerConnectedIso`, with its duality and
polarization naturality prerequisites, identifies the disconnected tower
with the unpointed tower. The same natural-isomorphism lemma transfers
surjectivity to the original disconnected map. No product evaluation or
transition is replaced.

`cmGeometricTestBase` discharges membership in the restricted test category.
It accepts any field Ω, the actual structural map p, and the two named
propositions `RelativeDualSchemeExistenceStatement` and
`RelativeDualSchemeGeometryStatement`. Field spectra are locally Noetherian.
The existing `componentwiseAdmissibleCMBase_of_relativeDual` then bundles
`Over.mk p` into the actual componentwise admissible category.

For algebraically closed Ω, `cmGeometricTestBase_map_surjective` additionally
uses connectedness of `Spec Ω` and
`admissibleCMBase_iff_dualGeometry` to obtain connected admissibility.
The named existence assertion supplies an actual dual for each abelian
scheme, and the named geometry assertion supplies the required geometry
of that same dual. The two preceding transfer theorems therefore apply.
The dual assertions are substantive hypotheses; this module proves
neither of them.

## Lifting through the exact representing equivalences

The family R consists precisely of the existing `CMLevelRepresentation`
witnesses for `smallLevelClassPresheafTower`. Each includes an object of
the same componentwise admissible category, smoothness, a projective-space
closed immersion and a natural isomorphism from its lifted Yoneda functor
to the specified class presheaf. The tower's morphisms are the existing
Yoneda preimages of the original class maps.

`representedCMGeometricHom_map_surjective` works in this full subcategory
of schemes over `Spec F`. For any actual morphism f from the constructed
field test base to the level V representing object, the representing
isomorphism gives its class q. The proved disconnected-map surjectivity
gives a class at U mapping to q. The inverse representing isomorphism
produces an actual morphism fU to the level U object.
`representedCMBaseTower_map_classes` and the inverse equations identify
the class of `fU ≫ (representedCMBaseTower R).map k` with q.
Injectivity of the representing equivalence and `ULift.up_injective`
give equality with f as actual morphisms. Thus postcomposition by the
original represented transition is surjective on these Hom sets. The
universe lift changes no map or equality.

For the entry definition, put `p = a ≫ (R V).base.obj.hom`. The map a
then gives an actual over-field morphism from `cmGeometricTestBase p` to
the level V object; the commuting equation holds by construction.
`Function.surjInv` chooses a preimage under the proved Hom-set
surjectivity. Forgetting its property and over-category wrappers gives the
desired actual scheme map. Applying `congrArg` to
`Function.surjInv_eq` proves its equation under the original scheme
transition. No lift or section is stored as arbitrary representing data.

## Surjectivity on scheme points

For an arbitrary point y of the level V scheme,
`HarrisGeometricPoint.ofResidue` gives the existing geometric point
obtained from an algebraic closure of its residue field. Its domain is a
nonempty field spectrum. Lift that actual scheme map through k, and
evaluate the lift at any point x of this spectrum. The proved composition
equation sends the resulting point back to the value of the original
geometric map at x. By its construction through the residue field and
`Scheme.fromSpecResidueField_apply`, that value is y.
This proves `representedCMSchemeTower_map_surjective` for every original
small-level transporter, including translating arrows.

The final theorem substitutes `chosenCMLevelRepresentation q`, precisely
the family already used to define `cmSchemeTower q`. It makes no new
choice of a scheme model or of the tower's transitions. The geometric
point argument requires no finite-type, étaleness or properness premise
on the transition.

## Retained hypotheses and remaining scope

The arithmetic and signature inputs are the actual totally real and CM
number fields, quadratic extension, central simple unitary datum,
imaginary quadratic subfield, complex embedding and Harris charts.
The inherited tensor preservation, composition, unit, associativity,
comparison and symmetry propositions remain explicit. So do Picard-zero
pullback, Mumford square, universal base change, duality naturality,
polarization stability, finite Weil transitions, the rational/profinite/
adelic comparison and torsion finite étaleness. The test-base construction
additionally retains exactly the two named relative dual propositions
described above.

The pointed class lift retains the same actual polarized representative
with its joint determinant and numerical witnesses. This argument never
assumes that dimension is invariant under all rational isogenies. The
geometric-family and component comparisons, the original transporter
maps and all their action conventions are reused unchanged.

Exact representability is still a hypothesis. Its restricted category is
explicit; comparison with the source functor on all locally Noetherian
F-schemes remains a further obligation. The source's global arithmetic
and division-algebra conditions must be established for any applicable
existence theorem; no universal projectivity or existence assertion for
arbitrary central simple data follows here. Étaleness of the original
transitions and invertibility of the exact residual coproduct-to-kernel-pair
comparison remain further geometric obligations. The results supply
surjectivity for those original transitions when the stated inputs hold;
they do not construct canonical-model comparisons, uniformization,
coefficient descent or local systems.
