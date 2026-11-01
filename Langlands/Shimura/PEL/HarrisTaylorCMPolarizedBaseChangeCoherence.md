# Coherence of normalized CM polarized Harris pullback

This derived module proves identity and composition for the actual
normalized CM polarized class and tower pullbacks constructed in
[HarrisTaylorCMPolarizedBaseChange](HarrisTaylorCMPolarizedBaseChange.md).
It constructs equality transports on their existing endpoints and uses
the actual ambient polarized coherence laws to prove the equations.

Fix a central simple unitary datum `D` on `A` over the totally real number
field `E` and CM quadratic extension `F/E`, with the displayed rational
and field scalar towers. The CM field `L` is imaginary quadratic over
`ℚ`, with an `L`-algebra structure on `F` and an embedding
`τ₀ : L →+* ℂ`. The signature charts `C` are those for
`harrisCMSection E (algebraMap L F) τ₀`; its proved CM-section property
is used throughout. All arithmetic types and schemes have universe zero.

Each base has a single structural map `p : S ⟶ Spec F`. The determinant
coefficients use its actual induced reflex structure
`D.harrisTaylorReflexStructure C p`, constructed with the explicitly
conjugated `harrisTaylorReflexToCM`. No independent reflex-field map is
supplied. The endpoints are the existing
`HarrisNumericalWeilLevel.IsoClass` at these parameters. Their image
predicate requires one actual polarized representative with the
normalized determinant, actual relative dimension `[E : ℚ] * n²` and
the full all-chart central trace condition. The imported normalized
comparison identifies this with normalized determinant and dimension
on that same representative. Relative dimension means
`SmoothOfRelativeDimension` for its actual structural morphism.
Its polarization, dual geometry and compatible level orbit retain
the existing definitions.

The named tensor comparison, composition, unit, associativity,
left-unitor and symmetry propositions; Picard-zero pullback,
Mumford-bundle and universal-base-change propositions; dual abelian
naturality and polarization pullback propositions remain explicit.
Identity retains `LieBaseChangeNaturalityStatement S`; composition
retains it on `S` and the intermediate base `T`. The finite Weil
transition and torsion finite-etale propositions, rational
profinite-integer/finite-adele comparison, invertibility of every
positive indexed torsion order, finite etale roots of unity and
ordered-pair dual additivity remain inputs on their applicable bases.
The schemes are quasi-separated. Points have source `Spec Ω` for a
field `Ω`, with the displayed finite-fibre witnesses on finite-etale
covers. No flatness or reducedness assumption is added.

The dual families are the existing constrained
`PositivePullbackDualData` on each object's actual abelian-scheme
pullback. They supply dual construction and evaluation data rather
than an arbitrary target class or a coherence equation. Composition
quantifies these families for `b`, `c` and `c ≫ b` independently.

`classPresentationEq` transports equal CM structural maps `p = q`
and equal points `s = r` on one base. Eliminating the equalities
makes the map the identity on the existing subtype; proof
irrelevance handles the finite-fibre witnesses.
`classPresentationEq_val_val` identifies its underlying ambient
polarized class with `ambientClassPointEq`. The induced reflex
maps change together with `p`; no separate comparison premise
is needed. `classTowerPresentationEq` is the corresponding
transport between the existing normalized numerical towers.
After equality elimination it is the identity natural
transformation, with component formula
`classTowerPresentationEq_app`.

Identity pullback has source structural map `p` and point
`t ≫ 𝟙 S`, and target structural map `𝟙 S ≫ p` and point `t`.
`classBaseChange_id` identifies this actual map with transport
along `(Category.id_comp p).symm` and `Category.comp_id t`.
Function extensionality and two applications of subtype
extensionality remove the numerical and determinant proof fields.
The existing underlying-value formulas and the new transport
formula reduce the equation to `ambientClassBaseChange_id` at
the underlying polarized quotient class. Extensionality at each
original level and class proves `classTowerBaseChange_id`.

For `b : T ⟶ S`, `c : R ⟶ T` and `t : Spec Ω ⟶ R`,
successive pullback starts at point `(t ≫ c) ≫ b` and ends
over structural map `c ≫ (b ≫ p)`. Direct pullback starts at
`t ≫ (c ≫ b)` and ends over `(c ≫ b) ≫ p`. The induced
reflex structure at each endpoint is the one determined by
that displayed CM structural map. Finite-fibre witnesses
remain explicit for all four point presentations, including
`t` and `t ≫ c`.

`classBaseChange_comp` proves
`F_c ∘ F_b = moveTarget ∘ F_direct ∘ moveSource` at each level.
The source transport uses the reflexive CM structural equality
and `Category.assoc t c b`; the target uses
`Category.assoc c b p` and the reflexive point equality.
Function extensionality, double subtype extensionality and
the actual underlying-value formulas reduce this to
`ambientClassBaseChange_comp`. Evaluation at each original
level and class proves `classTowerBaseChange_comp`, in the
categorical order
`F_b ≫ F_c = moveSourceTower ≫ F_direct ≫ moveTargetTower`.
These are equalities of the existing natural transformations
on the original Harris transporter category, including its
subgroup-forgetting and Hecke transporter arrows.

The provenance is internal: equality elimination constructs
the transports, and the existing ambient coherence laws give
the equations through the injective subtype inclusions.
The imported pullback preserves the conditions on the same
actual pulled representative. No dimension invariance under
arbitrary rational isomorphisms is used. Original-source
conventions and citations remain those of the imported
[normalized CM specialization](HarrisTaylorCMPolarizedClasses.md);
this module makes no new original-literature claim.

The result supplies pointed normalized CM coherence under
the displayed construction premises. Point independence,
an unpointed PEL moduli presheaf, representability, canonical
models, representing scheme levels and coefficient descent
remain further constructions in the host task.
