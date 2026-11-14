# Varying-base functors of unframed special-atlas classes

This internal construction packages the existing actual special-atlas comparison
quotients and supplied-target coefficient extensions into covariant functors.
It uses `SpecialAtlasClassBaseChangeAlong` and
`SpecialAtlasClassBaseChangeAlongComposition`. The quotient relation and the
actual formal comparisons establishing those laws are unchanged.

## Parameters and values

Let `K` be a nonarchimedean local field and `D` a finite-dimensional central
division algebra over `K`. An independently supplied field `L` with a
`K`-algebra embedding `ι : L →ₐ[K] D` is fixed. As in `SpecialAtlas`, every
representative contains the full-degree unramified integer-subfield
certificate and the required geometric tangent-character certificates.
The dimension is `CentralSimple.reducedDegree K D`; no existence of such
representatives or specialization to invariant `1/d` is asserted.

`SpecialAtlas.classFunctor ι` has source `CommAlgCat.{v} 𝒪[K]`. At a
coefficient algebra `R`, with its supplied `𝒪[K]`-algebra structure, its value
is `SpecialAtlas.IsoClass` over `R`. Its values lie in
`Type (max u (v + 1))`: base algebras share universe `v`, the local field and
division algebra share universe `u`, and covers may be infinite. The
independent field universe `s` appears in certificate propositions.

An arrow `f : R ⟶ S` acts by `q.baseChangeAlong f.hom`. This is the
previously constructed map that extends actual charts and the full
division-order action, transports to the supplied target scalar structure,
and descends through the relation of actual formal isomorphisms after
principal refinement. It does not choose a quotient representative.

The functor identity law applies `IsoClass.baseChangeAlong_id` pointwise.
The composition law applies the symmetry of
`IsoClass.baseChangeAlong_comp`, since categorical composition acts by
successive extension while the left side of `map_comp` uses the composite
algebra map. These laws ultimately use the actual identity and composition
formal comparisons in the imported modules.

## Height certificates and Nilp

`HeightSquaredAtlas.classFunctor ι π` uses the existing height-certified
subtype quotient. Each representative has an irreducible `π`, nilpotence of
its actual image in the base, and actual scalar-kernel height `d²` on every
chart, with residue-field cardinality `Nat.card 𝓀[K]`. Each map extends that
representative's own certificate. The functor laws use the corresponding
identity and composition laws inside this subtype quotient.

Both namespaces provide `nilpClassFunctor`, defined by precomposition with
`Nilp.forget 𝒪[K] π`. Its source is the actual full subcategory of
coefficient algebras on which the image of `π` is nilpotent. The height
functor is also defined on all coefficient algebras: it is empty when the
image of `π` is nonnilpotent. `classFunctor_base_nilpotent` reads the
nilpotence certificate from a class, and `classFunctor_isEmpty` derives
this emptiness by contradiction. No class-existence claim is made on
nilpotent bases.

## Natural injection and scope

`HeightSquaredAtlas.forgetHeightNatTrans ι π` has components equal to the
existing `IsoClass.forgetHeight`. Its naturality square is exactly
`forgetHeight_baseChangeAlong`. Each component is injective by
`forgetHeight_injective`: the certified subtype uses the restriction of
the same actual comparison relation. This does not transport height to
an arbitrary uncertified representative.

`nilpForgetHeightNatTrans` is the restriction of that natural
transformation along the Nilp inclusion, and
`nilpForgetHeightNatTrans_injective` retains componentwise injectivity.

These are varying-base functors of unframed special and height-certified
atlas classes. Framing triples, a chosen framing object, polarizations,
quasi-isogenies, group actions, levels, and representability require
further constructions. In particular this module does not identify these
unframed functors with Drinfeld's framed functor. The unit is derived
entirely from the named Library constructions and the supplied-map
prerequisites; it invokes no additional original-source assertion.
