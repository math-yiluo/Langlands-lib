# Constant equivariant sheaves on the twisted site and injectivity of global sections

Author: Worker 26. The twisted-site analogue of Worker 134's published
`Langlands.Cohomology.EquivariantComposite.ConstantAdjunction`, which does the same for
equivariant sheaves on a topological space (transport category of opens). It uses:

- `Langlands.Sheaf.Equivariant.TwistedOver` (Worker 26): the twisted category, its morphisms
  with a `twist` and an arrow `left` (`homMk`, `hom_ext`, `comp_twist`), the base object
  `base P ρ` with `hom_base`, its endomorphisms `baseEndo g` (twist `g`, arrow `ρ g`), the
  action `baseAction P ρ` (`g` acts through `baseEndo g⁻¹`), `twistedTopology`, and
  `IsLiftSystem` (every admissible action of `h` has twist `h⁻¹`);
- `Langlands.Sheaf.Equivariant.LocalActionCohomology` (Worker 13): `sectionsRep R a`, the
  sections over an object as a representation (`actionRepresentation_apply`);
- `Langlands.Sheaf.Equivariant.TwistedGlobalSections` and
  `Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison` (Worker 26):
  `sheafGlobalSectionsRep` (`sheafToPresheaf` followed by `sectionsRep R (baseAction P ρ)`),
  `sheafGlobalSectionsSmooth` (its smooth part), `discreteGlobalSections` and
  `exactGlobalSections`, Berkovich's `Γ_{X{G}}`;
- `Langlands.Sheaf.Equivariant.LocalAction`, `LocalActionDiscretePart`,
  `LocalActionSmoothPart` (Workers 13 and 26): `IsDiscrete`, `IsLocallyDiscrete`,
  `discreteSheafProperty`, `smoothSheafProperty`, `DiscreteSheaf`, `SmoothSheaf` and their
  inclusions, `IsDiscrete.isLocallyDiscrete`, `HasAdmissibleRefinements.covers`;
- `Langlands.Sheaf.Equivariant.LocalActionConstant` (`isDiscrete_sheafify`) and
  `Langlands.Sheaf.Equivariant.LocalActionSmoothConstant` (`isLocallyDiscrete_sheafify`)
  (Worker 26): sheafification preserves discreteness, resp. local discreteness;
- `Langlands.Representation.Category.SmoothPartAdjunction`: `SmoothRep.toRep ⊣
  smoothPartFunctor` (`toRepSmoothPartAdjunction`); `SmoothRep.toRep` preserves
  monomorphisms (`Langlands.Representation.Category.Abelian`);
- Mathlib: `sheafificationAdjunction`, `Adjunction.comp`, `Adjunction.mkOfHomEquiv`,
  `Adjunction.restrictFullyFaithful`, `Functor.mono_of_mono_map`, and
  `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` (a right adjoint
  whose left adjoint preserves monomorphisms preserves injective objects).

All declarations are in the namespace `Langlands.Sheaf.Equivariant.TwistedOver`.

## Purpose

Berkovich's spectral sequence `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)` of
§1.2 is the composite-functor spectral sequence of `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`. Its
standard input is that `Γ_{X{G}}` sends injective objects to objects acyclic for the
`G`-invariants. This module proves the stronger statement that `Γ_{X{G}}` sends injective
objects to injective smooth representations, for all module sheaves on the twisted site, for
discrete sheaves and for locally discrete sheaves, by constructing an exact left adjoint: the
constant equivariant sheaf of a representation.

## Data and universes

- A category `C : Type u` with `Category.{v} C`, a morphism property `P`, an object `X`, a
  group `G : Type uG` and `ρ : G →* Aut X`. The twisted category has morphisms in
  `Type (max v uG)`. `[P.ContainsIdentities]` is assumed where the base object is used, and
  `[P.RespectsIso]` where the twisted topology is used.
- A commutative ring `R : Type w`. Representations are `Rep.{w} R G`, smooth representations
  `SmoothRep.{w, uG, w} R G`, and presheaves take values in `ModuleCat.{w} R`.
- For sheaves: a topology `J` on `P.Over ⊤ X` with `[IsTranslationInvariant J]` and
  `[HasSheafify (twistedTopology ρ J) (ModuleCat R)]`. For smooth representations,
  `[TopologicalSpace G] [IsTopologicalGroup G]`.
- For discrete (resp. locally discrete) sheaves: a local action system `L` on the twisted
  category with `[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]` (resp.
  `[L.HasAdmissibleRefinements (twistedTopology ρ J)]`), as in `LocalActionDiscretePart`
  (resp. `LocalActionSmoothPart`), and a proof `hL : L.IsLiftSystem`.

## The structure maps

- `toBase U : U ⟶ base P ρ`: the twisted morphism with twist `1` and arrow the structure
  map `U.hom` (`toBase_twist`, `toBase_left`). `toBase_base`: for the base object it is the
  identity.
- `comp_toBase f`: for a twisted morphism `f : V ⟶ U` with twist `g`,
  `f ≫ toBase U = toBase V ≫ baseEndo g`. Both have twist `g`, and their arrows agree by the
  covering condition of `f`.

## The constant twisted presheaf

- `constantTwisted P ρ R : Rep R G ⥤ (TwistedOver P ρ)ᵒᵖ ⥤ ModuleCat R`: the presheaf that is
  the module `M` on every object, with a twisted morphism `f` acting by `M.ρ (twist f)⁻¹`
  (`constantTwisted_obj_map_apply`). Functoriality holds because twists multiply contravariantly
  under composition. A map of representations acts by its underlying linear map.
- With this convention, an admissible action of `h` that is a lift (twist `h⁻¹`) acts on
  sections by `M.ρ h`, and `g` acts on the sections over the base object, through
  `baseEndo g⁻¹`, by `M.ρ g`.
- `constantTwistedLift M F a`: for a map `a : M ⟶ (sectionsRep R (baseAction P ρ)).obj F`,
  the presheaf map with component `a` followed by `F.map (toBase U).op` at `U`. Naturality
  follows from `comp_toBase` and the equivariance of `a`.
- `constantTwistedHomEquiv M F`: presheaf maps from the constant presheaf to `F` correspond to
  equivariant maps from `M` to the sections of `F` over the base object. A presheaf map goes
  to its component at the base, which is equivariant by naturality at `baseEndo g⁻¹`; the
  inverse is `constantTwistedLift`. Naturality at `toBase U` gives one inverse law,
  `toBase_base` the other.
- `constantTwistedAdjunction R : constantTwisted P ρ R ⊣ sectionsRep R (baseAction P ρ)`.
- `constantTwisted_preservesMonomorphisms` (instance): componentwise, a monomorphism of
  representations is a monomorphism of modules.

## Constant sheaves and injectivity for all module sheaves

- `constantTwistedSheaf J R`: the constant twisted presheaf followed by sheafification on the
  twisted site.
- `constantTwistedSheafAdjunction J R : constantTwistedSheaf J R ⊣ sheafGlobalSectionsRep J R`:
  the composite with the sheafification adjunction.
- `constantTwistedSheaf_preservesMonomorphisms` (instance), and the instance
  `sheafGlobalSectionsRep_preservesInjectiveObjects`: global sections send injective module
  sheaves on the twisted site to injective representations.
- `smoothConstantTwistedSheaf J R`: `SmoothRep.toRep` followed by `constantTwistedSheaf`.
  `smoothConstantTwistedSheafAdjunction J R`: it is left adjoint to
  `sheafGlobalSectionsSmooth J R`, the composite with `toRepSmoothPartAdjunction`.
  `smoothConstantTwistedSheaf_preservesMonomorphisms` (instance) and
  `sheafGlobalSectionsSmooth_preservesInjectiveObjects` (instance).

## Discrete and locally discrete sheaves

- `isDiscrete_constantTwisted R L hL M`: for a lift system `L` and a smooth representation
  `M`, the constant twisted presheaf of `M` is discrete. An admissible action `a` of `H` on
  `U` acts on `m ∈ M` by `M.ρ h`; if the open subgroup `K` fixes `m`, then `H ⊓ K` is an open
  subgroup of `H` fixing `m`.
- `discreteSheafProperty_smoothConstantTwistedSheaf`: the constant sheaf is then a discrete
  sheaf (`isDiscrete_sheafify`). `discreteConstantTwisted J R L hL : SmoothRep R G ⥤
  L.DiscreteSheaf (ModuleCat R) (twistedTopology ρ J)` is the lift of
  `smoothConstantTwistedSheaf`; `discreteConstantTwisted_comp_inclusion` (`rfl`).
- `discreteConstantTwistedAdjunction J R L hL`: it is left adjoint to
  `discreteGlobalSections J R L`, by `Adjunction.restrictFullyFaithful` along the identity and
  the fully faithful inclusion of discrete sheaves.
- `discreteConstantTwisted_preservesMonomorphisms`: the inclusion is faithful, so it reflects
  monomorphisms. `discreteGlobalSections_preservesInjectiveObjects J R L hL`: `Γ_{X{G}}` sends
  injective discrete sheaves to injective smooth representations.
- Locally discrete sheaves: `smoothSheafProperty_smoothConstantTwistedSheaf` (a discrete
  presheaf is locally discrete when admissible objects cover, and sheafification keeps local
  discreteness), `smoothSheafConstantTwisted J R L hL` (the lift),
  `smoothSheafConstantTwisted_comp_inclusion` (`rfl`),
  `smoothSheafConstantTwistedAdjunction J R L hL` (left adjoint to
  `exactGlobalSections J R (L.smoothSheafInclusion _ _)`),
  `smoothSheafConstantTwisted_preservesMonomorphisms` and
  `exactGlobalSections_smoothSheafInclusion_preservesInjectiveObjects J R L hL`. In the proof
  of `smoothSheafProperty_smoothConstantTwistedSheaf` the universes of
  `isLocallyDiscrete_sheafify` are given explicitly; elaboration otherwise fails on a universe
  constraint.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`).

- §1.2, printed pp.4–5 = PDF pp.4–5: "The high direct images of the functor `Γ_{X{G}}` on the
  category of abelian sheaves will be denoted by `H^q(X{G}, F)`. For any abelian sheaf `F`
  there is a spectral sequence `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)`." The
  full passage is quoted in the Markdown of `AnalyticEtaleCohomology`.

## Provenance and correspondence

Derived. Berkovich states the spectral sequence without proof in this passage. The
construction here is ours: it transfers to the twisted site the argument of Worker 134's
published `ConstantAdjunction` for equivariant sheaves on a topological space (constant
presheaf with inverse-label action, maps out of it as equivariant global maps, sheafification,
and preservation of injectives by a right adjoint whose left adjoint preserves monomorphisms).
The convention that a twisted morphism with twist `g` acts by `g⁻¹` matches `baseAction`
(`g` acts through `baseEndo g⁻¹`) and `IsLift` (an admissible action of `h` has twist `h⁻¹`),
so that the constant sheaf of `M` carries the action of `M` on its global sections and over
admissible objects. That `Γ_{X{G}}` preserves injective objects is the hypothesis of the
composite-functor spectral sequence for `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}`.

## Not formalized here

The spectral sequence of §1.2 itself; an identification of the global sections of the
constant sheaf with `M`; constant sheaves for representations that are not smooth, as objects
of discrete or locally discrete sheaves; and exactness of the constant sheaf functors beyond
preservation of monomorphisms.
