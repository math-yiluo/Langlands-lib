# Lifting two-axis classes along square-zero extensions and Čech obstruction cocycles

Module `Langlands.AlgebraicGeometry.Picard.TwoAxisClassObstruction`, namespace
`Langlands.AlgebraicGeometry.Picard.TwoAxisRigidifiedLineBundle`. This is a supporting module of
the proof of Murre's condition (F8) for the two-axis class presheaf. Its content is internal: it
translates the published Čech obstruction theory of the openness-of-versality development
(modules `OpennessOfVersality.Sufficiency` and `OpennessOfVersality.NecessityGluing`) from line
bundles on a relative space into statements about classes of two-axis rigidified line bundles.

## Setting

`A` is an abelian scheme over a scheme `S`, `Λ` is a commutative ring and `f : Spec Λ → S`. The
self-product of the abelian scheme `abelian A (Over.mk f)` over `Spec Λ` has the structure
morphism `productStructure A f`, published in `TwoAxisClassArtinianLiftingProof`, together with
the natural isomorphisms `affineComparison A f B` from the self-product over a `Λ`-algebra `B` to
the relative space `relSpace (productStructure A f) B`.

## Basic constructions

- The instance `IsProper (productStructure A f)`: the structure morphism is the first projection
  of the self-product followed by the structure morphism of the abelian scheme. Both are proper.
- `carrierBundle A L`: the carrier line bundle of a rigidified line bundle `L`.
- `toRel A f B L`: a line bundle `L` on the self-product over `B`, pulled back along
  `inv (affineComparison A f B)` to the relative space over `B`.
- `toRelPullbackIso A f φ L`, for a `Λ`-algebra map `φ : B → C`: pulling `toRel A f B L` back
  along `relMap (productStructure A f) φ` is isomorphic to `toRel A f C` of the pullback of `L`
  along `productMap A (algHomOver f φ)`. The proof composes two published
  `LineBundle.pullbackCompEqIso` with `inv_affineComparison_naturality`.
- `ofRelPullbackIso A f φ N`: the analogous isomorphism for a line bundle `N` on the relative
  space, pulled back along `affineComparison`. It uses `affineComparison_naturality`.
- `ofRelToRelIso A f B L`: pulling `toRel A f B L` back along `affineComparison A f B` recovers
  `L`.
- `nonempty_carrierIso_of_eq`: if the restrictions of the classes of `L` and `L'` along `h` and
  `k` are equal, then the pulled-back carrier bundles are isomorphic. The proof applies
  `Quotient.exact` and then the forgetful functor to carriers.
- `exists_class_of_carrierIso`: let `p : B → C` be a `Λ`-algebra map, `E` a line bundle on the
  self-product over `B` and `D₀` a rigidified bundle over `C`. If the pullback of `E` along
  `productMap A (algHomOver f p)` is isomorphic to the carrier of `D₀`, then some class over `B`
  restricts to the class of `D₀`. The class is that of the published two-axis normalization of
  `E` (`LineBundle.twoAxisNormalizedBundleRigidification`). Its restriction has carrier
  isomorphic to that of `D₀` by `LineBundle.twoAxisNormalizedBundleRestrictionIso`. The published
  `nonempty_iso_of_carrierIso` upgrades this to an isomorphism of rigidified bundles. This is the
  same normalization step as in the final part of the (F4′) proof.
- `toAlgHom_comp_eq`: two `Λ`-algebra maps agree after composing with the structure maps from
  `Λ`. This supplies the compatibility hypothesis `hqρ` of the published obstruction theory,
  with the polynomial ring `P` taken to be `Λ` itself.

## Data of section `Obstruction`

The published obstruction theory is used with base ring `R := Λ`, polynomial ring `P := Λ` and
structure morphism `productStructure A f`. The data are:

- a `Λ`-algebra `A₀` with `algebraMap Λ A₀` surjective (`hπ`);
- an `A₀`-module `Q` with a `Λ`-linear `jQ : Q → Λ` whose image is exactly the kernel of
  `Λ → A₀` (`hjQ`);
- an ordered affine cover `K` of `relSpace (productStructure A f) Λ` and units `g` on its double
  intersections whose multiplicative Čech coboundary minus one (the published `defect`) lies in
  the extension of that kernel (`hg`);
- a rigidified bundle `L'` over `A₀`, and frames `e` of `toRel A f A₀ (carrierBundle A L')` on the
  published test cover over `A₀` (`he`), with transition functions the reductions of `g` (`hge`);
- `Λ`-algebras `Ã` and `B`, a `Λ`-algebra map `χ : A₀ → B` and a surjective `Λ`-algebra map
  `q : Ã → B` (`hq`);
- an `A₀`-module `M` with an injective `Λ`-linear `jM : M → Ã` whose image is the kernel of `q`
  (`hjMinj`, `hjMr`), and with `jM m * jM m' = 0` for all `m, m'` (`hjMsq`).

The published `zObs (productStructure A f) K jQ hjQ g hg ∈ C² ⊗[A₀] Q` is the obstruction cochain.
Here `C^p = cplx (productStructure A f) K A₀ p` is the Čech complex of the structure sheaf
base-changed to `A₀`, with differential `dif`. The published
`phiQ χ q (toAlgHom_comp_eq χ q) hπ jQ _ jM hjMinj hjMr : Q →ₗ[A₀] M` is the obstruction map.
It is characterised by `jM (φ x) = algebraMap Λ Ã (jQ x)` (published `jM_phiQ`).

## `exists_cocycle_of_classLift`

Assume moreover that the kernel of `q` is nilpotent (`hn`). Let `η` be a class over `Ã` whose
restriction along `q` equals the restriction along `χ` of the class of `L'`. Then there is
`c ∈ C¹ ⊗[A₀] M` with

  `(dif 1 ⊗ M)(c) + (C² ⊗ φ)(z) = 0`.

Proof, as implemented. Choose a representative `Lη` of `η`. By `nonempty_carrierIso_of_eq`, the
carriers of the two restrictions are isomorphic. With `toRelPullbackIso` this gives an
isomorphism `φ` between the pullback of `toRel A f A₀ (carrierBundle A L')` along `χ` and the
pullback of `N := toRel A f Ã (carrierBundle A Lη)` along `q`. The published
`exists_frames_lift` lifts the frames `e` to frames of `N` on the test cover over `Ã`. The
published `pullbackCocycle_frameCocycle_eq` compares their transition cocycle with `g`, and
`CocycleGluing.isCocycle_of_isTransition` shows it is a cocycle. Then `exists_cObs` provides the
one-cochain `c`, and `cObs_cocycle` proves the displayed equation.

## `exists_classLift_of_cocycle`

Conversely, if `c ∈ C¹ ⊗[A₀] M` satisfies the displayed equation, then some class over `Ã`
restricts along `q` to the restriction along `χ` of the class of `L'`. This direction does not
need nilpotence of the kernel.

Proof, as implemented. The published `exists_deformation` glues a line bundle `N` on the relative
space over `Ã` and an isomorphism from the pullback along `χ` of
`toRel A f A₀ (carrierBundle A L')` to the pullback of `N` along `q`. Pulled back along
`affineComparison A f Ã`, `N` becomes a line bundle on the self-product over `Ã`.
`ofRelPullbackIso`, the inverse of the glued isomorphism, `toRelPullbackIso` and
`ofRelToRelIso` identify its restriction along `q` with the carrier of
`relativePullback A (algHomOver f χ) L'`. Then `exists_class_of_carrierIso` gives the class.

## Provenance

Published Library inputs: `productStructure`, `affineComparison`, `affineComparison_naturality`,
`inv_affineComparison_naturality`, `productMap`, `first_naturality`, `second_naturality` (module
`TwoAxisClassArtinianLiftingProof`), `LineBundle.twoAxisNormalizedBundleRigidification`,
`LineBundle.twoAxisNormalizedBundleRestrictionIso`, `nonempty_iso_of_carrierIso`, and from the
openness-of-versality development `exists_frames_lift`, `pullbackCocycle_frameCocycle_eq`,
`exists_cObs`, `cObs_cocycle`, `exists_deformation`, `phiQ`, `zObs`, `cplx`, `dif`,
`testCover`, `defect`, `pushUnits`. Read cohomologically, the two theorems say that a lift exists
if and only if the obstruction class `φ_*[z]` vanishes in `H²`. This is the classical
obstruction theory of invertible sheaves along square-zero extensions, which Murre's proof sketch
of (F8) (Bourbaki exp. 294, printed p. 257) uses. The Lean statements are at the level of Čech
cochains and do not mention cohomology.
