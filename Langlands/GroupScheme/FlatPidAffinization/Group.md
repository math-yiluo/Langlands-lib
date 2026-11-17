# Actual canonical affinization groups over a PID

For a ring `R : Type u` with `CommRing R`, `IsDomain R` and
`IsPrincipalIdealRing R`, and an actual group scheme `G` over `Spec R` whose
structural morphism is flat, quasi-compact and separated, this file constructs
`affinizationGroup G` and `toAffinizationGroup G : G ⟶ affinizationGroup G`.
The universe `u` is arbitrary. There is no finite-generation, finite-type,
smoothness, connectedness or commutativity premise.

The underlying object of `affinizationGroup G` is definitionally

```lean
Over.mk (Spec.map
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.X.hom.appTop))
```

Thus its underlying scheme is exactly the spectrum of global functions of
`G.X.left`. The lemma `affinizationGroup_X` records this equality by reflexivity.
`groupStructure G` exposes the actual `GrpObj` directly on this prescribed
object. It contains unit, multiplication and inverse morphisms together with
proofs of the group identities, rather than an existential assertion.

The construction restricts `algΓ R ⋙ algSpec R` to the Cartesian full
subcategory of flat quasi-compact separated schemes. The product comparison
in `Langlands.AlgebraicGeometry.FlatPidAffinizationProducts` proves that this
restriction preserves binary products; its terminal comparison is also an
isomorphism. These give preservation of finite products. The monoidal
structure is `Functor.Monoidal.ofChosenFiniteProducts`, and
`affinizationGroup G` is the image under `mapGrp` of `restrictedGroup G`.
In particular, the constructed unit and multiplication are the images of the
original operations composed with the inverse terminal and product
comparisons, and the inverse is the image of the original inverse. Mathlib's
`grpObjObj` supplies their group-axiom proofs from these comparisons and the
original group axioms.

The natural transformation `restrictedToAffinization` consists of the
canonical maps to the spectra of global functions. In Cartesian monoidal
categories, natural transformations between monoidal functors are monoidal.
Consequently `Functor.mapGrpNatTrans` makes this a group homomorphism.
Precomposing with `(restrictedGroupIso G).inv` gives the homomorphism from the
original group scheme. Its underlying scheme map is proved in
`toAffinizationGroup_left` to be exactly `G.X.left.toSpecΓ`; the proof reduces
the composition to the identity followed by `toSpecΓ`.
`toAffinization_isMonHom` explicitly exposes unit and multiplication
compatibility of the canonical over-base map under `groupStructure G`.

This is an internal construction expanding the affinization step used in
Prasad–Yu, *On quasi-reductive group schemes*, Proposition 3.1,
author-preprint p.5. The source uses the natural group structure on
`Spec Γ(G, O_G)` before establishing finite generation. The extension from
its DVR application to PIDs is internal: torsion-freeness of global sections
implies flatness over a PID, and the flat qcqs product comparison then supplies
the finite-product isomorphisms. The construction does not use the Raynaud
affineness criterion or the smooth-case target.

Source: `prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`,
Proposition 3.1, printed p.5.
