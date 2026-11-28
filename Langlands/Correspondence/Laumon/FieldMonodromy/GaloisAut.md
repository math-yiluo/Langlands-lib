# The Galois group of a field as the fundamental group of its spectrum

Module `Langlands.Correspondence.Laumon.FieldMonodromy.GaloisAut`, namespace
`Langlands.Henniart.Laumon`.

Let `K` be a field, `Ω` a separable closure of `K` (Mathlib's `IsSepClosure K Ω`, both in one
universe `u`) and `Ω̄ = AlgebraicClosure Ω`. The module
`Langlands.Correspondence.Laumon.FieldMonodromy` defines the geometric point
`fieldGeometricPoint K Ω : Spec Ω̄ → Spec K` and the action
`fieldGaloisToAut K Ω : Gal(Ω/K) →* Aut (fiber (fieldGeometricPoint K Ω))` on the finite étale
fibre functor of weil-conjectures, `AlgebraicGeometry.Scheme.FiniteEtale.fiber`: `σ` is
extended to `Ω̄` (`fieldGaloisLift K Ω σ`) and acts on a point `t : Spec Ω̄ → P` by
`t ↦ Spec (fieldGaloisLift K Ω σ) ≫ t`. This module proves that this action identifies
`Gal(Ω/K)` with the fundamental group of `Spec K` at this geometric point, as topological
groups. This is the profinite identification of the fundamental group of the spectrum of a
field, Stacks Project, Lemma 58.6.3 (Tag 0BNE), used in Laumon (1987), Remarque (2.1.2.1),
p. 152.

## Main results

- `fieldGalois_isFundamentalGroup` (an instance): `Gal(Ω/K)`, with Mathlib's Krull topology
  and the action `fieldGaloisFiberMulAction` (`σ • t = (fieldGaloisToAut K Ω σ) • t`), is a
  fundamental group of the fibre functor `fiber (fieldGeometricPoint K Ω)` in the sense of
  Mathlib's `CategoryTheory.PreGaloisCategory.IsFundamentalGroup`: the action is natural,
  continuous for the discrete topology on the fibres, transitive on the fibres of Galois
  objects, and only the identity acts trivially on all fibres.
- `toAut_eq_fieldGaloisToAut`: Mathlib's `CategoryTheory.PreGaloisCategory.toAut` for this
  action is `fieldGaloisToAut K Ω`.
- `fieldGaloisToAut_isHomeomorph`: `fieldGaloisToAut K Ω` is a homeomorphism (`IsHomeomorph`)
  from `Gal(Ω/K)` onto `Aut (fiber (fieldGeometricPoint K Ω))` with the topology Mathlib puts
  on automorphism groups of functors to finite sets (`CategoryTheory.PreGaloisCategory`,
  module `Mathlib.CategoryTheory.Galois.Topology`). Being a group homomorphism, it is an
  isomorphism of topological groups, `fieldGaloisContinuousMulEquiv`.

This is clause 1 of `FiniteEtaleFieldMonodromyStatement`.

## Points with values in `Ω` and in `Ω̄`

For a finite étale `K`-scheme `P`, `fieldFiberLift K Ω` sends a `K`-morphism
`y : Spec Ω → P` (an element of the fibre of Mathlib's point
`AlgebraicGeometry.Scheme.pointSmallEtale` of the small étale site at `Spec Ω → Spec K`) to
the point `Spec Ω̄ → Spec Ω → P` of `fiber (fieldGeometricPoint K Ω)`.

- `fieldFiberLift_injective`: precomposition with `Spec Ω̄ → Spec Ω` is injective on morphisms
  out of `Spec Ω` (weil-conjectures's `AlgebraicGeometry.Scheme.specMap_comp_injective`).
- `fieldFiberLift_surjective`: every `K`-morphism `Spec Ω̄ → P` factors through `Spec Ω`. Its
  image is a point `p` of `P` with a `K`-embedding of the residue field `κ(p)` into `Ω̄`; since
  `P` is étale over `K`, `κ(p)` is separable over `K`, so its image lies in the separable
  closure of `K` in `Ω̄`, which is `Ω` (weil-conjectures's
  `AlgebraicGeometry.Scheme.exists_specAlgebraMap_comp_eq`).
- `fieldGaloisToAut_fieldFiberLift`: `fieldFiberLift` carries precomposition with `Spec σ` on
  points `Spec Ω → P` to the action of `fieldGaloisToAut K Ω σ`, because the extension of `σ`
  to `Ω̄` restricts to `σ` on `Ω` (`fieldGaloisLift_algebraMap`).
- `fiber_map_fieldFiberLift`: `fieldFiberLift` is natural in `P`.

## The proof

On the side of `Ω`, the proof uses weil-conjectures's study of the Galois point
`AlgebraicGeometry.Scheme.galoisPoint K Ω` of `Spec K` (module
`WeilConjectures.AlgebraicGeometry.Sites.GaloisModule`), whose fibre functor is that of
`pointSmallEtale (Spec Ω → Spec K)` lifted to the next universe. For a finite subextension `E`
of `Ω / K`, `Spec E` is a finite étale `K`-scheme (`finiteEtaleSpecOfIntermediateField`) with
the canonical point `x_E : Spec Ω → Spec E`; weil-conjectures proves that every point of every
étale `K`-scheme is the image of some `x_E` under a morphism `Spec E → X`
(`exists_galoisPoint_fiber_map_eq`), that the points of `Spec E` form one `Gal(Ω/K)`-orbit
(`exists_galoisPointAct_galoisPointFiberSpec_eq`), and that the stabilizer of `x_E` is the
fixing subgroup of `E` (`galoisPointAct_galoisPointFiberSpec_eq_iff`).

The four conditions of `IsFundamentalGroup` are then checked as follows, transporting along
the bijection `fieldFiberLift`.

1. **Naturality.** `fieldGaloisToAut K Ω σ` is a natural transformation.
2. **Continuity.** A point `y : Spec Ω → X` is the image of some `x_E`, so its stabilizer
   contains the fixing subgroup of `E` (`exists_fixingSubgroup_le_stabilizer`), which is open
   in the Krull topology since `E` is finite over `K`. A subgroup containing an open subgroup is
   open, and on a discrete space an action with open stabilizers is continuous (Mathlib's
   `continuousSMul_iff_stabilizer_isOpen`).
3. **Transitivity on Galois objects.** Let `X` be a Galois, hence connected, finite étale
   `K`-scheme, and `t₀` a point of its fibre. It comes from a point `Spec Ω → X`, the image of
   some `x_E` under a morphism `g : Spec E → X`. As `X` is connected and the fibre of `Spec E` is
   nonempty, `g` is surjective on fibres (Mathlib's
   `surjective_of_nonempty_fiber_of_isConnected`). As the fibre of `Spec E` is one orbit and
   `g` commutes with the action, every point of the fibre of `X` lies in the orbit of `t₀`.
4. **Faithfulness.** If `σ` acts trivially on all fibres, it fixes the point `x_E` of
   `Spec K⟮a⟯` for every `a ∈ Ω` (`K⟮a⟯` is finite over `K`), so `σ` fixes `K⟮a⟯` and
   `σ a = a`.

Mathlib's `CategoryTheory.PreGaloisCategory.toAut_isHomeomorph` then shows that `toAut` is a
homeomorphism for every compact fundamental group; `Gal(Ω/K)` is compact since `Ω / K` is
Galois. The category of finite étale `K`-schemes is a Galois category with fibre functor
`fiber (fieldGeometricPoint K Ω)` by weil-conjectures's instances
`AlgebraicGeometry.Scheme.FiniteEtale.galoisCategory` and
`AlgebraicGeometry.Scheme.FiniteEtale.fiberFunctor`, as `Spec K` is connected.

## External declarations

From weil-conjectures: `AlgebraicGeometry.Scheme.specAlgebraMap`,
`AlgebraicGeometry.Scheme.galoisOverHom`, `AlgebraicGeometry.Scheme.galoisPoint`,
`AlgebraicGeometry.Scheme.galoisPointAct`, `AlgebraicGeometry.Scheme.galoisEtaleSpec`,
`AlgebraicGeometry.Scheme.galoisPointFiberSpec`,
`AlgebraicGeometry.Scheme.exists_galoisPoint_fiber_map_eq`,
`AlgebraicGeometry.Scheme.exists_galoisPointAct_galoisPointFiberSpec_eq`,
`AlgebraicGeometry.Scheme.galoisPointAct_galoisPointFiberSpec_eq_iff`,
`AlgebraicGeometry.Scheme.galoisPointAct_fiber_map_galoisPointFiberSpec`,
`AlgebraicGeometry.Scheme.exists_specAlgebraMap_comp_eq`,
`AlgebraicGeometry.Scheme.specMap_comp_injective`,
`AlgebraicGeometry.Scheme.FiniteEtale.fiber`, `AlgebraicGeometry.Scheme.FiniteEtale.fiber_ext`,
`AlgebraicGeometry.Scheme.FiniteEtale.fiber_left_comp`,
`AlgebraicGeometry.Scheme.FiniteEtale.galoisCategory`,
`AlgebraicGeometry.Scheme.FiniteEtale.fiberFunctor`. From Mathlib:
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`,
`CategoryTheory.PreGaloisCategory.toAut`,
`CategoryTheory.PreGaloisCategory.toAut_isHomeomorph`,
`CategoryTheory.PreGaloisCategory.surjective_of_nonempty_fiber_of_isConnected`,
`continuousSMul_iff_stabilizer_isOpen`, `IntermediateField.fixingSubgroup_isOpen`. Under
`#print axioms`, `fieldGaloisToAut_isHomeomorph` depends only on `propext`,
`Classical.choice` and `Quot.sound`.
