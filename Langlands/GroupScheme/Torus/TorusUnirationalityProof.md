# Proof: rationality of Weil-restricted multiplicative groups and unirationality of tori

Worker 91.

The theorem `Langlands.GroupScheme.torusUnirationality` proves the published proposition
`Langlands.GroupScheme.TorusUnirationalityStatement` (module
[`Torus.TorusUnirationalityStatement`](TorusUnirationalityStatement.md)) at an arbitrary
universe `u`:

```lean
theorem torusUnirationality : TorusUnirationalityStatement.{u}
```

Its type is exactly `TorusUnirationalityStatement.{u}`. No hypothesis is added and the
statement is not changed. In words, for every field `k`:

1. for every finite field extension `k'` of `k`, `(𝔾_m)_{k'/k}` is birational over `k` to a
   finite-dimensional affine space (Milne, *Algebraic Groups* (2017), Proposition 12.60);
2. every torus `T` over `k` is unirational: some nonempty open subscheme of a
   finite-dimensional affine space over `k` maps over `k` to `T` with dense image (first half
   of Milne's Proposition 12.64);
3. for every finite étale `k`-algebra `A`, the induced torus `(𝔾_m)_{A/k}` is birational over
   `k` to a finite-dimensional affine space (second half of Proposition 12.64).

The module compiles with no errors or warnings. The theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`. The module also proves the auxiliary results
listed below, in the namespace `Langlands.GroupScheme.TorusUnirationality`.

## Implemented proof

### Parts 1 and 3

Both are instances of `WeilGmRational.hasFiniteAffineBirationalModel k B` from the helper
module [`Torus.WeilRestrictionRational`](WeilRestrictionRational.md), which holds for every
commutative `k`-algebra `B` that is finite over `k`. Part 1 takes `B = k'`; the instance
`Module.Finite k k'` comes from `FiniteDimensional k k'`. Part 3 takes `B = A`. The
hypothesis `Algebra.Etale k A` is not used: the result holds for every finite algebra.

### Part 2: every torus is unirational

Milne derives Proposition 12.64 from Proposition 12.63 (every torus is a quotient of an
induced torus). The Lean proof uses a related route through Library results: the Galois norm
from the Weil restriction of the split torus is smooth, hence open.

**The split Weil homomorphism is an isomorphism.** Let `L / k` be a finite field extension,
`I` a finite type, `G` a group scheme over `L` and `σ : G ≅ 𝔾_m^I` (`splitTorus`). The
Library's `WeilGm.splitWeilHom k L I G σ` (module
[`Torus.WeilRestrictionSplitNorm`](WeilRestrictionSplitNorm.md)) is a homomorphism of
`k`-group schemes `Res_{(I → L)/k} 𝔾_m ⟶ Res_{L/k} G`. It is built by
`Corepresented.groupSchemeMap` from the natural transformation `WeilGm.splitWeilNat`, whose
component at a `k`-algebra `T` is `WeilGm.splitWeilPointHom`: a unit `w` of `(I → L) ⊗[k] T`
goes to the point of `G` over `L ⊗[k] T` whose split coordinates are the coordinates
`splitCoord i w` of `w`.

- `splitCoordUnits_bijective`: the coordinate map `((I → L) ⊗[k] T)ˣ → (I → (L ⊗[k] T)ˣ)` is
  bijective. It equals the unit map of the algebra isomorphism
  `(I → L) ⊗[k] T ≃ₐ[k] (I → L ⊗[k] T)` (built from `Algebra.TensorProduct.comm` and
  `Algebra.TensorProduct.piRight`) followed by `MulEquiv.piUnits`. The two maps are compared
  on pure tensors.
- `splitWeilPointHom_bijective`: `splitWeilPointHom` is the composite of three bijections:
  the coordinate map above, the inverse of the split-torus point equivalence
  `splitTorus.algebraPointsEquiv`, and composition with `σ.inv`. The last one is
  `Iso.homCongr` of the identity and the scheme isomorphism underlying `σ.symm`.
- `isIso_splitWeilNat`: every component of `splitWeilNat` is an isomorphism of groups
  (`ConcreteCategory.isIso_iff_bijective`), so the natural transformation is an isomorphism
  (`NatIso.isIso_of_isIso_app`).
- `groupSchemeMap_id`: `Corepresented.groupSchemeMap c c (𝟙 F) = 𝟙 _`. Both sides agree on
  affine points (`Corepresented.hom_ext_affinePoints`, `Corepresented.groupSchemeMap_affinePoints`).
- `isIso_splitWeilHom`: `splitWeilHom` has inverse `Corepresented.groupSchemeMap` of
  `inv splitWeilNat`. Both composites are the identity by `Corepresented.groupSchemeMap_comp`
  (module [`CorepresentedComultiplication`](../CorepresentedComultiplication.md)) and
  `groupSchemeMap_id`.

**`isUnirational_of_isTorus k T hT : IsUnirational k T.X`.** Let `T` be a torus over `k`.

1. `torusFiniteGaloisSplitting` (module
   [`Torus.FiniteGaloisSplittingProof`](FiniteGaloisSplittingProof.md)) gives a finite Galois
   extension `L / k` such that the base change `T_L` is a split torus.
2. `T` is commutative (`IsTorus.isCommMonObj`, module [`Torus.MaximalAmbient`](MaximalAmbient.md));
   let `Tc` be `T` as a commutative group scheme. `T` and `T_L` are affine
   (`SplittingAssembly.isAffine_of_isTorus`), and `T_L` is a torus (`IsSplitTorus.isTorus`)
   and hence smooth (`IsTorus.smooth`).
3. The Galois norm `N := GaloisNorm.norm k L Tc : Res_{L/k}(T_L) ⟶ T` (module
   [`Torus.GaloisNorm`](GaloisNorm.md)) is smooth by `GaloisNormSmoothnessProof.galoisNormSmoothness`
   (module [`Torus.GaloisNormSmoothnessProof`](GaloisNormSmoothnessProof.md)).
4. Choose `I` and `σ : T_L ≅ 𝔾_m^I` from the splitting and let
   `s := WeilGm.splitWeilHom k L I T_L σ : Res_{(I → L)/k} 𝔾_m ⟶ Res_{L/k}(T_L)`. It is an
   isomorphism (`isIso_splitWeilHom`), so its underlying scheme morphism is an isomorphism.
5. `Res_{(I → L)/k} 𝔾_m` is unirational. `WeilGmRational.hasFiniteAffineBirationalModel k (I → L)`
   gives a finite affine birational model, and `HasFiniteAffineBirationalModel.isUnirational`
   (module [`PointTopology.UnirationalTransport`](../../AlgebraicGeometry/PointTopology/UnirationalTransport.md))
   turns it into unirationality.
6. The underlying map of `s ≫ N` is open. Mathlib makes a smooth morphism flat and locally of
   finite presentation, hence universally open (`UniversallyOpen.of_flat`), and so an open
   map (`Scheme.Hom.isOpenMap`). An isomorphism is also an open map.
7. `T.X.left` is integral (`IsTorus.isIntegral`, module [`Torus.Integral`](Integral.md)),
   hence irreducible. The range of `s ≫ N` is open and nonempty, since the source is nonempty
   by `WeilGmRational.nonempty_left k (I → L)`. So the range is dense.
8. `IsUnirational.map` (module `PointTopology.UnirationalTransport`) composes the
   parametrization of `Res_{(I → L)/k} 𝔾_m` with `s ≫ N`, a morphism with dense range, and
   gives `IsUnirational k T.X`.

### The final theorem

`torusUnirationality` introduces `k` and assembles the three parts:
`WeilGmRational.hasFiniteAffineBirationalModel k k'`, `isUnirational_of_isTorus k T hT`, and
`WeilGmRational.hasFiniteAffineBirationalModel k A`.

## Relation to the literature

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`:
Definition 12.59 and Proposition 12.60 (p.250), Definition 12.62 and Proposition 12.64
(p.251). The source and the correspondence between Milne's statements and the Lean statement
are recorded in [`TorusUnirationalityStatement.md`](TorusUnirationalityStatement.md).

Parts 1 and 3 follow Milne's proof of Proposition 12.60. The proof of part 2 differs from
Milne's, which uses Proposition 12.63. Here, after splitting `T` over a finite Galois
extension `L`, the torus `Res_{L/k}(T_L)` is identified with `Res_{(I → L)/k} 𝔾_m`, which is
rational. The Galois norm `Res_{L/k}(T_L) ⟶ T` is smooth, so its image is a nonempty open,
hence dense, subset of the irreducible `T`.
