# Extension of additive functors to rationalized categories

Let C be a preadditive category, D a Q-linear preadditive category, and F : C → D an additive functor. The object and morphism universes of C and D are independent. This module constructs the extension of F to the existing `Langlands.Rationalization C`. Its morphisms are the actual tensor products Q tensor_Z Hom_C(X,Y), with composition and identities defined in `Langlands.CategoryTheory.Rationalization`.

All new declarations are in `Langlands.Rationalization`. For objects X and Y of C, `liftHom F` is a Q-linear map from the rationalized Hom group to Hom_D(F(X),F(Y)). It applies `TensorProduct.AlgebraTensorModule.lift` to the bilinear map (q,f) ↦ q • F(f). The input map on integral morphisms is `F.mapLinearMap ℤ`; it is Z-linear because F is additive. The outer Q-linearity is supplied by `LinearMap.id.smulRight`. Thus no map out of the tensor product is assumed. `liftHom_tmul` proves the defining formula

```
liftHom F (q tensor f) = q • F.map f.
```

`liftHom_ofHom` specializes this to the inclusion f ↦ 1 tensor f. `liftHom_comp` proves compatibility with the existing rationalized composition by induction on each tensor argument. Additive cases use linearity and bilinearity of composition. On pure tensors, the proof uses preservation of composition by F, bilinearity in D, and commutativity of rational multiplication.

`lift F : Rationalization C ⥤ D` sends the wrapped object X to F(X). Its map is `liftHom F`. The identity proof uses the tensor identity 1 tensor id and `F.map_id`; its composition proof is `liftHom_comp`. The supplied `Additive` instance follows from the linearity of `liftHom`. Mathlib's `Functor.ratLinear` consequently supplies Q-linearity of this additive functor between Q-linear categories. `lift_map_tmul` gives its pure-tensor formula. `inclusionLiftIso F` identifies `inclusion ⋙ lift F` with F by identity components; naturality is the integral-morphism formula.

`liftEnd F X` is the Q-algebra homomorphism from `Rationalization.End X` to the actual categorical endomorphism algebra of F(X). Both endomorphism rings use f*g = g ≫ f. Preservation of multiplication therefore follows from `liftHom_comp F g f`; the other ring laws follow from linearity and preservation of the identity. Compatibility with scalar algebra maps follows from the published formula q ↦ q tensor id in the source and q ↦ q • id in the target. `liftEnd_ofEnd` recovers F's map on integral endomorphisms, and `liftEnd_endTensor` proves the formula q tensor f ↦ q • F(f) as an equality of endomorphisms.

The provenance is derived algebra from the imported Library rationalization and the pinned Mathlib tensor universal property, additive-functor linear maps, and categorical endomorphism algebras. The new bilinear map, functor, natural isomorphism and algebra homomorphism are constructed here, with all their required laws proved. No external geometric theorem is used or claimed.

This is a prerequisite for the rational endomorphism action on a relative Lie module. It requires an actual additive functor F and a Q-linear target; it neither constructs the Lie module nor assumes that a geometric Lie functor already exists. Applying it to Lie requires the separate cotangent, dual and differential constructions and the proof of additivity of that differential. The file makes no assertion about base change, local freeness, geometric isogenies, or a localization universal property.
