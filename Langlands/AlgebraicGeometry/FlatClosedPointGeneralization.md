# Field points of flat schemes over a local ring

This internal module helps compare root data across the fibres of a group scheme
over a local ring. It is pure algebraic geometry; it mentions no group schemes.

Setting: `R : Type u` is a commutative ring, `X` a scheme in universe `u`,
`f : X ⟶ Spec R` a morphism, and `l : Type u` a field with an `R`-algebra
structure. Write `Spec l → Spec R` for `Spec.map (CommRingCat.ofHom (algebraMap R l))`.

`FieldPointLift f l` is a structure with these fields:

- a field `L : Type u` (fields `L` and `field`);
- an `l`-algebra structure on `L` (field `algebra`);
- a morphism `point : Spec L ⟶ X` with
  `point ≫ f = Spec.map (ofHom (algebraMap l L)) ≫ Spec.map (ofHom (algebraMap R l))`
  (field `comm`).

So it is an `L`-valued point of `X` over the composite `Spec L → Spec l → Spec R`.
The field and algebra fields are registered as instances.

`FieldPointLift.ofPullbackPoint w` builds such a lift from any point `w` of the
fibre product `pullback f (Spec l → Spec R)`. It needs no hypothesis on `R` or `f`:

- `L` is the residue field `κ(w)`.
- The `l`-algebra structure comes from the ring map `l → κ(w)`. This is
  `Spec.preimage` of `Spec κ(w) → pullback → Spec l`, the composite of
  `fromSpecResidueField w` with the second projection.
- `point` is `fromSpecResidueField w` composed with the first projection.

The compatibility follows from `pullback.condition` and `Spec.map_preimage`.

`nonempty_pullback_of_flat_of_closedPoint` assumes `R` is local, `f` is flat, and
`x : X` has `f x = IsLocalRing.closedPoint R`. Under these assumptions the fibre
product of `f` with `Spec l → Spec R` is nonempty, for every field `l` over `R`.
The proof:

- Let `t` be the point of `Spec l` and `s` its image in `Spec R`.
- Every point of a local spectrum specializes to the closed point
  (`IsLocalRing.specializes_closedPoint`), so `s ⤳ f x`.
- A flat morphism is generalizing (Mathlib's `Flat.generalizingMap`, from going
  down for flat ring maps). So some `z ⤳ x` has `f z = s`.
- `Scheme.Pullback.exists_preimage_pullback` gives a point of the fibre product
  over `z` and `t`.

`fieldPointLift f x hx l` is the definition and the record's declaration. Under the
same hypotheses it applies `ofPullbackPoint` to a point chosen with
`Nonempty.some` from the previous theorem.

`exists_extension_point_of_flat_of_closedPoint` is the existence form used
downstream. Under the same hypotheses, there are a field `L`, an `l`-algebra
structure on `L` and a morphism `g : Spec L ⟶ X` with
`g ≫ f = Spec.map (ofHom (algebraMap l L)) ≫ Spec.map (ofHom (algebraMap R l))`.
It unpacks `fieldPointLift f x hx l`.

Scope: `L` is not claimed to be finite, algebraic or separable over `l`. Nothing is
claimed about the location of `g` beyond its image in `Spec R`; in particular `g`
need not specialize to `x`.

Provenance: internal. The argument is the standard one: flat morphisms satisfy
going down (Stacks Project, Tag 03HV), and points of a fibre product exist over
any pair of points with a common image (Stacks Project, Tag 01JT). Every step uses
Mathlib results named above; no Library module is imported.
