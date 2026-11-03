# Semidirect products of group objects

This module constructs the semidirect product `N ⋊ H` of group objects. It follows
Milne's construction (*Algebraic Groups*, Section 2.f, printed p.50): an action of
`H` on `N` by group automorphisms makes the functor of points
`T ↦ N(T) ⋊ H(T)` a group functor. Its underlying set functor is represented by
`N × H`. The module then specializes to group schemes, with `H` acting on a normal
subgroup by conjugation inside an ambient group `G`, and builds the homomorphism
`N ⋊ H ⟶ G`, `(n, h) ↦ j n * i h`.

## Generic part (cartesian monoidal category `C`)

- `isMonHom_of_mul_comp`: let `f : M ⟶ N` go from a monoid object to a group
  object. If `(x * y) ≫ f = (x ≫ f) * (y ≫ f)` for all generalized points `x, y`,
  then `f` is a monoid morphism. Preservation of the unit follows by cancellation
  in the group `𝟙_ C ⟶ N`.
- `AutAction H N`: a morphism `act : H ⊗ N ⟶ N` with three conditions on
  generalized points. The unit acts trivially, `(h * h') • n = h • (h' • n)`, and
  `h • (n * n') = (h • n) * (h • n')`, where `h • n` is `lift h n ≫ act`.
- `AutAction.autHom a T`: the induced group homomorphism
  `(T ⟶ H) →* MulAut (T ⟶ N)`.
- `AutAction.precomp f X`: precomposition with `f : T' ⟶ T`, as a group
  homomorphism of point groups.
- `AutAction.pointsFunctor a : Cᵒᵖ ⥤ GrpCat`: `T ↦ (T ⟶ N) ⋊ (T ⟶ H)`, the Mathlib
  semidirect product for `autHom a T`. Morphisms act by precomposition, through
  `SemidirectProduct.map`.
- `AutAction.representableBy a`: `N ⊗ H` represents the underlying set functor of
  `pointsFunctor a`. A point `x` is sent to `⟨x ≫ fst, x ≫ snd⟩`.
- `AutAction.obj a := N ⊗ H`, with the group object structure transported from
  `pointsFunctor a` (Mathlib `GrpObj.ofRepresentableBy`).
- Coordinates: `left : obj ⟶ N`, `right : obj ⟶ H`, the point `pt n h` with given
  coordinates, the simp lemmas `pt_left` and `pt_right`, and `hom_ext` and `eta`.
- `mul_left`, `mul_right`, `one_left`, `one_right`: points multiply as in the
  semidirect product, `(x * y)` has coordinates
  `(x.left * (x.right • y.left), x.right * y.right)`, and the unit has coordinates
  `(1, 1)`. These follow from Mathlib's `yonedaGrpObjIsoOfRepresentableBy`.
- `right` is a monoid morphism (instance).
- `inl := pt (𝟙 N) 1 : N ⟶ obj` and `inr := pt 1 (𝟙 H) : H ⟶ obj`.

## Group schemes

Let `S` be a scheme, `i : H ⟶ G` and `j : N ⟶ G` homomorphisms of group schemes
over `S`, with `j` a monomorphism on underlying objects.

- `ConjStable i j`: for every test object `T`, `h : T ⟶ H` and `n : T ⟶ N`,
  the point `i h * j n * (i h)⁻¹` lies in the published `SubgroupFunctor.range j`.
- `conjStable_of_isNormal`: this holds when `range j` is normal.
- `conjAct hc : H ⊗ N ⟶ N`: the action `(h, n) ↦ j⁻¹ (i h * j n * (i h)⁻¹)`. It
  is chosen once at the universal point `(fst, snd)`. `conjAct_comp` computes its
  composite with `j` at every point.
- `conjAction hc : AutAction H N`, with the three axioms checked after
  cancelling the monomorphism `j`. `conjAction_act` unfolds its action map.
- `group hc : GroupScheme S`: the semidirect product `N ⋊ H` for this action.
- `mulMap hc := (left ≫ j) * (right ≫ i)`, i.e. `(n, h) ↦ j n * i h`.
  `mulMap_mul` shows it is multiplicative on points: using `conjAct_comp`, the
  identity becomes `j n * (i h * j n' * (i h)⁻¹) * (i h * i h') =
  j n * i h * (j n' * i h')`.
- The instance `IsMonHom (mulMap hc)` and `mulHom hc : group hc ⟶ G` (Mathlib
  `Grp.homMk`), with `mulHom_hom_hom`.
- `pt_mulMap`, `inl_mulMap`, `inr_mulMap`: `pt n h ↦ j n * i h`, and the
  composites with `inl` and `inr` are `j` and `i`.

## Provenance

The semidirect product and its multiplication `(n, q) (n', q') = (n · q n', q q')`
are Milne Section 2.f, printed p.50 (PDF p.66). The functor-of-points
construction is implemented with Mathlib's `SemidirectProduct` and
`GrpObj.ofRepresentableBy`, over any cartesian monoidal category. The conjugation
action of a subgroup `H` normalizing `N`, and the homomorphism `N ⋊ H ⟶ G` given by
multiplication in `G`, are Milne Section 5.f, printed p.111 (PDF p.127). Milne
defines the subgroup `NH` as the image of this homomorphism. Here `H` and `N` map to
`G` by `i` and `j`, `j` a monomorphism, and stability under conjugation is the
explicit hypothesis `ConjStable i j`. The module is an internal helper for forming
that image in the split unipotent radical existence proof.
