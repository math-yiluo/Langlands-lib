# Containment of a full special-fibre kernel in an open chart

This module proves that a scheme-theoretic kernel lies in an open subscheme,
first over an algebraically closed field and then for the special fibre of a
smooth integral model. The hypothesis in both cases is about rational points
only. This is internal infrastructure, not a result stated in this form in the
literature. It is support for the proof of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Proposition 8.4.15 (printed pp. 306–307 /
PDF pp. 337–338). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

**What this does not do.** This module does **not** prove KP Proposition
8.4.15 or the Library statement
`Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelStatement`. It does
not construct any open cell. It does not show that kernel elements of an
unramified parahoric model satisfy the rational-point hypothesis. It does not
prove smoothness, connectedness or unipotence of any kernel. It supplies only
the passage from rational points to the full scheme-theoretic kernel.

## Context and provenance

In the proof of KP 8.4.15, the authors claim that `ker(ρ_{Ω,Ω'})` lies in the
special fibre of the open cell of `G⁰_{Ω'}` (PDF p. 338, the paragraph
beginning "Fix a system of positive roots"). They check this for an element
`g ∈ ker(ρ_{Ω,Ω'})(f)`: they lift `g` to `G⁰_{Ω'}(O)`, show that the lift lies
in the integral points of the open cell, and conclude that "g lies in the
special fibre of the open immersion". Then they treat the kernel as a scheme,
as a product of root-group kernels. KP leave implicit the step from
`f`-points to the whole kernel *scheme*, which may be non-reduced a priori. This
module proves that step in general. It uses only two facts:

* over an algebraically closed field, the closed points of a scheme locally of
  finite type are rational points and are dense in every closed subset (the
  Jacobson property);
* over a Henselian local ring, rational points of the special fibre of a smooth
  model lift to integral sections (KP Lemma 8.1.3 for `n = 1`, published as
  `Langlands.GroupScheme.IntegralModel.reduction_surjective`).

The statements and their arrangement are internal design by Worker 4783 for
Task 6203, which Worker 282 and Worker 4783 share. The conclusion of
`Hom.exists_specialFibreKernel_lift` has the form of the hypothesis
`l ≫ m = kernelι q` of Worker 282's published
`Langlands.GroupScheme.KernelProductChart.iso`, so the two results compose.

## Results over a field

Let `k` be a field and `q : G ⟶ H` a homomorphism of group schemes over
`Spec k`.

* `kernel_locallyOfFiniteType`: if `G` is locally of finite type over `k`, so is
  the kernel `kernel q`. The unit section `η[H.X]` is locally of finite type,
  because composing it with the structure map gives the identity. The kernel
  inclusion is a base change of the unit section by
  `kernel_isPullback_scheme`. The structure map of the kernel is that inclusion
  followed by the structure map of `G`.
* `kernelι_rationalPoint_map`: a rational point of `kernel q`, composed with the
  kernel inclusion, is a rational point of `G` that `q` sends to `1`. This is the
  membership part of the published `kernelPointsEquiv`.

Assume in addition that `k` is algebraically closed and `G` is locally of finite
type.

* `kernelι_range_subset_of_rationalPoints`: let `U` be an open subset of the
  underlying space of `G`. Suppose that for every rational point `p` of `G` with
  `q(p) = 1`, the image of the closed point of `Spec k` under `p` lies in `U`.
  Then the image of the underlying map of the kernel inclusion lies in `U`.
  *Proof.* Suppose a point `y` of the kernel maps outside `U`. The preimage `Z`
  of the complement of `U` is closed in the kernel and contains `y`. The kernel
  is locally of finite type over a field, hence a Jacobson space
  (`LocallyOfFiniteType.jacobsonSpace`). So `Z` contains a closed point `z`
  (`nonempty_inter_closedPoints`). Since `k` is algebraically closed, `z` is the
  location of a rational point `x` of the kernel (the published bijection
  `rationalPointEquivClosedPoint`). Its image in `G` is a rational point killed
  by `q`, so by hypothesis it lies in `U`. That contradicts `z ∈ Z`.
* `exists_kernel_lift_of_rationalPoints`: let `m : P ⟶ G.X` be a morphism over
  `Spec k` whose underlying map is an open immersion. Suppose every rational
  point of `G` killed by `q` has its location in the range of `m`. Then there is
  a morphism `l : (kernel q).X ⟶ P` over `Spec k` with `l ≫ m` equal to the
  kernel inclusion. The previous result gives containment of the ranges, and
  `IsOpenImmersion.lift` factors the kernel inclusion through `m`. The
  factorization is compatible with the structure maps because `m` is a morphism
  over `Spec k`. This is a factorization of morphisms of schemes, not just of
  points, so non-reduced structure of the kernel is kept.

## Results for integral models

Let `R` be a local domain with fraction field `K`, and `M` an integral model
(`Langlands.GroupScheme.IntegralModel`) of a group scheme `G` over `Spec K`. The
actual special fibre `M.specialFibre` is the base change of the total space
along `residueBaseMap R : Spec(R/𝔪) ⟶ Spec R`.

* `specialFibreProjection M` is the first pullback projection from the special
  fibre to the total space of `M`.
* `residueBaseMap_closedPoint`: the residue base map sends the unique point of
  `Spec(R/𝔪)` to the closed point of `Spec R` (`IsLocalRing.comap_closedPoint`).
* `specialFibreProjection_reduction`: for an integral section `x`, the
  projection of the point of its reduction `M.reduction x` is the image of the
  closed point of `Spec R` under `x`. This follows from `reduction_left`
  (the reduction is the pullback lift of `residueBaseMap R ≫ x.left` and the
  identity) and the previous fact.
* `specialFibre_pullback_map_isOpenImmersion`: if `j : P ⟶ M.group.X` is a
  morphism over `Spec R` whose underlying map is an open immersion, then its
  base change `(Over.pullback (residueBaseMap R)).map j` to the special fibre
  is again an open immersion. The base change is identified with
  `pullback.map … j.left (𝟙 _) (𝟙 _)`, and open immersions are stable under base
  change.

Now assume that `R` is a Henselian local ring with algebraically closed residue
field. Let `φ : M.Hom N f` be a morphism of integral models over `f : G ⟶ H`,
with `M` smooth (`M.IsSmooth`). Write `φ.specialFibreMap` for the induced
homomorphism of special fibres.

* `Hom.specialFibreKernel_subset`: let `U` be an open subset of the total
  space of `M`. Suppose every integral section `x` of `M` whose image
  `φ(x)` reduces to `1` in `N` has `x(closed point) ∈ U`. Then every point of
  the scheme-theoretic kernel of `φ.specialFibreMap` projects into `U`.
  *Proof.* The special fibre of `M` is locally of finite type over the residue
  field, being a base change of the smooth structure map. Apply
  `kernelι_range_subset_of_rationalPoints` to the preimage of `U`. A rational
  point `p` of the special fibre killed by `φ.specialFibreMap` is the reduction
  of an integral section `x` (`reduction_surjective`, which uses Henselianity
  and smoothness of `M`). By `Hom.reduction_naturality`, `φ(x)` reduces to
  `1`. So `x(closed point) ∈ U`, and by `specialFibreProjection_reduction` the
  location of `p` projects into `U`.
* `Hom.exists_specialFibreKernel_lift`: let `j : P ⟶ M.group.X` be a morphism
  over `Spec R` that is an open immersion. Suppose every integral section `x` of
  `M` whose image `φ(x)` reduces to `1` has `x(closed point)` in the range of
  `j`. Then there is a morphism
  `l : (kernel φ.specialFibreMap).X ⟶ (Over.pullback (residueBaseMap R)).obj P`
  over the residue field with
  `l ≫ (Over.pullback (residueBaseMap R)).map j = kernelι φ.specialFibreMap`.
  *Proof.* Apply `exists_kernel_lift_of_rationalPoints` to the base change of
  `j`, an open immersion by `specialFibre_pullback_map_isOpenImmersion`. Lift a
  rational point `p` killed by the special-fibre map to an integral section `x`
  as before. Every point of `Spec R` specializes to the closed point, and the
  range of `j` is open. So the hypothesis `x(closed point) ∈ range j` gives
  `range x ⊆ range j`, and `x` factors as `y ≫ j` (`IsOpenImmersion.lift`).
  The pullback lift of `residueBaseMap R ≫ y` and the identity is then a
  residue point of the base change of `P`. Its composite with the base change
  of `j` equals `M.reduction x = p`, which we check componentwise with
  `pullback.hom_ext`. So the location of `p` lies in the range of the base
  change of `j`.

The hypotheses are about integral sections, not about kernels of `R`-schemes.
In the intended use, `j` is the open cell of the source parahoric model. The
hypothesis is then KP's claim that an `O`-point of `G⁰_{Ω'}` whose image
reduces to the identity lies in the integral points of the open cell. That
claim is not proved here.

KP state their results for the ring of integers `O` of the maximal unramified
extension of a discretely valued Henselian field. Its residue field is the
algebraic closure `f` of the residue field of `k`. The Lean results assume only
a Henselian local domain with algebraically closed residue field, with no
discreteness or completeness hypothesis.
