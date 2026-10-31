# Isogenies on points valued in an algebraically closed field

This helper module proves three facts about an isogeny `f : G ⟶ H` of group
schemes over `S`, in the Library's finite-flat-surjective sense
(`Langlands.GroupScheme.IsIsogeny`). The points are taken over a morphism
`s : Spec K ⟶ S`. Two of the facts need `K` to be algebraically closed. They are
used by the reduction of rational prime-adic polarization Weil nondegeneracy,
where `f` is the underlying homomorphism of a polarization.

Classically these are the facts behind Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Chapter X,
Proposition (10.6) and Corollary (10.7), printed p.144: an isogeny induces an
isomorphism on rational Tate modules. The proofs below work directly with points
and do not follow that source's Ext argument.

## Declarations

- `Langlands.GroupScheme.exists_pow_quasiInverse`. This is pure group theory.
  Let `φ : M →* M'` be a surjective homomorphism of commutative groups whose
  kernel is finite. Put `N = Nat.card φ.ker`, so `0 < N`. Every kernel element
  satisfies `x ^ N = 1`, by `pow_card_eq_one'` in the finite group `φ.ker`.
  Hence `powMonoidHom N` factors through `M ⧸ φ.ker`
  (`QuotientGroup.lift`). Composing with the inverse of the first isomorphism
  theorem `QuotientGroup.quotientKerEquivOfSurjective` gives `ψ : M' →* M`
  with `ψ (φ x) = x ^ N`. Applying `φ` and surjectivity then gives
  `φ (ψ y) = y ^ N`.
- `Langlands.GroupScheme.pointsHom f T`. An abbreviation for the homomorphism of
  point groups `(T ⟶ G.X) →* (T ⟶ H.X)` induced by `f`, namely
  `IsMonHom.monoidHom f.hom.hom T`. It sends `x` to `x ≫ f.hom.hom`.
- `Langlands.GroupScheme.IsIsogeny.pointsHom_surjective`. Assume `K` is
  algebraically closed. The underlying morphism of an isogeny is finite, hence
  locally of finite type, and surjective. A point `y : Over.mk s ⟶ H.X` has
  underlying morphism `y.left : Spec K ⟶ H.X.left`. By
  `Langlands.exists_point_lift_of_locallyOfFiniteType_surjective` there is
  `a : Spec K ⟶ G.X.left` with `a ≫ f.hom.hom.left = y.left`. Since `f` lies
  over `S`, `a` lies over `s`, so `Over.homMk a` is a point of `G` over `s`
  that maps to `y`.
- `Langlands.GroupScheme.IsIsogeny.finite_ker_pointsHom`. Here `K` is any field.
  Let `e : Spec K ⟶ H.X.left` be the underlying morphism of the identity point.
  A kernel point `x` satisfies `x.left ≫ f.hom.hom.left = e`. It therefore gives
  a section `pullback.lift x.left (𝟙 _)` of the second projection
  `pullback f.hom.hom.left e ⟶ Spec K`. This projection is finite, as a base
  change of a finite morphism. By
  `Langlands.AlgebraicGeometry.FiniteEtale.finite_sections_of_isFinite` it has
  only finitely many sections. The assignment is injective: composing a section
  with the first projection recovers `x.left`. So the kernel is finite
  (`Finite.of_injective`).
- `Langlands.GroupScheme.IsIsogeny.exists_points_quasiInverse`. Assume `K` is
  algebraically closed and both group objects are commutative. Applying
  `exists_pow_quasiInverse` to `pointsHom f (Over.mk s)` gives `N > 0` and two
  facts. First, every point `x` over `s` with `x ≫ f.hom.hom = 1` satisfies
  `x ^ N = 1`. Second, there is a homomorphism `ψ` from points of `H` to points
  of `G` with `ψ y ≫ f.hom.hom = y ^ N`. The other composite identity
  `ψ (x ≫ f) = x ^ N` is proved but not exported, because the reduction does not
  need it.

The module adds no hypotheses beyond those displayed. Its proofs use only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
