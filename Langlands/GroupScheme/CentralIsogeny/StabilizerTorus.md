# Stabilizers of torus-centralized points under central isogenies

Lean module: `Langlands.GroupScheme.CentralIsogeny.StabilizerTorus`, namespace
`Langlands.GroupScheme`.

This module proves `CentralIsogenyStabilizerTorusStatement` from
`Langlands.GroupScheme.CentralIsogeny.StabilizerTorusStatement`. Let `π : G ⟶ A` be a
central isogeny of group schemes over a field `K`, and let `a` be an action of `A` on `G`
with `a(π h) g = h g h⁻¹`. Suppose a rational point `x` of `G` has its centralizer, on
every test scheme, inside a closed torus `i : T ⟶ G`. Then there is a closed torus
`j : S ⟶ A` through which every point of `A` that fixes `x` under `a` factors.

## Declarations

- `exists_closedEmbedding_of_isTorus (hT : IsTorus T) (f : T ⟶ A)
  (hf : IsFinite f.hom.hom.left)`: if `T` is a torus over `Spec K`, `A` is any group scheme
  over `Spec K`, and the underlying scheme morphism of `f` is finite, then there are a
  group scheme `Q`, a central isogeny `q : T ⟶ Q` and a closed subgroup `φ : Q ⟶ A` with
  `q ≫ φ = f`. Moreover `Q` is smooth and affine over `Spec K`.
- `centralIsogenyStabilizerTorus : CentralIsogenyStabilizerTorusStatement.{u}`.

## Proof of `exists_closedEmbedding_of_isTorus`

`Q` is the quotient of `T` by the kernel of `f`, and `φ` is the map induced by `f`.

1. `A` is separated over the field (`fieldSeparated`), so the kernel inclusion
   `kernelι f` is a closed subgroup. The kernel's structure morphism is a base change of
   the finite morphism `f.hom.hom.left` (`kernel_isPullback_scheme`), so it is finite. The
   torus `T` is commutative (`IsTorus.isCommMonObj`), so the kernel is central and its
   range is normal. A torus is smooth and affine (`IsTorus.smooth`,
   `SplittingAssembly.isAffine_of_isTorus`).
2. The Library theorem `exists_centralIsogeny_of_finite_central_subgroup` gives a smooth
   affine `Q` and a central isogeny `q : T ⟶ Q` whose kernel has the same range as
   `kernelι f`. Hence `kernelι q ≫ f = 0` (`mem_range_kernelι_iff`).
3. `q` is finite, flat and surjective, so `FpqcHomDescent.hom q f` (Library,
   `GroupScheme/HomDescent`) is a homomorphism `φ : Q ⟶ A` with `q ≫ φ = f`
   (`FpqcHomDescent.fac`). The kernels of `f` and `q` have the same range, so the Library
   theorem `FpqcHomDescent.mono_of_kernel_range_le` shows that `φ` is a monomorphism of
   group objects. Its underlying scheme morphism `φ.hom.hom.left` is then a monomorphism
   (`Over.mono_left_of_mono`).
4. `φ.hom.hom.left` is proper. The composite `q.hom.hom.left ≫ φ.hom.hom.left` equals
   `f.hom.hom.left`, which is finite and so universally closed. Since `q.hom.hom.left` is
   surjective, `UniversallyClosed.of_comp_surjective` shows that `φ.hom.hom.left` is
   universally closed. Its composite with `A.X.hom` is the smooth structure morphism of
   `Q`, so `φ.hom.hom.left` is locally of finite type (`locallyOfFiniteType_of_comp`).
   Instance search supplies separatedness.
5. A proper monomorphism of schemes is a closed immersion
   (`IsClosedImmersion.iff_isProper_and_mono`, Mathlib), so `φ` is a closed subgroup.

## Proof of `centralIsogenyStabilizerTorus`

Take `K`, `π`, `a`, `x`, `i : T ⟶ G` and the hypotheses as in the statement.

1. **The torus.** The morphism `(i ≫ π).hom.hom.left` is finite, being the composite of a
   closed immersion and a finite morphism. Applying `exists_closedEmbedding_of_isTorus` to
   `i ≫ π` gives `q : T ⟶ Q` and a closed subgroup `φ : Q ⟶ A` with `q ≫ φ = i ≫ π`,
   where `Q` is smooth and affine. The Library theorem `torusImageClosedTorusStatement`
   (closed torus image of a torus) applied to `q` gives a commutative group scheme `Z`
   that is a torus, a closed subgroup `jZ : Z ⟶ Q` and `fZ : T ⟶ Z` with
   `fZ ≫ jZ = q`. Put `S := Z.toGrp` and `j := jZ ≫ φ`. This is a composite of closed
   immersions, so it is a closed subgroup.
2. **Lifting a fixed point.** Let `c : W ⟶ A.X` satisfy
   `a.act c (toUnit W ≫ x) = toUnit W ≫ x`. Form the scheme pullback `P` of `c.left` and
   `π.hom.hom.left`, with projections `r : P ⟶ W.left` and `h : P ⟶ G.X.left`. View `P`
   as a scheme over `Spec K` through `r` (call this object `W'`, with `rr : W' ⟶ W`).
   Then `h ≫ π = rr ≫ c` on `W'`.
3. **The lift centralizes `x`.** By the naturality of the action
   (`AutomorphicAction.naturality`), `rr ≫ c` fixes `toUnit W' ≫ x`. By the
   inner-action hypothesis, `a.act (h ≫ π) (toUnit W' ≫ x) = h (toUnit W' ≫ x) h⁻¹`.
   Hence `h` commutes with `toUnit W' ≫ x`. The centralizer hypothesis gives
   `t : W' ⟶ T.X` with `t ≫ i = h`.
4. **The point lies in `S` after the cover.** Put `s' := (t ≫ fZ).left`. Then
   `s' ≫ J = r ≫ c.left`, where `J` is the underlying scheme morphism of `j`. Indeed
   `fZ ≫ jZ ≫ φ = q ≫ φ = i ≫ π` and `t ≫ i ≫ π = h ≫ π = rr ≫ c`.
5. **Descent along the cover.** `r` is a base change of the finite, flat, surjective
   `π.hom.hom.left`. So it is flat, surjective and quasi-compact, and therefore an
   effective epimorphism (Mathlib instance in `AlgebraicGeometry.Sites.Fpqc`). `J` is a
   closed immersion, hence a monomorphism. If `g₁ ≫ r = g₂ ≫ r`, then
   `g₁ ≫ s' ≫ J = g₂ ≫ s' ≫ J`, so `g₁ ≫ s' = g₂ ≫ s'`. Thus `EffectiveEpi.desc` gives
   `s : W.left ⟶ Z.X.left` with `r ≫ s = s'`. Cancelling the epimorphism `r` gives
   `s ≫ J = c.left`. Then `s` is a morphism over `Spec K`, because `J` lies over
   `Spec K`. As a morphism `W ⟶ S.X` it satisfies `s ≫ j.hom.hom = c`.

Of `IsCentralIsogeny π` the proof uses only that `π` is finite, flat and surjective. It
does not use that the kernel of `π` is central: instead of `T / ker π`, it takes the
torus image of `T` in `T / ker(i ≫ π)`.

## Provenance

Provenance: derived. The argument follows the derivation in the statement's Markdown,
which derives the proposition from Steinberg, *Regular elements of semi-simple algebraic
groups* (1965), §11 (Kneser's remark on dropping simple connectedness): a torus in `A` is
built from the centralizer torus `T`, and a stabilizer point of `A` lifts to `G` after
the fppf cover by `π`. The implemented proof differs in two places. First, the torus is
the closed torus image of `T` in `T / ker(i ≫ π)` (Library
`torusImageClosedTorusStatement`), not `T / ker π`. Second, the lift is descended to `W`
by the effective-epimorphism property of the flat surjective cover, not by a sheaf-level
statement. `exists_closedEmbedding_of_isTorus` is an internal lemma written for this
proof. It records the standard fact that a homomorphism with finite underlying morphism
induces a closed embedding of the quotient by its kernel: a proper monomorphism is a
closed immersion.
