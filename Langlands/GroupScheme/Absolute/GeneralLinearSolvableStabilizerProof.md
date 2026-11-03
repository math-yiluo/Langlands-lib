# Proof that `GL_N` acts on a proper scheme with solvable point stabilizers

Authors: Worker 1399 (flag scheme, action, properness, fixed-point reduction, assembly and this
description), using Worker 135's module `Langlands.LinearAlgebra.FullFlagSolvable` (whose
interface was designed by Worker 1399) for the linear-algebra step.

The module proves

```
theorem Langlands.GroupScheme.generalLinearSolvableStabilizer :
    GeneralLinearSolvableStabilizerStatement.{u}
```

for the published proposition of
`Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerStatement`, at arbitrary universe
`u`. For every algebraically closed field `k : Type u` and every `N : ℕ` (including `N = 0`),
it constructs `X : Over (Spec k)` and an actual
`SchemeAction (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)) X` with `IsProper X.hom`
and `Nonempty X.left`. Every closed subgroup `i : H ⟶ GL_N` such that `(a.restrict i).IsFixed x`
for a rational point `x` satisfies `IsSolvableGroupScheme H`. The proof does not use that `k` is
algebraically closed and does not use Borel conjugacy.

## Mathematical context and route

The textbook witness is the flag variety of `k^N`. It represents the functor of full flags of
locally free direct summands (Milne, *Algebraic Groups* (2017), Propositions 7.29–7.30,
printed p.146). It is projective, and the stabilizer of a full flag is a conjugate of the upper
triangular group, which is solvable (Example 6.28, printed p.132). The implemented route
differs. The Library has single Grassmannians and their projective embeddings but no flag
schemes. So the witness `Z` is a closed subscheme of ONE quotient Grassmannian,
`G(rank N, Idx N → k)`, cut out by the linear condition `FlagLocus.Stable`. Over a field, the
stable points correspond to full flags of `K^N`. This uses copies of `K^N` with multiplicity
`(N + 1)^j` at level `j` and a base-`(N + 1)` digit argument, from
`Langlands.RingTheory.Grassmannian.FlagLocus`. Only this field-level correspondence is used:
the proof does not identify `Z` with the flag scheme over arbitrary rings.

## Points and action (namespace `Langlands.GroupScheme.FlagScheme`)

- `Pt k N A`: the stable points of `G(rank N, A ⊗[k] (Idx N → k); A)` for a `k`-algebra `A`.
  `Pt.map φ` is the Library base change `Module.Grassmannian.map φ` (stability is kept by
  `FlagLocus.Stable.map`). `Pt.smul g` is `FlagLocus.smul k g` for `g : GL (Fin N) A`
  (stability is kept by `FlagLocus.Stable.smul`).
- Section `Witness`: fix a scheme `Z` with `q : Z ⟶ Spec k` and bijections `ptZ A` between
  `Pt k N A` and the morphisms `Spec A ⟶ Z` over `Spec k`. `ptOver` rewrites them as morphisms
  `specOver A ⟶ Over.mk q` in `Over (Spec k)`. Under the naturality hypothesis `hptZ`
  (base change of points corresponds to precomposition), `ptOver_map` states
  `ptOver (s.map φ) = specMapOver φ ≫ ptOver s`.
- `exists_action`: there is a `SchemeAction` `a` of `GL_N` on `Over.mk q` whose action on an
  affine point `y` over `A` by a point `h` of `GL_N` over `A` is
  `ptOver ((ptOver⁻¹ y).smul (matrixOf h))`. This is
  `GeneralLinear.exists_schemeAction_of_affine` (module
  `Langlands.GroupScheme.GeneralLinearActionOfPoints`) applied to the transported action. Its
  three hypotheses are `FlagLocus.map_smul_point` (naturality, via `ptOver_map`),
  `FlagLocus.one_smul` and `FlagLocus.mul_smul`.

## Fixed points and solvability (section `Stabilizer`, any field `k`)

- `isSolvable_points_of_isFixed`: let `x` be a rational point fixed by the restricted action
  `a.restrict i` of a subgroup `i : H ⟶ GL_N`. Let `K` be a field `k`-algebra, `T` a test
  object and `e : specOver K ⟶ T` such that `g ↦ e ≫ g ≫ i` is injective on points `T ⟶ H.X`.
  Then the group `T ⟶ H.X` is solvable. Proof:
  1. `ρ g := matrixOf (e ≫ g ≫ i)` is a group homomorphism `(T ⟶ H.X) →* GL (Fin N) K`
     (`MonObj.mul_comp`, `MonObj.comp_mul`, `matrixOf_mul`). It is injective by the
     hypothesis on `e` and `matrixOf_injective`.
  2. Let `s` be the stable point over `K` corresponding to the `K`-point `toUnit ≫ x`.
     Fixedness, applied to the test `specOver K`, the map `toUnit`, and the point `e ≫ g`,
     together with `SchemeAction.restrict_act` and the action formula of `exists_action`, gives
     `FlagLocus.smul k (ρ g) s = s` for every `g`.
  3. `FlagLocus.exists_fullFlag` gives a full flag `F` of `K^N` (monotone,
     `finrank (F j) = j`) preserved by `Matrix.mulVec` of every matrix fixing `s`, in
     particular by every `ρ g`.
  4. Worker 135's `LinearAlgebra.isSolvable_of_injective_representation_fullFlag` turns the
     injective representation `ρ` preserving `F` into `Group.IsSolvable (T ⟶ H.X)`.
- `isSolvableGroupScheme_of_isFixed`: if moreover `i` is a closed subgroup, then
  `IsSolvableGroupScheme H`. Take `K := AlgebraicClosure k`,
  `T := (Over.map (toAlgebraicClosure k)).obj (Over.mk (𝟙 _))` (`Spec k̄` as an object over
  `Spec k`) and `e` the identity of `Spec k̄`. Injectivity holds because the closed immersion
  `i.hom.hom.left` is a monomorphism. The Library's multiplicative equivalence
  `baseChangePointsEquiv (toAlgebraicClosure k) H (Over.mk (𝟙 _))` identifies the points of
  the base change of `H` to `k̄` (the group in the definition of `IsSolvableGroupScheme`) with
  the group `T ⟶ H.X`. Solvability is then transported along this injective homomorphism
  (`Group.isSolvable_of_isSolvable_injective`).

## Assembly (`generalLinearSolvableStabilizer`)

1. The Library theorem `Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace`,
   applied to the finite free `k`-module `Idx N → k` and rank `rank N`, gives a scheme `Gr`
   over `Spec k`. It represents the functor of points `Module.Grassmannian A (A ⊗[k] (Idx N → k)) (rank N)`
   naturally in `A` (`pt`, `hnat`). It has a closed immersion `ιP` into projective space
   `Proj k[x_0, …, x_m]` over `Spec k` with `ιP ≫ ProjSpace.π k m = p`.
2. The Library theorem `AlgebraicGeometry.Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal`,
   applied with the condition `FlagLocus.Stable k`, which is cut out by ideals by
   `FlagLocus.exists_ideal_stable_map_iff`, gives a closed immersion `ιZ : Z ⟶ Gr`. `Z`
   represents `Pt k N` (`ptZ`) compatibly with `pt` (`hptZ`). Naturality of `ptZ` follows by
   cancelling the monomorphism `ιZ` and using `hnat`.
3. `X := Over.mk (ιZ ≫ p)` with the action `a` from `exists_action`.
4. Properness: `ιZ ≫ p = ιZ ≫ ιP ≫ ProjSpace.π k m` is a composite of two closed immersions
   (proper) and the proper projection of projective space (the Library instance
   `ProjSpace.isProper_π`).
5. Nonemptiness: the standard flag `FlagLocus.stdPoint N k k` is stable
   (`FlagLocus.stable_stdPoint`), so `ptZ k` gives a morphism `Spec k ⟶ Z`, and the image of
   the unique prime of `k` is a point of `Z`.
6. Stabilizers: `isSolvableGroupScheme_of_isFixed`.
