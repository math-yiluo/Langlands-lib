# Lifting maximal split tori through a central isogeny, given a kernel exponent

Module `Langlands.GroupScheme.CentralIsogeny.MaximalSplitTorusLift`, namespace
`Langlands.GroupScheme.CentralSplitTorusLift`.

This module assembles the proof of
`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement` from one remaining
input: a positive integer `N` that kills every point of the kernel of the central isogeny.
It is an internal helper, not a literature statement. The literature proof is different.
Borel–Tits 1972 (source `borel-tits-1972-complements-groupes-reductifs`) prove Théorème
2.20(ii) on printed p.260, PDF p.9. They take a maximal `k`-torus `T'` of the target that
contains the given split torus. The inverse image of `T'` is a maximal torus of the source by
Proposition 2.11(iv), printed pp.256–257. Its maximal `k`-split subtorus maps onto the given
split torus. Proposition 2.11(iv) is not in the Library. Here the lift is built instead from
the power map of `Langlands.GroupScheme.CentralIsogeny.PowerLift`, and maximality comes from
a finiteness argument.

Throughout, `k` is a field and `G`, `H` are group schemes over `Spec k`.

## Imported helpers and declarations

* `injective_of_integral_comp_injective`: let `f : A →+* B` be integral, with `A` nontrivial
  and `B` a domain, and `g : B →+* C`. If `g ∘ f` is injective, then `g` is injective. The
  proof applies going-up (`Ideal.eq_bot_of_under_eq_bot`) to the kernel of `g`.
* `isIso_of_closedImmersion_finite_comp_schematic`: let `a : X ⟶ Y` be a closed immersion and
  `q : Y ⟶ Z` finite, with `Y` affine and integral and `Z` affine and nonempty. If `a ≫ q` is
  schematically dominant, then `a` is an isomorphism. Global sections reduce this to the
  previous lemma.
* `exists_splitSubtorus_lift_of_surjective_splitParametrization`: let `G` be affine over `k` and `π : G ⟶ H`. Let `D`, `S` be
  commutative group schemes with `D` a split torus. Let `a : D ⟶ G` and `b : D ⟶ S` be
  homomorphisms with `b` surjective on underlying schemes, and `i : S ⟶ H` a closed subgroup,
  with `a ≫ π = b ≫ i`. Then there is a split subtorus `j : T ⟶ G` and a homomorphism
  `f : T ⟶ S`, surjective on underlying schemes, with `j ≫ π = f ≫ i`. Here `T` is the
  closed image of `a` (`IsSplitTorus.dominantFactorization`), and `j` is its inclusion. Since
  `D ⟶ T` is schematically dominant, the range of `j ≫ π` lies in the range of `i`. So
  `j ≫ π` factors through `i` as `f`, and `f` is surjective because `D ⟶ T ⟶ S` equals `b`.
* `flat_and_locallyOfFinitePresentation`: let `G`, `H` be connected reductive, `j : T ⟶ G` and
  `i : S ⟶ H` split subtori, and `f : T ⟶ S` a homomorphism that is surjective on underlying
  schemes. Then `f` is flat and locally of finite presentation. `f` is locally of finite type
  between affine schemes of finite type over `k`, and `S` is integral and noetherian. Flatness
  is `DominantHomFlat.flat_of_isDominant`. Finite presentation follows from finite type over a
  noetherian target.
* `isMaximalSplitTorus_of_surjective`: let `G`, `H` be connected reductive and `π : G ⟶ H` a
  homomorphism that is finite on underlying schemes. Let `i : S ⟶ H` be a maximal split torus,
  `j : T ⟶ G` a split subtorus, and `f : T ⟶ S` surjective on underlying schemes with
  `j ≫ π = f ≫ i`. Then `j` is a maximal split torus of `G`. Suppose `j` factors as `a ≫ m`
  through a split subtorus `m : M ⟶ G`. The image `z : Z ⟶ H` of `m ≫ π` is a split subtorus
  (`IsSplitTorus.exists_dominant_factor_isSplitSubtorus`). It contains `i`, because `T ⟶ S` is
  schematically dominant (`exists_over_factor_of_schematic_precomp`). By maximality of `i`,
  the factorization `S ⟶ Z` is an isomorphism, so `m ≫ π` factors as `q ≫ i`. Then `q` is
  finite because `π` is finite and `i` is a closed immersion. Also `a ≫ q = f` is schematically
  dominant, and `M` is integral and affine. The previous lemma shows that the closed immersion
  `a` is an isomorphism.
* `exists_lift_of_kernel_pow_eq_one`: let `G`, `H` be connected reductive over `k`, and
  `π : G ⟶ H` a central isogeny (`IsCentralIsogeny π`). Let `i : S ⟶ H` be a maximal split
  torus, and `N > 0` with `x ^ N = 1` for every point `x : T ⟶ (kernel π).X` and every
  `T : Over (Spec k)`. Then there are a commutative group scheme `T`, a maximal split torus
  `j : T ⟶ G` and a homomorphism `f : T ⟶ S` with `j ≫ π = f ≫ i`, where `f` is flat,
  surjective and locally of finite presentation on underlying schemes. This is the conclusion
  of the target statement. The proof takes `Φ : S ⟶ G` with `Φ ≫ π = [2N] ≫ i`
  (`IsCentralIsogeny.exists_comp_eq_multiplication_comp`). It applies `exists_splitSubtorus_lift_of_surjective_splitParametrization`
  with `a = Φ` and `b = [2N]`, where `b` is surjective by
  `IsSplitTorus.flat_and_surjective_multiplication`. The last two lemmas then give flatness,
  finite presentation and maximality.
* `statement_of_kernel_exponent hexp : CentralIsogenyMaximalSplitTorusLiftStatement.{u}`. Here
  `hexp` says: for every field `k` in universe `u` and every central isogeny `π` of connected
  reductive groups over `k`, there is `N > 0` with `x ^ N = 1` for all points `x` of
  `kernel π`. The proof takes `N` from `hexp` and applies `exists_lift_of_kernel_pow_eq_one`.

## Provenance

`injective_of_integral_comp_injective` and
`isIso_of_closedImmersion_finite_comp_schematic` are reused from Worker 1482's
published `Langlands/GroupScheme/Torus/FiniteHomRigidity.lean`.
`exists_splitSubtorus_lift_of_surjective_splitParametrization` is reused from
Worker 1437's published `Langlands/GroupScheme/CentralIsogeny/SplitParametrization.lean`.
These three imported helpers live in namespace `Langlands.GroupScheme`.
The maximality argument of `isMaximalSplitTorus_of_surjective` is adapted from
Worker 1482's `Langlands/GroupScheme/Torus/FiniteHomMaximalityReduction.lean`,
with split tori in place of maximal tori.
