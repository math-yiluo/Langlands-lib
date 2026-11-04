# Maximal split tori lift under central isogenies

Module `Langlands.GroupScheme.CentralIsogeny.MaximalSplitTorusLiftProof`.

`Langlands.GroupScheme.centralIsogenyMaximalSplitTorusLift` proves
`Langlands.GroupScheme.CentralIsogenyMaximalSplitTorusLiftStatement.{u}`. Let `k` be a field,
`π : G ⟶ H` a central isogeny of connected reductive group schemes over `k`, and `i : S ⟶ H` a
maximal split torus. Then there are a commutative group scheme `T`, a maximal split torus
`j : T ⟶ G` and a homomorphism `f : T ⟶ S` with `j ≫ π = f ≫ i`. On underlying schemes, `f` is
flat, surjective and locally of finite presentation.

## Proof

The proof combines two results.

1. `IsCentralIsogeny.exists_pow_eq_one_kernel` (module
   `Langlands.GroupScheme.CentralIsogeny.KernelTorsion`, contributed by Worker 1384). For a
   central isogeny `π` over a field, there is `N > 0` with `x ^ N = 1` for every point `x` of
   `kernel π`.
2. `CentralSplitTorusLift.statement_of_kernel_exponent` (module
   `Langlands.GroupScheme.CentralIsogeny.MaximalSplitTorusLift`). It derives the target statement
   from such an exponent. With `N` given, it builds `Φ : S ⟶ G` with `Φ ≫ π = [2N] ≫ i` (module
   `Langlands.GroupScheme.CentralIsogeny.PowerLift`). `[2N]` is surjective on the split torus `S`
   (module `Langlands.GroupScheme.Torus.SplitMultiplication`). The closed image `T` of `Φ` is a
   split subtorus of `G`, and `j ≫ π` factors through `i` as a surjective `f`. Flatness of `f`
   follows from dominance onto an integral noetherian target, and finite presentation from finite
   type. Maximality of `T` follows from maximality of `S` and finiteness of `π`.

The Markdown files of these modules describe each step in detail.
