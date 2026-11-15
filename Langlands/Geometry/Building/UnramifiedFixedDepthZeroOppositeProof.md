# Proof of depth-zero opposite factors at the Galois-fixed points

`Langlands.Geometry.Building.unramifiedFixedDepthZeroOpposite` proves the
published statement
`Langlands.Geometry.Building.UnramifiedFixedDepthZeroOppositeStatement.{u}` at
an arbitrary universe `u`, with its hypotheses unchanged. This is the
restricted form of KP Proposition 9.4.9(2) (Kaletha–Prasad 2023, printed
p. 349, PDF p. 380). Fix a nonarchimedean local field `F`,
`K = inertiaFixedField F`, and the data of the statement: a maximal split torus
`iS : S → G`, the torus `T ⊇ S` with `T_K` maximal split, opposite factor pairs
`hE`, an apartment class `D` with V 6 for a centralizer datum `C`. Let `z` be
an `Aut(K/F)`-fixed apartment point, `a` a relative root, and `g ∈ U_a(F)` with
`g ≠ 1` and restricted value `φ z a g = 0`. Then for all `g', g'' ∈ U_{-a}(F)`
with `g' g g'' ∈ N_G(S)(F)`, the restricted values `φ z (-a) g'` and
`φ z (-a) g''` are nonnegative.

The proof is a one-line application of three Library results:

1. `unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels` (module
   `UnramifiedRecoveredDepthZeroOpposite`) proves
   `UnramifiedRecoveredDepthZeroOppositeReductionStatement`: the
   recovered-model statement `UnramifiedFixedRecoveredParabolicModelsStatement`
   and the integral opposite-factor statement `IntegralOppositeFactorsStatement`
   together imply the exact target. That reduction builds the closed integral
   torus and the actual reductive quotient of the special fibre at `z`. It shows
   that a value-zero root point does not reduce into the unipotent radical, and
   applies integral opposite factors.
2. `unramifiedFixedRecoveredParabolicModels` (module
   `UnramifiedNearbyParabolicComparisons`, submitted with this proof) proves the
   recovered-model statement without premises. It supplies the recovered
   singleton models at every fixed point, together with parabolic comparison
   images and exact reduction preimages along nearby descended translates.
3. `Langlands.BruhatTits.IntegralModels.integralOppositeFactors` (module
   `IntegralOppositeFactorsProof`) proves `IntegralOppositeFactorsStatement`.

Hence `unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels
unramifiedFixedRecoveredParabolicModels integralOppositeFactors` has exactly
the target type.

The implemented route differs from KP's proof of Proposition 9.4.9 and
Theorem 8.2.9. KP use the Bruhat–Tits group scheme `G^0_z`, the rank-one
Bruhat decomposition and a Weyl-element lift. Here the special-fibre argument
is carried by the actual recovered component models, the parabolicity and
exact preimage of their nearby comparison images (KP Axiom 4.1.22(2),(4)), and
the proved integral opposite-factor theorem. No premise, unproved proposition
or new axiom is added. Compilation reports only `propext`, `Classical.choice`
and `Quot.sound`.
