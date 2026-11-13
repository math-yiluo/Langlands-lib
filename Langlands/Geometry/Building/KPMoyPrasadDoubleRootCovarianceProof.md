# Proof: double-root Moy–Prasad covariance (KP Proposition 13.2.5(1), (2))

The theorem `Langlands.Geometry.Building.moyPrasadDoubleRootCovariance` proves the published
proposition `MoyPrasadDoubleRootCovarianceStatement.{u}` (module
`Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement`) at an arbitrary universe `u`.

## Statement proved

Take a nonarchimedean local field `F`, a group scheme `G` over `F` with `IsAffineHom G.X.hom`,
supplied `P : ParahoricBuildingData G` and `Zf : P.CentralizerFiltration`. Assume
`P.SatisfiesApartmentAxioms`, `Zf.SatisfiesFiltrationAxioms` and
`Zf.IsDoubleRootCommutatorFriendly`. Then for every point `y` of the reduced building and every
`r : ℝ≥0`, any two subgroups `Q`, `Q'` of `G(F)` with `Zf.IsMoyPrasadAt y r Q` and
`Zf.IsMoyPrasadAt y r Q'` are equal. Here `Zf.IsMoyPrasadAt y r Q` means that
`Q = g P_{x,r} g⁻¹` for some `g ∈ G(F)` and some apartment point `x` with `g · x = y`. This is
the well-definedness of `P_{y,r}` for points of the reduced building, i.e. Kaletha–Prasad,
Proposition 13.2.5(1) and (2), for supplied data with the double-root premise.

## Implemented proof

The proof introduces the quantified data and hypotheses and applies one published Library
theorem:

- `Langlands.Geometry.Building.ParahoricBuildingData.CentralizerFiltration.isMoyPrasadAt_unique_of_doubleRootCommutatorFriendly`
  (module `Langlands.Geometry.Building.MoyPrasadDoubleRootConjugation`). Its hypotheses are
  `hP : P.SatisfiesApartmentAxioms`, `hZ : Zf.SatisfiesFiltrationAxioms`,
  `hZ2 : Zf.IsDoubleRootCommutatorFriendly`, a point `y`, a depth `r`, subgroups `Q`, `Q'`
  and the two presentations `Zf.IsMoyPrasadAt y r Q`, `Zf.IsMoyPrasadAt y r Q'`; its
  conclusion is `Q = Q'`.

The statement's hypotheses are passed to it unchanged, so the theorem's type is exactly the
target proposition.

## Route of the cited theorem

For orientation only; this module adds no argument of its own. According to the Lean source
and Markdown of the cited modules, the theorem above is assembled as follows.

1. `double_opposite_central_mem_of_doubleRootCommutatorFriendly`
   (`MoyPrasadDoubleRootConjugation`): for roots `a`, `2a`, a depth `r > 0`,
   `u ∈ U_{a,x,0}` and `v ∈ U_{-2a,x,r}`, every decomposition `u v = v' j(z) u'` with
   `v' ∈ U_{-a}(F)`, `u' ∈ U_a(F)` has `z ∈ Z(F)_r`. If `u = 1` or `v = 1`, injectivity of the
   product `U_{-a} × Z × U_a → G` (`oppositeRootTripleProduct_injective`) and monicity of the
   centralizer inclusion give `z = 1`. Otherwise axiom V 4 (`filtration_double_le_half`) puts
   `v` in `U_{-a,x,r/2}`, so `t = x_a(u) ≥ 0` and `s = x_{-a}(v) ≥ r/2`. Rewriting
   `v⁻¹ u v u⁻¹ = (v⁻¹ v') j(z) (u' u⁻¹)`, the premise `IsDoubleRootCommutatorFriendly`
   (applied with `u' := v ∈ U_{-2a}(F)` and depth `t + s > 0`) puts `z` in `Z(F)_{2(t+s)}`,
   and since `2(t+s) ≥ r` the filtration's antitonicity gives `z ∈ Z(F)_r`.
2. `conjugate_double_opposite_mem_moyPrasad_of_doubleRootCommutatorFriendly` feeds this bound to
   `conjugate_double_opposite_mem_moyPrasad_of_central_bound`
   (`MoyPrasadMixedConjugation`), giving `u v u⁻¹ ∈ P_{x,r}` for those `u`, `v`.
3. `sharpFixer_le_normalizer_moyPrasad_of_doubleRootCommutatorFriendly` passes this mixed bound
   to `sharpFixer_le_normalizer_moyPrasad_of_double_opposite_bound`
   (`MoyPrasadCovarianceReduction`), which treats depth zero and all other root pairs, and
   concludes that the sharp fixer of every apartment point `x` normalizes every `P_{x,r}`.
   It uses the components `IsCommutatorFriendly` and `IsRootCompatible` of
   `SatisfiesFiltrationAxioms`.
4. `isMoyPrasadAt_unique_of_sharp_normalization` (`MoyPrasadCovarianceReduction`) compares two
   presentations `(g, x)`, `(h, x')` of `y`: equality of their classes in the apartment
   quotient (`ApartmentQuotient.mk_eq_mk_iff`) yields `n ∈ N(F)` with `n · x = x'` and
   `g⁻¹ h n` in the sharp fixer of `x`. Normalizer stability (`IsNormalizerStable`, a
   component of `SatisfiesFiltrationAxioms`, via `moyPrasad_map_conj_normalizer` in
   `MoyPrasadNormalizerCovariance`) transports `P_{x',r}` to `P_{x,r}` under conjugation by
   `n⁻¹`, and step 3 shows that `g⁻¹ h n` normalizes `P_{x,r}`, so the two conjugates agree.

## Scope

The building data and the filtration of `Z(F)` are supplied, exactly as in the statement; this
proof constructs neither, and it does not prove that a filtration with the double-root property
exists (`CentralizerFiltrationDoubleRootExistenceStatement`). No hypothesis is added to the
statement and no unproved proposition is assumed. The inspected axioms are `propext`,
`Classical.choice` and `Quot.sound`.
