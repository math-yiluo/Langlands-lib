# Jacquet nonvanishing for split types of level `(0, 0)`

Module `Langlands.BushnellKutzko.SplitTypeJacquet.LevelZeroCase`.

`HasProperJacquetModule ρ`, for a complex representation `ρ` of `GL_n(F)`, says that there are a
block shape `B` with `B.parabolic F ≠ ⊤` and `g ∈ GL_n(F)` such that
`Jacquet.Coinvariants ρ (B.conjugateUnipotent g)` is not a subsingleton. This is the conclusion of
`Langlands.BushnellKutzko.ZeroSecondLevelSplitTypeJacquetStatement`.

`levelZeroSplitType_jacquet`: let `F` be a nonarchimedean local field, `n > 0`, `π` an admissible
smooth complex representation of `GL_n(F)`, and `(K, ρ)` a smooth representation of a subgroup
such that `glRepresentationToAut ρ` is a split type of level `(0, 0)` (`IsLevelZeroSplitType`). If
`π` contains `ρ` (`ContainsType π ρ`), then `HasProperJacquetModule π.representation`.
Irreducibility of `π` is not used.

Proof. The split type gives a lattice chain `L`, cuspidal layer data `a` with two different
factor classes, and an isomorphism of `(glSubgroupToAut K, glRepresentationToAut ρ)` with the
inflation of the layer factors to `U(𝔄)`. Let `g₀ = layerChange a`. For `x` in
`J0 F (blkOf (layerShape a))`, the unit group of the standard order, `g₀ x g₀⁻¹ ∈ K`. The
containment map precomposed with the inverse of the isomorphism of pairs, and then with the
inverse of `layerTensorEquiv a`, is a nonzero intertwiner from `stdType (layerDatum a)` into
`π ∘ Ad(g₀)` (`toLin_layerChange_conj`, `layerTensorEquiv_inflation`). The representation
`π ∘ Ad(g₀)` is admissible (`isAdmissible_comp_continuousMulEquiv` with `conjContinuous g₀`).
`standard_jacquet` then gives `B` and `g` with a nonzero Jacquet module of `π ∘ Ad(g₀)` along
`B.conjugateUnipotent g`. Its relations are those of `π` along `B.conjugateUnipotent (g₀ g)`
(`relations_comp_conj`, `conjugateUnipotent_map_conj`), so `π` has a nonzero Jacquet module
along `B.conjugateUnipotent (g₀ g)` (`subsingleton_coinvariants_iff`).

This proves, at level `(0, 0)` and for admissible smooth representations, the existential Jacquet
nonvanishing consequence of C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.3.3), printed p. 291 (PDF p. 303): some conjugate of the
unipotent radical of some proper block parabolic has a nonzero Jacquet module. The theorem of the
source says more. It takes a parabolic subgroup `P` subordinate to the given order and minimal for
this property (setup on printed p. 290, PDF p. 302) and shows that the Jacquet module along the
unipotent radical of `P` contains the Levi representation `ϑ_U`. Neither statement is proved here.
Split types of level `(0, 0)` are those of (8.1.2), printed p. 267 (PDF p. 279). The route differs
from the source. The cuspidal factors are reordered inside `GL_n(k_F)` by the Harish–Chandra
multiplicity formula, in place of the associated split types and covers of (8.3.4)–(8.3.9).
Compression by the contraction `diag(ϖ, 1)` along a coarse two-block parabolic is then injective
by a finite Mackey argument.
