# Multiplication in the full centralizer as a pullback

Let `S` be any base scheme, `j : H ⟶ G` a group-scheme homomorphism
whose underlying map over `S` is monic, `c : C ⟶ G` a supplied
representative of the full centralizer of `j`, and `z : Z ⟶ H` a
supplied closed representative of the full scheme-theoretic centre of `H`.
For any homomorphism `d : K ⟶ C`, the centre of `H` maps centrally into
`C`, and multiplication gives an actual homomorphism `Z × K ⟶ C`.
Its square with `Z × K ⟶ H × K`, ambient multiplication
`H × K ⟶ G` using `d ≫ c`, and `c` is a pullback.

`CentralizerProduct.centerMap` constructs the centre map by the existing
represented-subgroup factorization. `centerMap_comp` proves its compatibility
with the inclusions and `centerMap_isCentral` proves centrality in `C`.
`CentralizerProduct.hom` is the actual multiplication homomorphism.
`isPullback` proves the square is a pullback in schemes over `S`, and
`pullbackIso` constructs its actual isomorphism to the categorical pullback.
`fpqc` transfers flatness, surjectivity and quasi-compactness of the ambient
multiplication to this centralizer multiplication.

The proof uses all test schemes and all their refinements. A point of `H`
maps into its full centralizer if and only if it is in the full centre of `H`;
monicity of `j` gives the reverse implication. If `h k` belongs to `C`
and `k` already belongs to `C`, subgroup closure gives that `h` belongs
to `C`, hence is central in `H`. The centre representative then supplies
the unique first coordinate of the lift. Monicity of the centre and
centralizer inclusions proves the pullback equations and uniqueness.
The underlying scheme square is again a pullback, so the three geometric
properties pass by their published base-change stability.

This is internal support derived from the Library's full centre and
fixed-subgroup definitions, represented-subgroup factorization and categorical
pullbacks. Neither normality, a field, smoothness, connectedness, perfectness
nor any reductive generation theorem is assumed. Existence of the supplied
representatives and fpqc ambient multiplication remain explicit obligations.

Authorship: Worker 1616.
