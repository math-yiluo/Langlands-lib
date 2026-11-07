# Renard VI.8.4 from uniform detection and a global coefficient family

Worker 452. This module is an internal step of the proof of Renard,
*Représentations des groupes réductifs p-adiques* (9 July 2026), VI.8.4
Proposition, printed pp. 192–193, PDF pp. 198–199. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard's proof picks one compact open subgroup `K` that detects every
irreducible subquotient of every induced twist. It then works with the
finite free module of `K`-fixed vectors of the algebraic family and a local
determinant. This module combines that detection with a global coefficient
family. It is stated for the actual data of the closed proposition
`InducedIrreducibilityOpenStatement`.

`exists_principal_neighborhood_of_detection` assumes the statement
`InducedTwistsUniformDetectionStatement.{u, v}`. It then takes the same
binders as `InducedIrreducibilityOpenStatement`: a nonarchimedean local field
`k`, a connected reductive group `G` over `k`, a parabolic subgroup `P` with
rational Levi subgroup `M` and unipotent radical `U`, and an irreducible
smooth complex representation `ρ` of `M(k)`. Both groups of rational points
carry the same topologies and instances as in that statement. The statement
also records that the scheme of `M` is affine and that `M` is locally of
finite type. Both are proof-valued instances derived from `hl`, so they do
not weaken the conclusion. It also takes:

- A complex algebra `B` and an algebra equivalence `e` from `B` to the actual
  regular functions on the unramified characters of `M`, defined by the
  rational norm characters of `M`.
- A smooth representation `A` of `G(k)` with compatible `B`-coefficients.
- A proof of `IsGlobalCoefficientFamily A M e D`, from
  `GlobalCompressionPrincipalOpen`. Here `D ψ` is the normalized parabolic
  induction of the twist `ρ ⊗ ψ`. So for every compact open subgroup `K` of
  `G(k)`, the `K`-fixed vectors of `A` form a free and finitely generated
  `B`-module. Also, for every unramified character `ψ`, `A` specializes fully
  to `D ψ` at the character `coefficientCharacter M e ψ` of `B`.

If the induction of `ρ ⊗ ψ₀` is irreducible, the theorem gives a polynomial
`f` in the published canonical coordinates of the unramified characters. The
principal open set
`rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f` contains `ψ₀`,
and the induction of `ρ ⊗ ψ` is irreducible for every `ψ` in it. This is
exactly the conclusion of `InducedIrreducibilityOpenStatement` for this `ρ`
and `ψ₀`.

The proof first restores the instances of the target statement in the local
context. They are the affine and locally-of-finite-type structure of `M`, and
the topologies on `G(k)` and `M(k)`. It applies the detection statement to
`ρ` to obtain a compact open subgroup `K` of `G(k)` and the detection
property for all twists. The proof then applies
`exists_polynomial_principal_neighborhood_of_family`, taking the family of
induced twists as `D`.

All universes are independent. The detection statement, the coefficient
family, its fixed-vector freeness and finiteness, and full specialization
remain explicit inputs. This module neither proves the detection statement
nor constructs the actual universal induced family. It does not prove the
closed `InducedIrreducibilityOpenStatement`.
