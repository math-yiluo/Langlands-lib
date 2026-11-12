# Maximal compactness of the actual integral-point image

Authors: Worker 4686 (this module), Worker 5139 (the Levi-side modules listed
below).

This module proves the published proposition
`Langlands.GroupScheme.IntegralModel.MaximalCompactStatement` (module
`MaximalCompactStatement.lean`) at every universe `u`, without extra hypotheses.

## Target

`MaximalCompactStatement.{u}` is the final assertion of Getz–Hahn Theorem 2.4.3.
For every universe-`u` field `F` with `[ValuativeRel F]`, `[TopologicalSpace F]`
and `[IsNonarchimedeanLocalField F]`, every group scheme `G` over `Spec F` with
`IsConnectedReductive G`, and every supplied `M : IntegralModel 𝒪[F] F G` whose
special-fibre pullback `(GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj
M.group` is connected reductive: with the affine instance from `hG.isAffineHom`
and `rationalPointTopology F G.X` on `rationalPoints G`, the subgroup
`M.integralPoints` is compact, and every compact subgroup `L` of `G(F)` with
`M.integralPoints ≤ L` equals `M.integralPoints`.

## Declarations

* `leviMaximalCocharacter : LeviMaximalCocharacterStatement.{u}`. It applies
  `leviMaximalCocharacterStatement_of_isOpen` (module `LeviMaximalCocharacter`) to
  the published `isOpen_integralPoints_localField` (module
  `LocalIntegralSeparation`): for every local field `F`, every `G` over `Spec F`
  with affine underlying scheme and every `M : IntegralModel 𝒪[F] F G`,
  `M.integralPoints` is open in `G(F)`. This is exactly the openness hypothesis of
  `leviMaximalCocharacterStatement_of_isOpen`.
* `maximalCompactStatement : MaximalCompactStatement.{u}`. It applies the published
  `maximalCompactStatement_of_integralDiagonalRepresentation` (module
  `IwasawaCellLinear`) to the published `integralDiagonalRepresentation :
  IntegralDiagonalRepresentationStatement.{u}` (module
  `IntegralDiagonalRepresentation`) and to `leviMaximalCocharacter`.

Both proofs are single term applications; the theorem's type is literally
`MaximalCompactStatement.{u}`.

## The proof route

The route is Maculan's algebraic proof (Marco Maculan, *Maximality of hyperspecial
compact subgroups avoiding Bruhat–Tits theory*, Ann. Inst. Fourier 67(1) (2017),
registered as `maculan-2017-hyperspecial-maximality`), adapted to the Library's
supplied integral models. The pieces are:

1. `IwasawaCellReduction` (published): maximal compactness from opposite Iwasawa
   coverings `G(F) = P(F)·M(𝒪) = P⁻(F)·M(𝒪)`, integrality on opposite cells, and
   Levi maximality. Compactness of `M.integralPoints` is the published
   `isCompact_integralPoints_localField`.
2. `IwasawaCellDynamic` (published): the Iwasawa coverings for the dynamic
   parabolics of a model cocharacter `χ`, reducing the target to
   `DynamicCellIntegralityStatement` and `LeviMaximalCocharacterStatement`.
3. `IwasawaCellLinear` (published): cell integrality from
   `IntegralDiagonalRepresentationStatement`, a faithful integral matrix
   representation diagonalizing `χ`.
4. `IntegralDiagonalRepresentation` (published): proof of that statement, from
   integral matrix coefficients of the model over the principal ideal domain `𝒪[F]`
   and simultaneous diagonalization of a cocharacter of `GL_N` over `𝒪[F]`.
5. The Levi side, added with this module:
   * `UnramifiedTorusPowerIntegrality`: every element of a compact subgroup of a
     topological group has a positive power in a given open subgroup, and a point
     on a closed split torus of the model over the maximal unramified integers is
     integral when a positive power of it is.
   * `TorusModelPowerIntegrality`: for a model with connected reductive generic
     group and torus special fibre, a point with an integral positive power is
     integral (a power form of Maculan, Proposition 4.6).
   * `Torus/HenselianCocharacterLifting`: over a Henselian local ring, a
     cocharacter of a closed split torus of the closed fibre lifts to the group, up
     to an automorphism of the closed fibre.
   * `DynamicCentralizer`: the integral dynamic centralizer of a model cocharacter
     as an `IntegralModel` of the generic centralizer, reflection of integral points
     through closed model morphisms, and Levi maximality when the special fibre of
     that centralizer is a torus and integral points are open: an element of a
     compact subgroup of the centralizer's rational points has an integral power,
     hence is integral in the centralizer model, hence in `M`.
   * `LeviMaximalCocharacter`: a model cocharacter with torus special centralizer
     (finite-field quasi-splitness, a maximal split torus with torus centralizer, a
     centralizing cocharacter, Henselian lifting), and
     `leviMaximalCocharacterStatement_of_isOpen`.

Each of these modules has its own Markdown describing its statements and proofs.
The final module adds no definitions and uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
