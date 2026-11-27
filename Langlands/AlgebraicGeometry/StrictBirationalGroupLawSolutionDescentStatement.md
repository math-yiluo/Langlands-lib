# Descent of solutions of strict birational group laws from strictly henselian bases

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawSolutionDescentStatement`
states the descent step of Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), §6.5
Corollary 2 and its proof, printed pp. 157–158 (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`, file SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is
PDF page `p + 7`), as an implication between two propositions of the Library. The module
states a proposition and proves nothing.

## The proposition

`StrictBirationalGroupLawSolutionDescentStatement.{u}` is the implication

`StrictBirationalGroupLawHenselianSolutionStatement.{u} → StrictBirationalGroupLawSolutionStatement.{u}`.

- The hypothesis (module
  `Langlands.AlgebraicGeometry.StrictBirationalGroupLawHenselianSolutionStatement`, BLR 5.2/3
  over a strictly henselian discrete valuation ring) says: over every discrete valuation ring
  in universe `u` which is Henselian with separably closed residue field, every birational
  group law on a smooth, separated, faithfully flat scheme of finite type which restricts to a
  strict law on an `R`-dense open `X'` has a solution with domain `X'`.
- The conclusion (module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawSolutionStatement`,
  BLR 6.5/2) says the same over every discrete valuation ring in universe `u`.

## Correspondence with the source

BLR deduce 6.5/2 from 5.2/3 as follows (printed pp. 157–158). Let `R'` be a strict
henselization of `R`. The base change of the strict law to `R'` is strict and has a solution
`U' ↪ G'` by 5.2/3. Over `R'' = R' ⊗_R R'` the uniqueness of solutions (5.1/3) extends the
canonical descent datum of `U' = U ⊗_R R'` to a descent datum on `G'` compatible with the
group structure, satisfying the cocycle condition. Theorem 6.5/1 (printed p. 157: for a
faithfully flat extension `R → R'` of discrete valuation rings, a smooth separated
`R'`-group scheme of finite type with a descent datum compatible with the group law descends
to an `R`-group scheme) then descends `G'` to the required group scheme over `R`.

The proposition records exactly this deduction: the strictly henselian case of the
statement implies the general case, in a fixed universe `u`. It does not prescribe the
extension used. Any faithfully flat extension of `R` by a strictly henselian discrete
valuation ring in universe `u` serves for BLR's argument, because BLR's Theorem 6.5/1 applies
to every faithfully flat extension of discrete valuation rings. The Library's
`Langlands.CommutativeAlgebra.StrictHenselianDvrExtensionStatement` asserts that such an
extension exists in the same universe, and `Langlands.CommutativeAlgebra.strictHenselianDvrExtension`
proves it.
