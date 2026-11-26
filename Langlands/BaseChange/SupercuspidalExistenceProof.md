# Proof of the existence of supercuspidal representations of `GL_n(F)`

Lean module: `Langlands.BaseChange.SupercuspidalExistenceProof`, namespace
`Langlands.BaseChange`.

`supercuspidalExistence : SupercuspidalExistenceStatement.{u, uV}` proves the published
statement of [SupercuspidalExistenceStatement](SupercuspidalExistenceStatement.md) with both
universe parameters free: for every nonarchimedean local field `F : Type u` (any
characteristic) and every `n > 0` there are a complex vector space `V : Type uV`, a
representation `π` of `GL_n(F)` on `V` and a character `χ` of the centre such that
`π.IsIrreducible`, `GeneralLinear.IsSupercuspidal π` and `HasCentralCharacterRep π χ`. The only
axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## The construction

Write `n = m + 1`, and let `𝒪`, `k` and `ϖ` be the valuation ring, residue field and a
uniformizer of `F`.

1. `GL_{m+1}(k)` has an irreducible cuspidal finite-dimensional representation `σ`
   (`FiniteGeneralLinear.exists_irreducible_cuspidal_fdRep`).
2. `σ` is inflated to `GL_{m+1}(𝒪)` through reduction modulo the maximal ideal and extended to
   `J = ϖ^ℤ GL_{m+1}(𝒪)` with `ϖ · 1` acting trivially (`LevelZero.inducingRep`).
3. The smooth induced representation `E` of this representation from `J` to `GL_{m+1}(F)` is
   admissible (`LevelZero.smoothInduced_isAdmissible`, by the Cartan decomposition and
   cuspidality).
4. The subrepresentation `A` of `E` spanned by the translates of the function supported on `J`
   with a nonzero value `v₀` at `1` is finitely generated. Its irreducible quotient `τ` is
   admissible, and its Jacquet coinvariants vanish for every conjugate of the unipotent radical of
   every proper standard block parabolic (`LevelZero.exists_irreducible_supercuspidal_smoothRep`,
   by the Iwasawa decomposition and cuspidality of `σ`).

## The proof of the statement

`supercuspidalExistence` writes `n = m + 1` and installs on `GL_{m+1}(F)` the Hausdorff,
locally compact, second countable, σ-compact and totally disconnected structures proved in
`Langlands.Group.GL.LocalFieldTopology`. Then:

- `LevelZero.exists_irreducible_supercuspidal_smoothRep F m` gives `τ` with carrier in
  `Type u`, irreducible, admissible and with vanishing Jacquet coinvariants.
- `exists_irreducible_smoothRep_equiv_of_separable` (the group being separable) gives an
  irreducible smooth `σ : SmoothRep.{0, u, uV}` with carrier in `Type uV` and an equivalence
  `e : τ.representation.Equiv σ.representation`.
- Admissibility passes along `e` (`isAdmissible_of_equiv`), and so does the vanishing of each
  Jacquet quotient (`Jacquet.coinvariants_subsingleton_iff`); together they are
  `GeneralLinear.IsSupercuspidal σ.representation`.
- The central character comes from Schur's lemma for irreducible smooth representations of
  σ-compact totally disconnected groups: the first part of `Renard.Smooth.centralCharacter`,
  applied to the centre, gives `χ` with `σ z v = χ z • v` for all central `z`, which is
  `HasCentralCharacterRep σ.representation χ`.

The witnesses are `V = σ` (its carrier), its additive group and complex module structures,
`π = σ.representation` and `χ`.

## Sources and route

The source result is Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), `bushnell-kutzko-1993-admissible-dual`, SHA256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`: Theorem (6.2.2), printed
p. 203 (PDF p. 215), applied to simple types of level zero (Chapter 5), for which `J = GL_N(𝔬_F)`
and `λ` is inflated from an irreducible cuspidal representation of `GL_N(k)`. The source shows
that the representation compactly induced from an extension of `λ` to `F^× J` is irreducible and
supercuspidal. The Lean proof follows a different route: it does not prove irreducibility of the
induced representation, but takes an irreducible quotient of a cyclic subrepresentation, and it
proves admissibility and the vanishing of the Jacquet quotients directly. The existence of the
cuspidal representation `σ` is derived from the Library's count of cuspidal classes of
`GL_n(k)` rather than from Green's character theory.
