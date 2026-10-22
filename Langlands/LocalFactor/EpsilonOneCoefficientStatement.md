# Tate's `ε₁` over coefficient fields of characteristic zero

Worker 33 wrote this module for task `e534647a`. It covers Tate 1979, the
paragraph after (3.6.11), in the nonarchimedean case. Here Tate extends the
local constant `ε₁(V, ψ)` of (3.6.10) from complex coefficients to every
coefficient field of characteristic 0. The main declaration is
`Langlands.LocalFactor.EpsilonOneCoefficientStatement`. It is a proposition
only. No coefficient-field `ε₁` and no local-constant system is constructed
or chosen, nothing is proved, and nothing is assumed as an axiom.

## The source

Tate, printed p.18:

> Thus in the nonarchimedean case we can define, for `V` and `ψ` over any
> field `E` of characteristic 0 (an open subgroup of `I` acting trivially on
> `V`, and `ψ` trivial on some `π^n O`), an `ε₁(V, ψ) ∈ E*`, in a unique way
> such that `ε₁(V^α, ψ^α) = ε₁(V, ψ)^α` for any homomorphism `α: E → E'` and
> such that `ε₁` is the old `ε₁`, given by (3.6.10), when `E = ℂ`. So defined,
> `ε₁(V_E, ψ · Tr_(E/F))` is inductive in degree 0 (2.3.2) for every field of
> scalars `E` of characteristic 0, and `ε₁(V, ψ)` will be given by (3.6.11) if
> `V` corresponds to a quasi-character `χ: F* → E*`.

Tate prints the coefficient field as a boldface `E`, and the finite extension
`E` of `F` in `V_E` and `Tr_(E/F)` in italics. In this module the coefficient
field is `K`, and `E`, `L` are finite intermediate extensions of the
algebraic closure of `F`. The old `ε₁` of (3.6.10) is `ε_D(V, ψ, dx₁)`,
where `dx₁` gives the ring of integers volume one.

## Objects

From the published Library:

- `CommonClosure`: the finite intermediate extensions `E : Extension F` of
  the algebraic closure of a p-adic field `F`, their Weil subgroups `W_E`
  (`weilSubgroup F E`), the canonical local-field data `fieldData F E`, the
  complex additive characters (`AdditiveCharacter F E`, with values
  `ψ.complex`) and Haar measures (`HaarMeasure F E`) of `E`, the rebracketing
  `nestedWeilEquiv` of `W_L` as a subgroup of `W_E` for `E ⊆ L`, reciprocity
  families `e` with components `reciprocityUnits F e E : W_E → Eˣ`, and the
  class `ExactGrothendieckGroup.ofRepresentation (ContinuousPredicate F E) ⟨A, hA⟩`
  of a genuine continuous complex representation in the exact virtual group.
- From `fieldData F E`: `additiveLattice n`, the fractional ideal
  `π^(-n) O`; `principalUnits m`, the unit level `U^m` (so `U^0 = Oˣ`); `ord`,
  the normalized valuation; `residueCardinality = q`; and `integerVolume μ`,
  the volume `μ(O)`.
- `CommonClosureWeilDeligne.inertia F E`: the inertia subgroup of `W_E`, the
  kernel of the degree map.
- `NonabelianSystem`: complex-valued assignments `ε_E(x, ψ, μ)` and the system
  property `IsSystem F e ε`: normalized reciprocity, additivity, Haar
  scaling, degree-zero induction with arbitrary Haar measures, and rank-one
  agreement with the abelian constant through `reciprocityUnits`.
- `FiniteRepresentation K G`: finite-dimensional representations of `G` over
  any field `K` on an actual carrier space, with `rank`, `restrict`, the
  finite-index induction `induce`, and `IsShortExact` for a pair of
  intertwiners. `IsContinuous` is continuity of a complex representation.
- `EpsilonOne.UnitQuotient (fieldData F E) a`, from
  `Langlands.LocalFactor.EpsilonOneStatement`: the quotient
  `U^0 / U^a = Oˣ / U^a`, the index set `Oˣ mod π^a` of the sum in (3.6.11).

The new declarations, in the namespace
`Langlands.LocalFactor.EpsilonOneCoefficient`, are:

- `IsConjugate α A B`, for a field homomorphism `α : K → K'`: some
  `α`-semilinear map `f : A → B` (`f(z v) = α(z) f(v)`) intertwines the
  actions and maps a basis of `A` onto a basis of `B`. This says that `B` is
  isomorphic to `K' ⊗_(α, K) A`, Tate's `V^α`.
- `TrivialOnOpenInertia A`: some open subgroup of the inertia subgroup of
  `W_E` acts trivially on `A`. This is Tate's condition on `V`.
- `IsAdmissibleCharacter ψ`, for an additive character `ψ : E → K`: `ψ` is
  nontrivial and trivial on some `π^(-n) O`. This is Tate's condition on `ψ`.
- `AdditiveConductorAt ψ n`: `n` is the largest integer with `ψ` trivial on
  `π^(-n) O`. This is Tate's `n(ψ)` for `K`-valued characters.
- `ConductorAt χ a`, for a character `χ : Eˣ → Kˣ`: `a` is the least natural
  number with `χ` trivial on `U^a`. This is Tate's `a(χ)`.
- `IsCharacterLine e χ A`: `A` has rank one and `g ∈ W_E` acts on it by the
  scalar `χ(rec_E(g))`, where `rec_E = reciprocityUnits F e E`. This is the
  representation corresponding to `χ`, with the same reciprocity components
  as the rank-one law of `IsSystem`.
- `induced F E L h A`, for `E ⊆ L` and a representation `A` of `W_L` over
  `K`: restriction along `nestedWeilEquiv`, followed by `induce` from `W_L`
  to `W_E`. This is the construction of `CommonClosure.inducedRepresentation`
  over `K`, without a continuity certificate.
- `traceAddChar F E L h ψ = ψ ∘ Tr_(L/E)`, the `K`-valued character of `L`.
- `Assignment F`: a function `ε₁(E, K, ψ, A) ∈ Kˣ` for every intermediate
  field `E`, every field `K` of characteristic 0 in the universe `uK`, every
  additive character `ψ : E → K`, and every representation `A` of `W_E` over
  `K` with carrier in the universe `max uF uK`. Values on inputs that violate
  Tate's conditions are not constrained by any clause.

## The statement

`EpsilonOneCoefficientStatement` says: for every prime `p`, every p-adic
field `F`, every reciprocity family `e`, and every assignment `ε` with
`IsSystem F e ε`,

1. **Existence.** Some `ε₁ : Assignment F` satisfies `Compatible F ε₁` and
   `Normalized F ε ε₁`.
2. **Uniqueness.** Any two assignments that both satisfy `Compatible` and
   `Normalized` agree on every input with `ψ` admissible and `A` trivial on an
   open subgroup of inertia (`AgreeOnAdmissible`).
3. **Properties.** Every assignment `ε₁` satisfying `Compatible` and
   `Normalized` satisfies `Additive`, `InductiveInDegreeZero` and
   `RankOneFormula F e`.

The predicates are:

- `Compatible F ε₁` (`ε₁(V^α, ψ^α) = ε₁(V, ψ)^α`). For every intermediate
  field `E`, every homomorphism `α : K → K'` of fields of characteristic 0,
  every admissible `ψ : E → K`, every representation `A` over `K` trivial on
  an open subgroup of inertia, and every `B` over `K'` with
  `IsConjugate α A B`: `ε₁(E, K', α ∘ ψ, B) = α(ε₁(E, K, ψ, A))`.
- `Normalized F ε ε₁` (the old `ε₁` when the coefficients are `ℂ`). For every
  intermediate field `E`, every field `K` with a ring isomorphism
  `κ : K ≃ ℂ`, every admissible `ψ : E → K`, every `A` over `K` trivial on an
  open subgroup of inertia, every complex additive character `ψ'` with
  `ψ'(y) = κ(ψ(y))` for all `y`, every Haar measure `μ` with `μ(O_E) = 1`, and
  every continuous complex representation `A'` with `IsConjugate κ A A'`:
  `κ(ε₁(E, K, ψ, A)) = ε_E([A'], ψ', μ)`.
- `Additive F ε₁` (Tate (2.3.2), additivity over `K`). For every
  intermediate field `E`, field `K` of characteristic 0, admissible
  `ψ : E → K`, and intertwiners `f : A → B`, `g : B → C` of representations
  over `K` that are trivial on open subgroups of inertia and form a short
  exact sequence `0 → A → B → C → 0`:
  `ε₁(E, K, ψ, B) = ε₁(E, K, ψ, A) · ε₁(E, K, ψ, C)`.
- `InductiveInDegreeZero F ε₁` (Tate (2.3.2), inductivity in degree 0 over
  `K`). For all intermediate fields `E ⊆ L`, every field `K` of
  characteristic 0, every admissible `ψ : E → K`, and every pair `A, B` of
  representations of `W_L` over `K` that are trivial on open subgroups of
  inertia and have `rank A = rank B`:

  `ε₁(E, K, ψ, Ind A) · ε₁(E, K, ψ, Ind B)⁻¹ = ε₁(L, K, ψ ∘ Tr_(L/E), A) · ε₁(L, K, ψ ∘ Tr_(L/E), B)⁻¹`,

  where `Ind = induced F E L h`.
- `RankOneFormula F e ε₁` (Tate (3.6.11) over `K`). For every intermediate
  field `E`, field `K` of characteristic 0, character `χ : Eˣ → Kˣ`,
  admissible `ψ : E → K`, integer `n` and natural number `a` with
  `AdditiveConductorAt ψ n` and `ConductorAt χ a`, and every `A` with
  `IsCharacterLine e χ A`: for every `c ∈ Eˣ` with `ord c = n + a` and every
  map `r : Oˣ/U^a → Oˣ` sending each class to a representative of it,

  `ε₁(E, K, ψ, A) = χ(c) · q^n · ∑_(x ∈ Oˣ/U^a) χ(r x)⁻¹ · ψ(r x / c)`.

  The sum is a `finsum` over the finite quotient, and `q^n` is an integer
  power in `K`.

### Design choices

- **The coefficient fields.** The coefficient fields are all fields `K` of
  characteristic 0 in one universe `uK`. The field `ℂ` itself lies in the
  lowest universe, so "`K = ℂ`" is expressed through a ring isomorphism
  `κ : K ≃ ℂ`, required for every such `κ`. This loses nothing: two choices of
  `κ` differ by an automorphism of `ℂ`, and the old `ε₁` is equivariant for
  every automorphism of `ℂ` by (3.6.10). Representations over `K` have
  carriers in the universe `max uF uK`. Induction from a subgroup of `W_E`
  keeps carriers in this universe.
- **Conjugates are described by relations.** The Library has no
  construction of `K' ⊗_(α, K) V`. `IsConjugate` describes it instead: an
  `α`-semilinear intertwiner that maps a basis to a basis.
  `Langlands.LocalFactor.EpsilonOne.GaloisEquivarianceStatement` asks
  instead for an `α`-semilinear bijection, which is right when `α` is an
  automorphism of `ℂ`. When `α` is not onto and `A` is nonzero, the
  conjugate `K' ⊗_(α, K) A` admits no `α`-semilinear bijection from `A`:
  over the subfield `α(K)` its dimension is `dim A · [K' : α(K)]`, which is
  larger than `dim A`. The basis condition describes `K' ⊗_(α, K) A` for
  every `α`, onto or not. It also covers zero representations: if `A` is
  zero, the bases are empty, `B` is zero, and the unique map `A → B` is an
  `α`-semilinear bijection. When `α` is onto, the basis condition is
  equivalent to bijectivity. The conjugate character `ψ^α = α ∘ ψ` is built
  directly. Conjugates always exist, so nothing is lost: `K' ⊗_(α, K) A`
  with `v ↦ 1 ⊗ v` satisfies `IsConjugate α A _`.
- **Tate's conditions on the source only.** `Compatible` and `Normalized`
  assume Tate's conditions on `ψ` and `A` only. The conjugates satisfy them
  automatically: `α ∘ ψ` is nontrivial and trivial on the same lattice, and
  a conjugate has the same kernel. The complex objects `ψ'` and `A'` in
  `Normalized` always exist. The values of `ψ` are `p`-power roots of unity,
  so `κ ∘ ψ` is unitary and, being trivial on an open lattice, continuous.
  `A'` has open kernel on the open profinite inertia subgroup, so it is
  locally constant and hence continuous.
- **Uniqueness on admissible inputs.** Tate's uniqueness concerns inputs
  satisfying his conditions. Values elsewhere are arbitrary, so clause 2 is
  stated with `AgreeOnAdmissible` rather than equality of functions.
- **Additivity.** In (2.3.2), "inductive in degree 0" presupposes "additive
  over `F`": multiplicativity on short exact sequences. `Additive` states it
  over each coefficient field, at every intermediate field and every
  admissible `ψ`.
- **Inductivity in degree 0 on generators.** By Tate's definition (2.3),
  `R⁰(W_L)` consists of the differences `[A] - [B]` with `dim A = dim B`.
  Given additivity, `ε₁` extends to a homomorphism on virtual
  representations, and `Ind` is additive. So the equation for all such pairs
  is exactly the commutativity of Tate's diagram on `R⁰`.
- **Every admissible `ψ` on `E`.** Tate's function is
  `(E, V_E) ↦ ε₁(V_E, ψ_F ∘ Tr_(E/F))` for one character `ψ_F` of `F`, and
  his diagram compares `E' ⊆ E`. `InductiveInDegreeZero` instead allows any
  admissible `ψ` on the smaller field, paired with `ψ ∘ Tr_(L/E)` on the
  larger one, as in `NonabelianSystem.InductionRelation`. Tate's form is the
  special case `ψ = ψ_F ∘ Tr_(E/F)`, since `Tr_(L/F) = Tr_(E/F) ∘ Tr_(L/E)`.
- **The rank-one clause.** Tate states it for `χ : F* → E*`, that is, at the
  base field. `RankOneFormula` holds at every intermediate field `E` of the
  common closure; at the bottom field it is Tate's statement. A character `χ`
  with a conductor `a(χ)` is exactly a `K`-valued quasi-character in Tate's
  sense. No hypothesis on `A` is needed: `reciprocityUnits` is continuous and
  `U^a` is open, so the kernel of `A` contains an open subgroup of `W_E`. The
  clause holds for every `c` of the right order and every system of
  representatives, as in Tate's "`u ∈ O* mod π^(a(χ))`".
- **A misprint in (3.6.11).** The printed display reads
  `ε₁(χ, ψ) = χ(c) q^(n(ψ)) ∑_(u ∈ O* mod π^(a(χ))) χ(u)(u/c)`: the
  character `ψ` and the inverse on `χ(u)` are missing. Tate says the formula
  follows from (3.2.6.1) and (3.2.6.2), and (3.2.6.2) integrates
  `χ⁻¹(x) ψ(x)` over `c⁻¹ O*`. This gives `χ⁻¹(u) ψ(u/c)`, which
  `RankOneFormula` uses. The computation is in the Markdown of
  `Langlands.LocalFactor.EpsilonOneStatement`, clause 1.

### Why the clauses hold

This explains the statement only. None of it is a Lean proof. Fix a system
`ε` and write `ε₁^ℂ(V, ψ) = ε_E([V], ψ, μ₁)` with `μ₁(O_E) = 1` for complex
inputs. It is equivariant under every automorphism of `ℂ` (Tate (3.6.10),
clause 3 of `EpsilonOneStatement`), and it satisfies (3.6.11) (clause 1
there).

- **Small fields of definition.** Let `ψ : E → K` and `A` satisfy Tate's
  conditions. The values of `ψ` are roots of unity: `E / π^(-n) O` is a
  `p`-primary torsion group. Inertia acts on `A` through a finite quotient,
  and `W_E` is generated by inertia and one Frobenius element. So in a basis
  of `A` all matrices of the action have entries in a finitely generated
  field. Hence `ψ` and `A` are defined over a countable subfield `K₀ ⊆ K`:
  `A` is a conjugate of a representation `A₀` over `K₀` along the inclusion.
  Every countable field of characteristic 0 embeds in `ℂ`.
- **Existence.** Choose such `K₀`, `A₀` and an embedding `ι : K₀ → ℂ`, and
  put `ε₁(A, ψ) = ι⁻¹(ε₁^ℂ(A₀^ι, ι ∘ ψ))`. The value lies in `ι(K₀)`: every
  automorphism of `ℂ` fixing `ι(K₀)` fixes `A₀^ι` up to isomorphism and fixes
  `ι ∘ ψ`, hence fixes the value by (3.6.10), and the elements of `ℂ` fixed by
  all automorphisms over a subfield form that subfield. The value does not
  depend on the choices. Every isomorphism between countable subfields of
  `ℂ` extends to an automorphism of `ℂ`, so two embeddings of `K₀` give the
  same value by (3.6.10). Two choices of `K₀` and `A₀` are compared inside a
  larger countable subfield of `K` that contains both and the entries of an
  isomorphism between their base changes; every embedding extends to it.
  Compatibility with `α : K → K'` follows by using `α(K₀)` and `ι ∘ α⁻¹` for
  the conjugates. When `κ : K ≃ ℂ`, the choice
  `ι = κ` on `K₀` gives `Normalized`, since `A'` is isomorphic to `A₀^κ` and
  `ε` depends only on the class `[A']`. On the remaining inputs any value,
  for example `1`, may be used.
- **Uniqueness.** Let `ε₁` satisfy `Compatible` and `Normalized`. The
  subfield `K₀` and the field `ℂ` lifted to the universe `uK` are fields of
  characteristic 0 in the universe `uK`. `Compatible` for the inclusion
  `K₀ → K` and for `ι : K₀ → ℂ`, followed by `Normalized` for the lifted copy
  of `ℂ`, gives `ε₁(A, ψ) = ι⁻¹(ε₁^ℂ(A₀^ι, ι ∘ ψ))`. The right side does not
  depend on `ε₁`.
- **Properties.** By uniqueness each `ε₁` is computed by this formula on all
  inputs satisfying Tate's conditions. Induced representations and
  `ψ ∘ Tr_(L/E)` again satisfy the conditions. A short exact sequence, a pair
  `A, B` of equal rank, or a character `χ` is defined over one countable
  subfield, and its conjugate along `ι` is a short exact sequence of
  continuous complex representations, a degree-zero pair, or a continuous
  complex character with the same conductors. Conjugation commutes with
  induction and with the trace. Then `Additive` follows from the additivity
  of `ε`, `InductiveInDegreeZero` from its degree-zero induction (the Haar
  measures do not matter there), and `RankOneFormula` from its rank-one law
  and (3.6.11) over `ℂ`, transported by `ι⁻¹`.

### Related items not restated

- Tate's remark (3) at the end of 3.6: the `ε_D`-system, like `ε₁`, works
  over any coefficient field of characteristic 0 once Haar measures with
  values in that field are defined (citing Deligne, (6.1)). It is a remark
  about presentation, and the Library has no field-valued Haar measures. By
  Deligne (6.1), every Haar measure `μ` with values in `K` is `μ(O)` times
  the unique measure giving `O` volume one. So for `μ(O) ≠ 0`,
  `ε_D(V, ψ, μ)` over `K` is `μ(O)^(dim V) · ε₁(V, ψ)`, and the remark asserts
  nothing beyond this module's `ε₁`. It is not formalized.
- The global remark after (3.6.10), the archimedean `dx₁`, and the remark on
  `ε_L` are discussed in the Markdown of
  `Langlands.LocalFactor.EpsilonOneStatement`.

## Sources

- `tate-1979-number-theoretic-background`, SHA-256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
  J. Tate, *Number theoretic background*, Corvallis Part II (1979). PDF page =
  printed page + 9.
  - Printed p.18 (PDF p.27): (3.6.10), (3.6.11), the paragraph quoted above,
    and the closing remarks (1)-(3) of 3.6.
  - Printed p.11 (PDF p.20): (2.3), the group `R⁰` of degree-zero virtual
    representations, and Definition (2.3.2) of additive, inductive, and
    inductive in degree 0. It continues on printed p.12 (PDF p.21), which
    also has the unicity Remark (2.3.3).
  - Printed pp.13-14 (PDF pp.22-23): (3.2.6), `n(ψ)`, `a(χ)`, `c`, and the
    rank-one formulas (3.2.6.1) and (3.2.6.2).
- `deligne-1973-local-constants`, SHA-256
  `b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
  P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
  LNM 349 (1973). Printed p.554 (PDF p.54): (6.1), Haar measures with values
  in a `ℤ[1/p]`-module `M`; the one with `μ₀(O) = 1` is unique, and every
  `M`-valued Haar measure is `m · μ₀` with `m = μ(O)`.
