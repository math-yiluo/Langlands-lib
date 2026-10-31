# Detection of nonzero mirabolic representations by twisted coinvariants

Author: Worker 11.

This helper module of the mirabolic finite-length proof
[MirabolicFiniteLengthProof](MirabolicFiniteLengthProof.md) proves a form of
Bernstein–Zelevinsky (1976), Corollary 5.14, printed p.48, for the Library's
actual mirabolic groups. Fix a locally constant character `ψ` of `F` that
generates all locally constant characters in the sense of
[MirabolicFiniteLengthCharacters](MirabolicFiniteLengthCharacters.md). Then a
smooth representation of the actual mirabolic group `P_(n+1)` with a nonzero
vector has nonzero twisted coinvariants for one of the `2^n` characters
`θ_S(u) = ψ(∑_{S i} u_(i,i+1))`. All declarations live in the namespace
`Langlands.Whittaker.MirabolicFiniteLength`. No existing pair is changed.

The source states 5.14 for some character `θ` of `U`. Its proof uses the exact
sequence of 5.12(d) for the functors `Φ⁻`, `Ψ⁻`, induction on the rank and
the transitivity 2.32 of coinvariants. The Lean proof keeps the induction on
the rank and the transitivity. It replaces 5.12(d), whose proof needs the
`l`-sheaf realization of 5.9–5.10, by a direct argument on the abelian radical
given below. The characters it produces already have all adjacent-entry coefficients
`0` or `1`, i.e. they lie in the source's set `Ω` of Corollary 5.22, printed
p.51. Hence the separate conjugation of an arbitrary `θ` into `Ω` in the source
proof of 5.22 is not needed.

Notation. `Jacquet.Localization.relations σ U θ` is the complex span of the
vectors `σ u v - θ u • v`, the space `E(U,θ)` of BZ76 §2.30, printed p.24. Its
quotient is `Coinvariants σ U θ`, with quotient map `mk`. Twisted coinvariants
are nonzero exactly when the relations are not the whole space.

## General facts about relations

These hold for any group `G` and complex representation `σ`.

- `isInvariant_bot U θ`: every character is invariant under the trivial
  subgroup. The Library's exactness lemmas in
  `Langlands.Representation.Jacquet.LocalizationExactnessProof` are stated
  for coinvariants with a residual action of a normalizing subgroup. They are
  used here with the trivial subgroup.
- `relations_eq_of_surjective`: the relations do not change when the acting
  subgroup is reparametrized by a surjection under which the actions and the
  characters correspond.
- `apply_mem_relations`: if `h` normalizes `U` and `θ'(h u h⁻¹) = θ(u)`, then
  `σ h` maps the relations of `θ` into those of `θ'`. Indeed `σ h` sends the
  generator `σ u w - θ u • w` to `σ(h u h⁻¹)(σ h w) - θ'(h u h⁻¹) • σ h w`.
- `relations_eq_bot_of_subsingleton`: the relations of a trivial subgroup are
  zero.
- `mem_relations_of_injective`: let `G` be a topological group, `U` exhausted
  by compact subgroups (`IsLimitOfCompactSubgroups`) and `θ` locally constant.
  For an injective intertwining map `i` into a smooth `σ`, if `i w` lies in the
  relations of `σ`, then `w` lies in the relations of the source. This is the
  Library's `map_injective_of_smooth`, the injectivity part of the exactness
  in BZ76 Proposition 2.35, printed p.25.

## The abelian step

Let `A` be a commutative topological group.

- `isLimitOfCompactSubgroups_top`: if every compact subset of a group lies in a
  compact subgroup, the top subgroup is exhausted by compact subgroups.
- `exists_pow_mem_of_isOpen`: if `⊤ : Subgroup A` is exhausted by compact
  subgroups and `H` is an open subgroup, each `a ∈ A` has a positive power in
  `H`. Indeed `a` lies in a compact subgroup `C`, `H ∩ C` has finite index in
  `C`, and Mathlib's `Subgroup.pow_relIndex_mem` applies.
- `exists_character_not_mem_relations`: under the same exhaustion hypothesis,
  let `σ` be a smooth representation of `A` and `e ≠ 0`. Then some locally
  constant character `χ : A →* ℂˣ` satisfies `e ∉ relations σ ⊤ χ`.

Proof of the last statement. Work in the group algebra `ℂ[A]`, acting on
`σ.asModule`. The annihilator `I` of `e` is a proper ideal because `e ≠ 0`.
Choose a maximal ideal `m ⊇ I` (`Ideal.exists_le_maximal`). Let `H` be an open
subgroup fixing `e`, given by smoothness. Then `s - 1 ∈ I ⊆ m` for `s ∈ H`.
Every group element has a power in `H`, so its image in the field `ℂ[A]/m` is
a root of unity. Sums and scalar multiples of integral elements are integral,
so `ℂ[A]/m` is integral over `ℂ` (by `MonoidAlgebra.induction_on`). Because `ℂ`
is algebraically closed, `ℂ → ℂ[A]/m` is bijective
(`IsAlgClosed.algebraMap_bijective_of_isIntegral`). This yields an algebra map
`φ : ℂ[A] → ℂ` with kernel `m`. Put `χ a = φ a`. Then `a - χ a ∈ m` for every
`a`, and `χ` is trivial on `H`, hence locally constant.
Suppose `e` were in the relations. Let `W` be the cyclic subrepresentation
`ℂ[A] e`. By `mem_relations_of_injective` along the inclusion, `e` lies in the
relations of `W`. Each generator of those relations is
`a·(f e) - χ a • (f e) = ((a - χ a) f) e` with `(a - χ a) f ∈ m`. Hence
`e = x e` for some `x ∈ m`. Then `1 - x ∈ I ⊆ m`, so `1 ∈ m`, a contradiction.

## Simple characters and the radical decomposition

Here `F` is any commutative ring, and `ψ : Multiplicative F →* ℂˣ`. The
groups are those of `Langlands.Group.GL.MirabolicRadical`:
`GeneralLinear.mirabolic n F` is `P_(n+1)`. Its subgroup
`radical n F` consists of the matrices `u(v) = [[I, v], [0, 1]]`, with
coordinates `radicalEquiv` onto `F^n`. The Levi map `levi g = diag(g, 1)` and
the embedding `successor : P_(n+1) → P_(n+2)` come with
`successorSubgroup n F`, its range.
`GeneralLinear.Mirabolic.upperUnipotent n F`, written `U_(n+1)`, is the
upper-unipotent subgroup of `P_(n+1)`, identified with the upper-unipotent subgroup of `GL_(n+1)` by
`upperUnipotentEquiv`.

- `selectedSum S`: for `S : Fin n → Bool`, the homomorphism
  `u ↦ ∑_{S i} u_(i,i+1)` from the upper-unipotent subgroup of `GL_(n+1)` to
  `F`. It is multiplicative by the Library's
  `GeneralLinear.UpperUnipotent.mul_adjacent_entry`.
- `simpleCharacter ψ S`: the character
  `θ_S(u) = ψ(∑_{S i} u_(i,i+1))` of the upper-unipotent subgroup of `P_(n+1)`,
  i.e. `ψ ∘ selectedSum S ∘ upperUnipotentEquiv`. For a nontrivial `ψ`, these are
  the characters `θ(a₁, …, a_n)` of BZ76 Lemma 5.5, printed p.45, with every
  `a_i ∈ {0, 1}`: the set `Ω` of Corollary 5.22. `simpleCharacter_apply`
  unfolds it.
- `radicalCharacter ψ n b`: the character of `radical (n + 1) F` that is trivial
  for `b = false` and `u(v) ↦ ψ(v_last)` for `b = true`. The latter is the
  character `Θ` of BZ76 §5.4 when `ψ` is nontrivial. `radicalCharacter_apply`
  unfolds it.
- `radicalCharacter_isInvariant`: these characters are invariant under
  conjugation by `successorSubgroup n F`. The Library's
  `levi_conjugate_radicalElement` computes conjugation as `v ↦ g v`. The last
  row of a mirabolic matrix is the last unit row, so `(g v)_last = v_last`
  (`Derivative.Mirabolic.mulVec_last`).
- `topLeftMatrix`, `topLeftGL`, `topLeft`: the upper-left `(n+1) × (n+1)`
  block of `u` in the upper-unipotent subgroup of `P_(n+2)`. It is upper
  triangular with unit diagonal (`topLeftMatrix_isUpperTriangular`,
  `topLeftMatrix_diag`), so its determinant is one (`det_topLeftMatrix`). It is
  therefore an upper-unipotent element of `GL_(n+1)`
  (`topLeftGL_mem_upperUnipotent`) and of `P_(n+1)`. `topLeft_apply` gives its
  entries. `successor_bottom` records the last row of `successor g`.
- `lastColumn u`: the last column of `u` above the corner entry.
- `eq_radicalElement_mul_successor`: `u = u(lastColumn u) · successor(topLeft u)`.
  This is the decomposition `U = U' · M` of BZ76 §5.2, printed p.44. It is
  checked entrywise by splitting both indices into the last index and the
  others.
- `simpleCharacter_snoc`: `θ_(S', b)(u) = θ_b(u(lastColumn u)) · θ_S'(topLeft u)`,
  where `(S', b)` is `Fin.snoc S' b`, i.e. `S'` followed by `b`.
- `radicalQuotient σ ψ b`: for a representation `σ` of `P_(n+2)`, the
  representation of `P_(n+1)` on `Coinvariants σ (radical (n + 1) F) θ_b`. It is
  given by the Library's residual `action` of `successorSubgroup n F`, composed
  with `successorEquiv`. `radicalQuotient_mk` says that `m` acts by
  `mk x ↦ mk (σ (successor m) x)`.
- `mk_mem_relations`: the quotient map onto the radical coinvariants sends the
  relations of `θ_(S', b)` for `U_(n+2)` into those of `θ_S'` for the
  radical quotient `τ`. On a generator `σ u y - θ_(S', b)(u) y`, write
  `u = u(c) · successor(t)`. The radical factor acts on the radical coinvariants
  by `θ_b(u(c))` (the Library's `mk_apply_subgroup`). The image is then
  `θ_b(u(c))` times a generator `τ t (mk y) - θ_S'(t) mk y`. This is the
  inclusion behind the transitivity `E_(U,θ) = (E_(M,θ|M))_(U',θ|U')` of BZ76
  §2.32, printed p.24, as used in the proof of 5.14.

## The p-adic induction

Here `F : PadicField p` with supplied `T : F.TopologicalData`, whose topology
is installed.

- `isLimitOfCompactSubgroups_pi m`: the vector group `F^m` (as a multiplicative
  group) is exhausted by compact subgroups. The product lattices `L_k^m` are
  compact and open (from the imported `PadicField.TopologicalData.isCompact_additiveLattice`
  and `PadicField.TopologicalData.isOpen_additiveLattice`) and increase with `k`. They cover `F^m` by
  `exists_mem_additiveLattice`. A compact set therefore lies in one of them
  (`IsCompact.elim_directed_cover`).
- `exists_relations_ne_top T ψ hgen n`: let `ψ` generate the locally constant
  characters of `F` (`hgen`). For every carrier `E`, every smooth
  representation `σ` of `GeneralLinear.mirabolic n F.Carrier` with a nonzero
  vector `e`, some `S : Fin n → Bool` has
  `relations σ (GeneralLinear.Mirabolic.upperUnipotent n F.Carrier)
  (simpleCharacter ψ S) ≠ ⊤`.

Proof, by induction on `n` for all carriers at once. For `n = 0` the
upper-unipotent group is trivial, the relations are zero, and `e ≠ 0` is not
in them. For `n + 1`, restrict `σ` to the radical `R ≅ F^(n+1)` through
`radicalEquiv`. The restriction is smooth (Library `isSmooth_comp` with the
continuous `radicalContinuousEquiv`). The abelian step and
`isLimitOfCompactSubgroups_pi` give a locally constant `χ` of `F^(n+1)` with
`e ∉ relations σ R χ`. By `exists_dotProduct_eq`, `χ v = ψ(a ⬝ᵥ v)`. If
`a = 0`, put `g = 1` and `b = false`. Otherwise
`exists_dotProduct_mulVec_eq_last` gives `g` with `a ⬝ᵥ (g v) = v_last`; put
`b = true`. In both cases `χ(g v) = θ_b(u(v))`. Hence conjugation by `levi g`
carries `χ` to `θ_b`. By `apply_mem_relations`, the vector `σ (levi g)⁻¹ e` is
not in the relations of `θ_b`, so its image in the radical quotient is
nonzero. The radical quotient is smooth by the Library's `isSmooth_action` and
`isSmooth_comp`. The induction hypothesis gives `S'` whose relations in the
radical quotient are not everything. If the relations of `θ_(S', b)` were
everything, `mk_mem_relations` and the surjectivity of `mk` would make the
relations of `θ_S'` in the radical quotient everything. So `S = (S', b)` works.

This mirrors the source's two cases: `θ|M = Θ` for the functor `Φ⁻` and
`θ|M = 1` for `Ψ⁻`. Because conjugation by `levi g` moves the vector, the
statement is existential over the nonzero vector and quantifies over all
carriers.

## Sources

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
(1976), 1–68. Registered source `bernstein-zelevinsky-1976-representations-gln`,
Central-Library PDF SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`; printed
pages equal one-based PDF pages. Read: §§2.30–2.35 pp.24–25, §§5.1–5.5
pp.44–45, §§5.9–5.14 pp.45–48, Corollaries 5.22 and 5.23 pp.51–52.
