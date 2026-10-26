# Finite length of restriction to the actual mirabolic subgroup

Author: Worker 499.

`Langlands.Whittaker.MirabolicFiniteLengthStatement.{uF,uV}` states implication
(1) implies (2) of Bernstein–Zelevinsky (1976), Corollary 5.22, printed p.51,
specialized to finite extensions of the p-adic numbers. It is a `Prop`-valued
definition. This module supplies no proof of the proposition.

For every prime `p`, algebraic extension `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, natural number `n`, and complex representation
`ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V`, the statement assumes
smoothness and finite length as a module over
`MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)`. It concludes finite length
over `MonoidAlgebra ℂ (GeneralLinear.mirabolic n F.Carrier)` for

```lean
Representation.asModule (ρ.comp (GeneralLinear.mirabolic n F.Carrier).subtype)
```

The local `letI := T.topology` installs precisely the supplied field topology
before smoothness is formed. The matrix group inherits its matrix-unit topology.
The remaining fields of `TopologicalData` certify that this supplied topology is
a compatible nonarchimedean local-field topology. No independent topology on `V`
is required.

## Actual group, action, and scope

The existing `Langlands.GeneralLinear.mirabolic n F.Carrier` consists of
invertible matrices with last row `(0, …, 0, 1)`. It is exactly the subgroup
`P` in BZ76 §5.1, printed p.44, with the source's matrix rank replaced by `n + 1`
and indices starting at zero. Its `.subtype` is the actual inclusion into the
existing general linear group. Restriction is composition with that inclusion:
an element `g` acts by `ρ g.val` on every vector of the original `V`.
Mathlib's `Representation.asModule` retains the full underlying carrier as a
type synonym and equips it with the integrated group-algebra action. The target
uses that action directly.

The field universe `uF` and carrier universe `uV` are independent. The assumptions
on `V : Type uV` are only `AddCommGroup V` and `Module ℂ V`. There is no
admissibility, irreducibility, scalar central character, finite complex
dimension, additive character, or derivative/classification premise.
All `n : ℕ` are quantified. At `n = 0` the rank is one and the existing
`GeneralLinear.Mirabolic.rankOneSubsingleton` identifies the mirabolic group as
trivial. No nonzero-vector or nontrivial-carrier hypothesis excludes the zero
representation; Mathlib's finite-length predicate includes the subsingleton
case.

BZ76 calls a representation algebraic when each vector has open stabilizer
(§2.1, printed p.15); this is the existing `Langlands.IsSmooth` condition,
expressed by an open subgroup fixing each vector. The source defines finite
length through bounded lengths of strict submodule chains (§2.8, printed p.16).
The `IsFiniteLength` predicates here are Mathlib's actual group-algebra module
predicates. Mathlib's `isFiniteLength_iff_exists_compositionSeries` identifies
them with existence of a finite composition series from bottom to top in the
invariant-submodule lattice.

Only the specified direction of Corollary 5.22 is stated. The other equivalences
in 5.22 and the separate mirabolic-representation criterion 5.23 are outside
this declaration. The theorem that admissible representations of finite type
have finite GL length is separately stated in
`Langlands.GLAdmissibleFiniteLengthStatement`; this contribution takes GL finite
length as input.

## Source proof and remaining proof obligations

The complete proof of Corollary 5.22 on printed p.51 was read, and its formulas
were visually checked. Write `r = n + 1`, and let `U` be the full upper
unipotent subgroup. For a smooth character `θ` of `U`, the source's
`E_{U,θ}` is the quotient by the complex span of
`ρ(u)v - θ(u)v` (§2.30, printed p.24).

The source proves (1) implies (3), followed by (3) implies (2). The following
mathematical steps remain proof obligations for this target; they are not
assumed as premises or proved in this statement module:

1. **Finite-dimensional twisted coinvariants.** BZ76 Theorem 5.21, printed
   p.51, bounds `dim E_{U,θ}` by `r!` for an irreducible smooth representation of
   `GL_r(F)` and every smooth character `θ`. Together with exactness and a
   finite GL composition series, this gives finite-dimensional twisted
   coinvariants for the input representation. The source says that 5.21 is
   proved in §7; this contribution does not formalize that proof.
2. **Exactness.** BZ76 Proposition 2.35(b), printed p.25, gives exactness of
   twisted coinvariants when the subgroup is exhausted by compact subgroups.
   A Lean proof must apply this to the actual `U`, justify the required
   compact exhaustion, and obtain additivity of finite dimensions along
   submodule filtrations. Smoothness must also pass to the actual restriction
   and its subquotients.
3. **Finitely many character representatives.** Using §5.5, printed p.45,
   the proof chooses `Ω` consisting of the `2^(r-1)` characters whose
   adjacent-entry coefficients are zero or one relative to a fixed nontrivial
   additive character. Every smooth character of `U` is carried to one of
   these by conjugation through the diagonal subgroup of `P`, which normalizes
   `U`. A Lean proof must construct these representatives and transport
   twisted coinvariants along that conjugation, including the empty
   coefficient tuple at rank one.
4. **Detection of nonzero mirabolic subquotients.** BZ76 Corollary 5.14,
   printed p.48, says that every nonzero smooth `P`-representation has
   nonzero `E_{U,θ}` for some character. Its printed proof uses the exact
   sequence of §5.12(d), induction on rank, and the iterated-coinvariant
   identity §2.32. Transport to `Ω` then makes every nonzero successive
   quotient contribute at least one to
   `d(E) = ∑ θ ∈ Ω, dim E_{U,θ}`.
5. **Finite length from the chain bound.** Exactness gives
   `d(E) = ∑ᵢ d(Eᵢ/Eᵢ₋₁)` for a strict finite chain of `P`-submodules.
   Thus every such chain has length at most the finite natural number `d(E)`.
   Relating actual invariant subspaces to group-algebra submodules and this
   chain bound to Mathlib's `IsFiniteLength` finishes the source route,
   including the zero module.

The existing `Langlands.Group.GL.Mirabolic` and
`Langlands.Representation.Whittaker.MirabolicModels` pairs are unchanged.
Neither the compact minimality nor the Kirillov embedding theorem is used as
an extra hypothesis here. JPSS (1983), printed p.397, explicitly invokes
BZ76 Corollary 5.22 to obtain finite composition series for the restrictions
of its two representations to `P_r`. This statement isolates that restriction
step for the Library's actual representations; it does not prove the JPSS
bilinear bound.

## Sources and reading

- I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
  where F is a non-Archimedean local field*, Russian Mathematical Surveys 31:3
  (1976), 1–68. Registered source:
  `bernstein-zelevinsky-1976-representations-gln`, retained Central-Library PDF
  SHA256 `72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
  Printed pages equal one-based PDF pages. Read pp.15–16,23–25,44–45,47–51;
  in particular §2.1, §2.8, §§2.30–2.35, §§5.1–5.6, §5.14, and the
  statement and complete proof of Corollary 5.22. The p.51 formulas were
  checked in the rendered original.
- H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
  Convolutions*, American Journal of Mathematics 105 (1983), 367–464.
  Registered source: `jpss-1983-rankin-selberg`, retained Central-Library PDF
  SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
  Printed p.397, one-based PDF page 32, was read visually for its use of
  BZ76 Corollary 5.22.

No matching erratum note was found in the checked project, current Library,
or literature errata locations. No correction to these cited passages was
available there. All source claims above are distinguished from the unproved
Lean target.
