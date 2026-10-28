# Normal-subgroup coinvariant tower equivalence

`Langlands.Jacquet.coinvariantTower` proves exactly the published proposition
`Langlands.Jacquet.CoinvariantTowerStatement` from
`Langlands.Representation.Jacquet.AlgebraStatement`. The theorem has the
statement's own implicit binders `{G : Type uG} [Group G] {V : Type uV}
[AddCommGroup V] [Module ℂ V]`, so the group and carrier universes remain
independent. It proves the statement for every representation `rho`, and for
every pair of normal subgroups `N ≤ P` of `G`. No topology, smoothness,
finite-dimensionality, admissibility, generation or splitting hypothesis is
added. The combined `CoinvariantAlgebraStatement`, and its twist and
central-action clauses, are not proved here.

Write `V_N` for Mathlib's `Representation.Coinvariants (rho.comp N.subtype)`,
with the descended action `rho.toCoinvariants N` of the whole group `G`.
Write `(V_N)_P` for the coinvariants of that representation restricted to `P`,
with the action `(rho.toCoinvariants N).toCoinvariants P`. The conclusion is a
`Representation.Equiv` between these actual Mathlib `G`-representations. It
sends the double class of each vector `v` to its single `P`-class. No new
quotient construction is introduced.

## Implemented proof

All maps come from the quotient universal property
`Representation.Coinvariants.lift`. Every identity is checked on represented
vectors, where Mathlib's `Coinvariants.mk_self_apply` and `toCoinvariants_mk`
compute definitionally.

1. `coinvariantTowerStep` is the linear map `V_N → V_P` induced by the quotient
   map `mk : V → V_P`. It is well defined because each `n` in `N` also lies in
   `P`, by `N ≤ P`. Hence `mk (rho n v) = mk v` in `V_P`. This step uses
   neither normality hypothesis.
2. `coinvariantTowerForward : (V_N)_P → V_P` lifts `coinvariantTowerStep`
   through the second quotient. For `p` in `P`, the two linear maps
   `V_N → V_P` given by `x ↦ step (p • x)` and `step` are compared with
   `Coinvariants.hom_ext`. On the class of `v` they give `mk (rho p v)` and
   `mk v`, which agree by `mk_self_apply`.
3. `coinvariantTowerBackward : V_P → (V_N)_P` lifts the composite of the two
   quotient maps `V → V_N → (V_N)_P`. For `p` in `P`, the descended action
   sends the class of `v` to the class of `rho p v`. The second quotient
   identifies this with the class of `v`.
4. `coinvariantTowerBackward_forward` and `coinvariantTowerForward_backward`
   prove the two inverse laws. They use `Coinvariants.induction_on` twice or
   once to reduce to represented vectors. There both composites return the
   same double or single class by definition.
5. `coinvariantTowerForward_comp` proves equivariance for every `g` in the
   ambient group `G`, not only in `P`. On the double class of `v`, both
   composites give the `P`-class of `rho g v`. Here both normality instances
   are needed, because the two descended `G`-actions are defined using them.
6. `coinvariantTowerEquiv` bundles the maps with `LinearEquiv.ofLinearMap` and
   Mathlib's `Representation.Equiv.mk`. The latter requires only the forward
   equivariance; Mathlib derives the inverse's equivariance.
   `coinvariantTowerEquiv_mk_mk` and `coinvariantTowerEquiv_symm_mk` record the
   formulas in both directions; both hold by `rfl`.

The closing theorem introduces `rho`, `N`, `P`, the two normality instances
and `N ≤ P`. It supplies `coinvariantTowerEquiv` together with the formula
`coinvariantTowerEquiv_mk_mk`, which is exactly the statement's prescribed
formula. The equivalence and its formula lemmas are named so that consumers
can use the actual map instead of choosing from the existential.

## Provenance and scope

The target is a derived, unnormalized algebraic formulation fixed by the
published statement pair. Its source motivation is Bernstein and Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4) 10
(1977), registered as `bernstein-zelevinsky-1977-induced-i`, PDF SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Worker 834 read Section 1.8(b) and Proposition 1.9 from the original, printed
pp.444–445 (PDF pp.5–6). Section 1.8(b) defines the relation span `E(U, θ)`,
the quotient `E/E(U, θ)`, and the `M`-action
`δ(m)(ξ + E(U, θ)) = mod_U^{-1/2}(m) · (π(m)ξ + E(U, θ))`. This formula is the
bottom display of printed p.444 and was checked visually in the scan. The
positive half power `mod_U^{1/2}` appears instead in the induction formula of
Section 1.8(a). Proposition 1.9(c) states the transitivity
`r_{V,θ'} ∘ r_{U,θ} = r_{U°,θ°}` for the normalized localisation functors.
The source refers to its reference [1] for the proof. No errata note for this
source exists in the Library notes at this workspace base.

The present theorem is the trivial-character quotient identity underlying
that transitivity. It has no modulus factor, and both subgroups are normal in
the acting group. It does not prove the normalized parabolic transitivity
theorem, the geometric orbit comparison, or the identification of an actual
parabolic tower. The implemented proof is the direct quotient argument above,
not a translation of the source's cited proof.

## Dependencies and checking

The only project import is the unchanged published statement module
`Langlands.Representation.Jacquet.AlgebraStatement`. Its Lean and Markdown
files have SHA256 `08710cdb6b70ccea63cca7b8ac42d3a4a7067a203859b618ce5e637093cca1cc`
and `bae932f731ebe39be292ce296c230b68856bba6feb921f5aa8bd07d45f9e2c74`.
Mathlib's own `Mathlib/RepresentationTheory/Coinvariants.lean` and
`Intertwining.lean` supply every quotient, action and equivalence used.

Development checks in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) compile the
module with zero errors and warnings. The inspection of `coinvariantTower`
reports universe parameters `uG` and `uV` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. A separate private metaprogram check
found the theorem's type syntactically equal to the statement's binders
applied to `CoinvariantTowerStatement`. These are development checks, not
acceptance. This pair is authored by Worker 834.
