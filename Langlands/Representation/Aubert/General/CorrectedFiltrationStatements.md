# Graded targets for the corrected support filtration

Implementation and documentation: Worker 379 (task
`0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4`, the complex-and-targets unit of the
general Aubert program `46df6a68-5db4-4428-8044-05151d6ce1f6`). The complex, its
terms and transition maps are Worker 194's; the filtration is
`CorrectedFiltration.step`.

This module states, as two proposition targets, the representation-theoretic
assertions about the graded pieces of the corrected support filtration that the
proof of the corrected Theorem 3.6 needs (erratum, pp. 4688–4690, with the
Ban–Jantzen 2016 Section 4 repair). Nothing here is proved or assumed.

## Data

Both targets are `Prop`-valued definitions in namespace
`Langlands.Aubert.General.CorrectedFiltration` of:

* the data of `StandardComplex`: `ι` with `[LinearOrder ι] [Fintype ι]`, a locally
  compact nonarchimedean group `G`, the standard families `P M U` with `h`,
  `hclosed`, `hδ`, `hP : Monotone P` and `hU : Antitone U`;
* the data of `IsInSupportCategory`: `hM`, the Levi-in-Levi decompositions `hL`
  and the association relation `IsAssociate`;
* a subgroup `T` with `Weyl T = N_G(T)/Z_G(T)` finite, and a Coxeter system `cs`
  on `Weyl T` indexed by `ι`.

`E` is an arbitrary smooth representation with carrier in `Type (max uG uV)`, and
`E ∈ Alg({I})` is `IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) E`.
`w` is the `i`-th length-ordered element `Support.rankOrderedElement cs.length i hi`,
the element added at step `i` of the filtration. The target `J` is written
through its removed roots `s`, `J = S \ s`, as in `StandardComplex`, and
`step … E I s i` is the `i`-th step `Ẽ^{θ_i'}_{J,I}` of `r_I(E_J)`.

`Ad(w⁻¹)` is `conjugationFunctor m hK` for a lift `m ∈ N_G(T)` of `w⁻¹`: it sends
a representation `τ` of `M K` to `x ↦ τ(m⁻¹ x m)` on `M I`, where `hK` states
`M I = m (M K) m⁻¹`, that is `M K = m⁻¹ (M I) m`. Since `m⁻¹` lifts `w`, this
is `M K = w (M I) w⁻¹` and `x ↦ τ(w x w⁻¹)`, Aubert's `Ad(w⁻¹)(τ)`.

## `CorrectedGradedVanishingTarget`

For `E ∈ Alg({I})`, every `s`, `i`: if `step (i + 1) ≠ step i` in `r_I(E_J)`, then
for every lift `m` of `w⁻¹` there is a standard `K ⊆ J` with
`∀ x, x ∈ M I ↔ m⁻¹ x m ∈ M K`, that is `w L_I w⁻¹ = L_K ⊆ L_J`.

Source: erratum, pp. 4688–4689: "s'il existe w ∈ W de longueur minimale dans la
double classe W_J w W_I tel que θ_2 − θ_1 = W_J w, et si Ẽ^{θ_2}_{J,I}/Ẽ^{θ_1}_{J,I}
est non nul, on a w L_I w⁻¹ ⊂ L_J", and later "l'ensemble w(I) est formé de
racines simples et est contenu dans J". The argument identifies the graded piece,
by the geometric lemma, with `i^{L_I}_{L_I ∩ w⁻¹L_Jw} Ad(w⁻¹) r^G_{wL_Iw⁻¹ ∩ L_J}(E)`
and uses `E ∈ Alg({I})` to see that a nonzero Jacquet module along
`w L_I w⁻¹ ∩ L_J` forces `w L_I w⁻¹ ⊆ L_J`. Ban and Jantzen point out that this
needs `w` minimal in the whole double coset `W_J w W_I`. In this formalization the
graded piece vanishes when `w` is not minimal (`step_succ_eq`), so the target
concerns the minimal case only through its hypothesis.

## `CorrectedGradedTransitionTarget`

Let `E ∈ Alg({I})`, `i`, `m` a lift of `w⁻¹`, and `K` with
`hK : ∀ x, x ∈ M I ↔ m⁻¹ x m ∈ M K`. Call `s` surviving when `K ⊆ S \ s` and
`w` is minimal in its double coset `W_J w W_I`
(`Group.RelativeWeylIndexing.IsMinimal cs (S \ s) I w`). The target asserts that
there is a family `β`, indexed by the surviving `s`, of morphisms of smooth
`M I`-representations

`β_s : step (i + 1) of r_I(E_J) ⟶ Ad(w⁻¹)(r_{L_K}(E))`

(the source is `SmoothRep.subrepresentation` of the step; the target is
`(conjugationFunctor m hK).obj ((jacquetFunctor (h K) (hclosed K)).obj E)`), such
that

1. every `β_s` is surjective;
2. the kernel of `β_s` is exactly the step `i`: `β_s x = 0 ↔ x ∈ step i`;
3. for surviving `s ⊆ t`, that is `J' = S \ t ⊆ J`, and every `x` in the step
   `i + 1` of `r_I(E_J)`, `β_t (r_I(φ^J_{J'}) x) = β_s x`. Here `r_I(φ^J_{J'})`
   is the actual Jacquet functor applied to Worker 194's transition
   `transition … E hst`, and `transition_mem_step` shows that it preserves the
   step `i + 1`.

By (1) and (2), `β_s` induces an isomorphism from the graded piece
`Ẽ^{θ_{i+1}'}_{J,I} / Ẽ^{θ_i'}_{J,I}` onto `Ad(w⁻¹)(r_{L_K}(E))`. By (3), under
these isomorphisms every graded transition between surviving indices is the
identity. The differential is the signed sum of the transitions with the exterior
signs of Worker 194's complex. So on the surviving indices it is the identity
of `Ad(w⁻¹)(r_{L_K}(E))` multiplied by those signs.

Source: erratum, p. 4689, the isomorphism `f ↦ (l ↦ ∫_{U_I ∩ w⁻¹P_Jw \ U_I}
f(w u l) dµ(u))` of the graded piece onto `(Ad(w⁻¹) ∘ r^G_{wL_Iw⁻¹})(E)`, and
p. 4690: "La construction de l'isomorphisme de Ẽ^{θ_i}_{J,I}/Ẽ^{θ_{i+1}}_{J,I} sur
Ad(w⁻¹)(r^G_{wL_Iw⁻¹}E) montre alors que les applications de transitions δ_k sont
l'identité de Ad(w⁻¹)(r^G_{wL_Iw⁻¹}E) multipliée par le signe qu'il faut." The
compatibility of the projections `π^J_K` used there is the commutative diagram of
p. 4689 (transitivity of Jacquet functors). Ban and Jantzen redo this step for
`w ∈ D(J, I)` (printed pp. 160–162): their isomorphism (4.1) on p. 160, and on
p. 162 the comparison of the integral formulas for `J` and `J − {α}`, which uses
`U_I ∩ w⁻¹ P_{J−{α}} w = U_I ∩ w⁻¹ P_J w` for `w ∈ D(J, I)`: "Therefore, up to sign,
δ is the identity."

The target does not prescribe the integral formula. It asks for some family of
surjections with the stated kernels that is compatible with the actual
transitions. This is what the Koszul argument of p. 4690 uses. The identification
itself does not depend on `E ∈ Alg({I})`, since `K ⊆ J` already gives
`L_I ∩ w⁻¹ L_J w = L_I` and `w L_I w⁻¹ ∩ L_J = L_K`. The hypothesis is kept
because the target is stated in the erratum's setting.

## How the targets enter the proof

On a fixed grade `i` the graded complex in degree `|s|` is the direct sum over the
removed sets `s` of the graded pieces. Its terms vanish outside the surviving `s`:
by `step_succ_eq` when `w` is not minimal in `W_J w W_I`, and by
`CorrectedGradedVanishingTarget` when `K ⊄ J`. Standard Levis determine their
index set (`M` is injective on the indices, a structural fact), so the `K` of the
vanishing target is the given one. By `mem_modifiedSupport_succ_iff` and the
Coxeter minimality criterion (`minimalityLengthCriterion_proof`), the surviving
`J` form the interval `w(I) ⊆ J ⊆ S_w`, where `S_w = {α ∈ S : w⁻¹ α > 0}`. On
that interval the graded complex is `Ad(w⁻¹)(r_{L_K}(E))` tensored with a Koszul
complex. It is acyclic unless `S_w = w(I)`, in which case only the terminal term
survives (erratum, p. 4690). The terminal homology is retained throughout.

## Faithfulness and scope

* `E` is an arbitrary smooth representation. The filtration is indexed by the
  finite Weyl group, not by a composition series of `E`.
* The targets quantify over every lift `m` of `w⁻¹`. Lifts differ by elements of
  `Z_G(T)`, which lie in `M I` for the actual standard families.
* For arbitrary data of the stated shape the targets can be false. They are meant
  for the rational points of a connected reductive group over a nonarchimedean
  local field, with `T` the maximal split torus, `cs` the Coxeter system of the
  relative Weyl group, and the standard families. The Bruhat decomposition and
  the identification of `cs` with the relative root system are structural
  requirements of the program's ledger (A01–A02).
* The cited proofs use the geometric lemma (Bernstein–Zelevinsky, Casselman
  6.2.1 and 6.3.3 as cited by the erratum) and transitivity of Jacquet functors,
  not a classification.

## Declarations

* `CorrectedGradedVanishingTarget`
* `CorrectedGradedTransitionTarget`

Both return `Prop`. They take `P M U h hclosed` (and, for the transition target,
`hδ hP hU`), `hM hL IsAssociate`, `T` and `cs`.

## Sources

* A.-M. Aubert, *Erratum*, Trans. AMS 348 (1996), printed pp. 4688–4690.
* D. Ban and C. Jantzen, *The Langlands quotient theorem for finite central
  extensions of p-adic groups II: intertwining operators and duality*, Glasnik
  Matematički 51 (2016), Section 4, printed pp. 160–162.
