# Intertwining kernels of compact induction from an open subgroup

Worker 3557 states
`Langlands.Induction.CompactInductionIntertwiningStatement.{uR,uG,uV,uW}`,
the conjunction of three propositions about maps between compactly induced
representations. These are proposition definitions and targets for separate
proofs. Defining them does not assume their truth.

## Conventions of the imported constructions

Throughout, `R` is a commutative ring, `G` a group with a topology and
`IsTopologicalGroup G`, and `H` a subgroup of `G` with the subspace topology.
No total disconnectedness, local compactness or Hausdorff property of `G` is
assumed.

`Langlands.Representation.Induction.Definitions` supplies compact induction
with the conventions of Vignéras 1996, I.5.1. For a representation `σ` of
`H` on `V`, an element of `CompactFunctions H σ` is a function `f : G → V`
with `f (h x) = σ h (f x)` for `h ∈ H`, fixed under right translation by one
open subgroup of `G`, whose nonzero support has compact image in the
right-coset space `H \ G` (`LeftQuotient H`). `quotientSupport H f` is that
image `quotientMap H '' Function.support f`, the set of cosets `H x` with
`f x ≠ 0`. `eval H σ f x` is the value `f x`. `G` acts by right translation.

`Langlands.Representation.Induction.OpenAdjunction` supplies, for open `H`
(`hH : IsOpen (H : Set G)`):

- `smoothCompactInduction R H`, the functor from
  `Langlands.SmoothRep.{uR,uG,max uG uV} R H` to
  `Langlands.SmoothRep.{uR,uG,max uG uV} R G` given by compact induction;
  `SmoothRep.hom T` is the underlying linear map of a morphism `T`;
- `unitFunction H hH σ hσ v` for a smooth `σ` (`hσ : IsSmooth σ`): the
  compactly induced function with value `σ h v` at `h ∈ H` and `0` off `H`.
  This is Vignéras's `i_v`, of support `H` with `i_v(1) = v` (I.5.2 b)).

Mathlib supplies the double-coset space
`DoubleCoset.Quotient (H : Set G) (H : Set G)` of the double cosets `H g H`
and the projection `DoubleCoset.mk H H`. `Langlands.IsSmooth σ` says every
vector is fixed by an open subgroup of `H`.

## The two predicates

For representations `σ` of `H` on `V` and `τ` of `H` on `W`:

- `IsIntertwiningKernel H σ τ Φ`, for `Φ : G → (V →ₗ[R] W)`, is the
  conjunction of
  1. the covariance `Φ (h * g * h') = τ h ∘ₗ Φ g ∘ₗ σ h'` for all `h, h' ∈ H`
     and `g ∈ G`, and
  2. for every vector `v`, finiteness of
     `quotientSupport H (fun g => Φ g v)`: only finitely many right cosets
     `H g` have `Φ g v ≠ 0`.
- `IsLocalIntertwinerFamily H σ τ s φ`, for a choice of representatives
  `s : DoubleCoset.Quotient H H → G` and values
  `φ : DoubleCoset.Quotient H H → (V →ₗ[R] W)`, is the conjunction of
  1. for every double coset `q` and every `h ∈ H` with
     `s q * h * (s q)⁻¹ ∈ H`, the identity
     `φ q ∘ₗ σ h = τ (s q * h * (s q)⁻¹) ∘ₗ φ q`; that is, `φ q` intertwines
     `σ` with the conjugate representation `h ↦ τ (s q h (s q)⁻¹)` of
     `H ∩ (s q)⁻¹ H (s q)`, and
  2. for every vector `v`, only finitely many `q` have `φ q v ≠ 0`.

Neither predicate assumes `s` to be a section of `DoubleCoset.mk`; the
statements below add that premise where it is used.

## The three statements

1. `CompactInductionKernelStatement.{uR,uG,uV}`. For every `R`, `G`, every
   open subgroup `H` (`hH`) and all objects `A`, `B` of
   `SmoothRep.{uR,uG,max uG uV} R H`:
   - every morphism
     `T : (smoothCompactInduction R H).obj A ⟶ (smoothCompactInduction R H).obj B`
     has an intertwining kernel `Φ : G → (A →ₗ[R] B)` with
     `Φ g v = (T (unitFunction H hH A.representation A.isSmooth v)) (g)`
     for all `g` and `v`;
   - every intertwining kernel `Φ` arises in this way from exactly one such
     `T`.

   `H` is open but not assumed compact.
2. `CompactInductionDoubleCosetStatement.{uR,uG,uV,uW}`. For every `R`, `G`,
   every subgroup `H` that is open and compact, all representations `σ` of `H`
   on `V : Type uV` and `τ` of `H` on `W : Type uW` with `σ` smooth, and every
   `s : DoubleCoset.Quotient H H → G` with `DoubleCoset.mk H H (s q) = q` for
   all `q`:
   - for every intertwining kernel `Φ`, the restriction `q ↦ Φ (s q)` is a
     local intertwiner family;
   - every local intertwiner family `φ` is the restriction of exactly one
     intertwining kernel `Φ`, that is `Φ (s q) = φ q` for all `q`.

   `τ` is not assumed smooth.
3. `CompactInductionFiniteTypeKernelStatement.{uR,uG,uV,uW}`. For every `R`,
   `G`, every open and compact subgroup `H`, all representations `σ` on `V`
   and `τ` on `W` of `H` such that `σ.asModule` is a finitely generated module
   over `MonoidAlgebra R H`, and every `Φ : G → (V →ₗ[R] W)`:
   `IsIntertwiningKernel H σ τ Φ` holds if and only if `Φ` has the covariance
   of the first conjunct and its support meets only finitely many double
   cosets, `(DoubleCoset.mk H H '' Function.support Φ).Finite`.

   Neither smoothness of `σ` nor of `τ` is assumed.

`CompactInductionIntertwiningStatement.{uR,uG,uV,uW}` is the conjunction of
the three, with `uV` the carrier universe of the first and the source universe
of the other two. It is the entry declaration of the unit.

## Original source and specialization

The registered original is M.-F. Vignéras, *Représentations ℓ-modulaires d'un
groupe réductif p-adique avec ℓ ≠ p*, Progress in Mathematics 137,
Birkhäuser, 1996.

- Literature ID:
  `provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`.
- File: `/home/taskhub/pilot/literature/Vignéras 1996, Représentations ℓ-modulaires d'un groupe réductif p-adique avec ℓ ≠ p.pdf`.
- SHA-256:
  `4d2daeee16515f994dfb04157915179b55b30d5bf2f874a16f13e7cb6fa7d657`.

Printed page `n` of Chapter I is PDF page `n + 18`. The author read and
visually checked I.8 introduction, 8.1 and 8.2 (printed pp.64–65, PDF
pp.82–83), the proof of 8.3 (i), (iii) (printed p.66, PDF p.84) and 8.5
(printed pp.67–68, PDF pp.85–86).

I.8.5 takes closed subgroups `K`, `H` of a locally profinite group `G` with
`K` open, `(σ, W) ∈ Mod_R K` of finite type and `(π, V) ∈ Mod_R H`. It
identifies `Hom_{RG}(ind_{G,K} σ, ind_{G,H} π)` by Frobenius reciprocity with
`Hom_{RK}(σ, Res_{K,G} ind_{G,H} π)` and with the module of functions
`f : G → Hom_R(W, V)` such that a) the support is a finite union of double
cosets `HgK` and b) `f(hgk) = π(h) f(g) σ(k)`. The dictionary is
`f(g)w = B(w)(g) = (A i_w)(g)`. The source names `K = H, σ = π` as one of the
two important cases. In §8, `K` is an open subgroup that is compact modulo the
centre (introduction of §8, printed p.64).

This unit treats the case of one subgroup `K = H` for both representations,
with the source's `(σ, W)` and `(π, V)` renamed `(σ, V)` and `(τ, W)`, so
values lie in `Hom_R(V, W)`.

- The first statement is the dictionary `A ↔ f` for an open subgroup `H`,
  without the finite-type hypothesis and without compactness. Then the
  correct support condition is per vector, as in the source's proof ("pour `w`
  fixe, la fonction `g ↦ f(g)w` vérifie a)"): finitely many right cosets
  `H g`, which is compact support in the discrete space `H \ G`.
- The third statement recovers the source's condition a) for compact open
  `H` and finitely generated `σ`, matching "Comme `W` est de type fini, la
  fonction `f` vérifie a)". The centre is not used; compactness of `H` itself
  replaces compactness modulo the centre.
- The second statement is the double-coset form. In the proof of 8.3 (i),
  (iii), the source writes
  `Hom_G(ind_{G,K} σ, ind_{G,K'} σ') = ⊕_{K'gK} Hom_K(σ, i_{K,g(K')} g(σ'))`
  and, for `σ' = σ`, `R ⊕ (⊕_{KgK ≠ K} Hom_{K ∩ g(K)}(σ, g(σ)))`; 8.2 lists
  the corresponding isomorphic modules, derived from Frobenius reciprocity
  (5.7) and the Mackey decomposition (5.5). Here `g(σ)` is the conjugate of
  `σ` by `g` (5.4 (iv)). With `g = (s q)⁻¹`, the source's
  `Hom_{K ∩ g(K)}(σ, g(τ))` is the module of maps intertwining `σ` with
  `h ↦ τ(s q h (s q)⁻¹)` on `H ∩ (s q)⁻¹ H (s q)`, which is conjunct 1 of
  `IsLocalIntertwinerFamily`. The statement does not pass through the Mackey
  decomposition: it parametrizes kernels directly by their values at double
  coset representatives. The source's direct sum appears for finitely
  generated `σ` (only finitely many `q` then have `φ q ≠ 0`); for arbitrary
  smooth `σ` the statement uses the per-vector finiteness of
  `IsLocalIntertwinerFamily`, which is what the per-vector support condition
  of the first statement gives. This per-vector form is derived for this
  unit; it is not printed in the source.

No project errata apply: the Library at commit
`68eafb81a99c3822b04ca5395ee9df12df27f067` has no errata note for this
source.

## Relation to existing work

- `Langlands.Induction.compactInductionHomEquiv` in
  `Langlands.Representation.Induction.OpenAdjunction` identifies maps out of
  `c-Ind_H^G A` with `H`-maps `A → Res c-Ind_H^G B` (`T ↦ T ∘ unitMap`). The
  first statement is the further identification with kernels on `G`. It is
  stated with the same categories, so the published adjunction is the
  intended main input of its proof.
- Depth-zero use. The published
  `Langlands.BruhatTits.SpecialFibreQuotientData.depthZeroInduction` in
  `Langlands.BruhatTits.IntegralModels.DepthZeroInduction` is
  `(smoothCompactInduction k D.neutral.integralPoints).obj
  (Q.inflationSmoothRep hC σ)`, in `SmoothRep.{uk,u,u}`. Taking
  `H = D.neutral.integralPoints`, `uG = uV = u` and `A`, `B` two inflations,
  the first statement describes all maps between depth-zero compact
  inductions by kernels on `G(K)`, and the second and third by values at
  double cosets of `G^0(R)` when `G^0(R)` is compact. This is the "basic
  intertwining or double-coset theorem" that the Kaletha–Prasad source ledger
  (`notes/bruhat-tits/kp-source-ledger.md`, Section 13.2.6 consumer) lists as
  open. Openness and compactness of `D.neutral.integralPoints` are not
  established on supplied models. For the canonical topology of a local field,
  `localFieldDepthZeroInductionHomEquiv` derives openness from its premise
  `LocalFieldIntegralModel.CongruenceNeighborhoodBasisStatement`; compactness
  is a separate obligation. This unit records no depth-zero specialization as a Lean
  declaration and states nothing about irreducibility or supercuspidality.

## Proof obligations for the separate proofs

This section describes the intended proof routes. It is provenance only and is
not an input to the statements.

1. Kernel statement. Compose the published adjunction with the map
   `B' ↦ (g, v) ↦ B'(v)(g)` on `H`-maps `A → Res c-Ind B`. Covariance follows
   from left covariance of `B'(v)` and `H`-equivariance of `B'`. Conversely
   `v ↦ (g ↦ Φ g v)` is a compactly induced function: it is right invariant
   under the open subgroup of `H` (open in `G`) fixing `v`, and its projected
   support is finite, hence compact. Uniqueness is uniqueness in the
   adjunction, since `T` is determined by `T ∘ unitMap`.
2. Double-coset statement. Covariance at `s q` gives the local intertwining
   property. Distinct `q` give distinct right cosets `H (s q)`, which gives
   per-vector finiteness. Conversely define
   `Φ (h * s q * h') = τ h ∘ₗ φ q ∘ₗ σ h'`; well-definedness is the local
   intertwining property. For a fixed `v`, the orbit `σ(H) v` is finite
   (smoothness and compactness of `H`), so finitely many `q` contribute, and
   each double coset `H g H` is a finite union of right cosets because
   `H ∩ g⁻¹ H g` is open in the compact group `H`. Uniqueness follows from
   covariance.
3. Finite-type statement. If `v_1, …, v_n` generate `σ.asModule`, then
   `Φ g ≠ 0` gives some `h` and `i` with `Φ (g h) v_i ≠ 0`, so the support of
   `Φ` lies in the finitely many double cosets through the right cosets of
   the supports of `g ↦ Φ g v_i`. Conversely each double coset is a finite
   union of right cosets, as in 2.

## Imported constructions

`Langlands.Representation.Induction.OpenAdjunction` (imported) supplies
`smoothCompactInduction` and `unitFunction`, and through its imports
`Langlands.SmoothRep`, `SmoothRep.hom`, `Langlands.IsSmooth`, `eval` and
`quotientSupport`. `Mathlib.GroupTheory.DoubleCoset` (imported) supplies
`DoubleCoset.Quotient` and `DoubleCoset.mk`. Mathlib supplies
`Representation.asModule` and `MonoidAlgebra`. This file introduces only the
two predicates and the four propositions; every imported Lean/Markdown pair is
unchanged.

## Development check

The module compiled in environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`
with no errors or warnings. Declaration inspection of each of the four
propositions and the two predicates reported `statement_returns_prop: true`.
The axioms were exactly `propext`, `Classical.choice` and `Quot.sound`, except
for `IsLocalIntertwinerFamily`, which uses only `propext` and `Quot.sound`.
The entry declaration has level parameters `uR`, `uG`, `uV` and `uW`. This is
development evidence; independent semantic review and publication are
separate.
