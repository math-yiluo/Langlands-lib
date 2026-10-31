# A trivialization of the Mumford family along `[n]` with equal kernel restrictions

Module `Langlands.AlgebraicGeometry.Picard.MumfordAlternationTrivialization`, namespace
`Langlands.AbelianScheme`.

This module proves the geometric input `MumfordKernelPointTrivialization` of the published
reduction `Langlands.AlgebraicGeometry.Picard.MumfordFiniteWeilAlternationReduction`. It does
so for every point `x` of `A[n]`, whenever the Mumford map of the actual line bundle underlies
a homomorphism `lam : A ⟶ A^∨`. Its provenance is internal: it is not a step of the source
argument (EGM, Chapter XI, (11.19)–(11.22), which uses theta groups). The argument
evaluates trivializations at sections and uses the constancy of global functions on `T ×_S A`.
It uses the transport calculus of `Langlands.AlgebraicGeometry.Modules.PullbackTransport`.
All results are proved, with only the standard axioms.

## Notation

`Λ = mumfordFamilyOfLineBundle preservation A L B evaluationB M evaluation` is the published
rigidified Mumford family on `Z = A ×_S A`. Its first factor is the parameter `a`, and it is
rigidified along `ε = mumfordSection A`, `a ↦ (a, 0)`. `C` is its carrier. Definitionally
(`mumfordBundle_forget` is `rfl`) it is `(add^* N ⊗ pr₁^* M) ⊗ pr₂^* M`, where `N` is the
normalized line bundle `LineBundle.normalize … L B evaluationB` and `evaluation : N ⊗ M ≅ O`. `[n] = multiplication A (n : ℤ)` and `nA` is its underlying
scheme map. For a test object `T` and `x : T ⟶ A[n]`, `x̄ = x ≫ kernelι` is the
point of `A` and `Y = T ×_S A`. The following maps are used:

| Lean | map |
| --- | --- |
| `pr = (relativeProjection A.X.hom).app T` | `Y → T`, `(t, b) ↦ t` |
| `e = (relativeSection …).app T` | `T → Y`, `t ↦ (t, 0)` |
| `xs = e ≫ kernelShear [n] (𝟙 T) x` | `T → Y`, `t ↦ (t, x̄ t)` |
| `p = (homFamilySpaceMap [n]).app T` | `Y → Y`, `(t, b) ↦ (t, n b)` |
| `mx = (relativeSpace A.X.hom).map x̄` | `Y → Z`, `(t, b) ↦ (x̄ t, b)` |
| `m1 = (relativeSpace A.X.hom).map 1` | `Y → Z`, `(t, b) ↦ (0, b)` |
| `hfs = (homFamilySpaceMap [n]).app A.X` | `Z → Z`, `(a, b) ↦ (a, n b)` |
| `mn = (relativeSpace A.X.hom).map nA` | `Z → Z`, `(a, b) ↦ (n a, b)` |
| `mumfordSwap A` | `Z → Z`, `(a, b) ↦ (b, a)` |
| `mumfordDiagonal A T` | `Y → Z`, `(t, b) ↦ (b, b)` |
| `pullback.snd T.hom A.X.hom` | `Y → A`, `(t, b) ↦ b` |
| `x̄.left`, `(1 : T ⟶ A.X).left` | `T → A`, `t ↦ x̄ t`, `t ↦ 0` |

The module `mumfordKernelPointModule … n x` of the reduction is `mx^* C`.

## Section `Core`

`transport_eq_of_constancy` is the comparison argument with all maps as variables. Its data
are the following.

- A module `C` on `Z` and `pr : Y ⟶ X` with `pr.appTop` an isomorphism.
- Maps `p, mx, m1, d, sn, e, xs, ε, hfs, mn, sw, xl, u0`.
- An isomorphism `R1 : ε^* O ⟶ ε^* C` and a morphism `Ψ : hfs^* C ⟶ mn^* C`.
- An isomorphism `τ : (𝟙 Z)^* C ⟶ sw^* C` and a morphism `R2 : m1^* C ⟶ m1^* O`.
- Rank-one hypotheses `hC` for `(d ≫ hfs)^* C` and `hO` for `(sn ≫ ε)^* O`.
- The listed equations between the maps, e.g. `e ≫ pr = 𝟙`, `xs ≫ pr = 𝟙`,
  `mx ≫ hfs = p ≫ mx`, `mx ≫ mn = m1` and `(d ≫ hfs) ≫ sw = d ≫ mn`.

It also takes three compatibilities, all with `transport` and `unitTransfer`:

- `F1x`: `Ψ` respects `R1` at `xl ≫ ε`.
- `F1u`: `Ψ` respects `R1` at `u0 ≫ ε`.
- `F2`: `R2` inverts `R1` at `u0 ≫ ε`.

Let `α' = transport mx Ψ ≫ R2 : (p ≫ mx)^* C ⟶ m1^* O`. The conclusion is
`transport e α' ≫ unitTransfer (u0 ≫ ε) (xs ≫ m1) = transport xs α'`.

Proof. `exists_transport_eq_smul` gives two constants `c1`, `c2 : Γ(X, ⊤)`:

- `c2` relates `transport d Ψ` and `transport (d ≫ hfs) τ` on `Y`.
- `c1` relates `transport sn R1 ≫ transport (sn ≫ ε) τ ≫ R2` and `unitTransfer (sn ≫ ε) m1`.

Specializing both along the sections `e` and `xs` gives four identities. The transports are
simplified with `transport_comp`, `transport_transport_eq` and `transport_unitTransfer`. At
`e`, `F1u` and `F2` give `(c2 * c1) • 𝟙 = 𝟙` on `(u0 ≫ ε)^* O`. At `xs`, `F1x` and `F2` give
`transport xl R1 ≫ transport xs α' = (c2 * c1) • unitTransfer _ _`, hence `= unitTransfer _ _`.
The same composite with `transport e α'` is computed with `F1x` and `F2`. Cancelling the
isomorphism `transport xl R1` gives the conclusion.

## Section `Geometry`

- `mumfordSwap A`: the exchange of the two factors of `A ×_S A`, with `mumfordSwap_fst`,
  `mumfordSwap_snd`.
- `mumfordSwap_addition`: `mumfordSwap A ≫ mumfordAddition A = mumfordAddition A`. This
  follows from commutativity of the group law (`MonObj.comp_mul`, `mul_comm`).
- `mumfordSection_fst`, `mumfordSection_snd`: the components of `ε` are `𝟙` and
  `A.X.hom ≫ unitSection A`.
- `mumfordDiagonal A T`: the map `(t, b) ↦ (b, b)`, with `mumfordDiagonal_fst`,
  `mumfordDiagonal_snd`.
- `unitPoint_left_comp_unitSection`, `relativeSection_map` (naturality of the unit section
  in the parameter), `mumfordSection_homFamilySpaceMap`, `mumfordSection_swap`.
- `kernelPoint_multiplication`, `kernelPoint_multiplication_left`: `x̄ ≫ nA = 1`, from
  `GroupScheme.kernelPointsEquiv`. `unitPoint_multiplication_left`: `1 ≫ nA = 1`.
- `kernelShearSection_eq`: `xs` is the point `(𝟙, x̄.left)` of `T ×_S A`. This is the Library's
  `relativeSection_kernelShear`.

## Section `Points`

These are the equations of `transport_eq_of_constancy` for the concrete maps of the table,
stated exactly in the form the core theorem uses. Each is proved by `pullback.hom_ext` and
the component lemmas above:

`kernelShearSection_projection`, `kernelShearSection_homFamilySpaceMap`,
`kernelPoint_map_homFamilySpaceMap`, `kernelPoint_map_multiplication`,
`kernelShearSection_diagonal`, `kernelShearSection_snd`,
`kernelShearSection_map_homFamilySpaceMap`, `unitSection_map_homFamilySpaceMap`,
`kernelPoint_mumfordSection_multiplication`, `kernelPoint_mumfordSection_swap`,
`unitPoint_mumfordSection_multiplication`, `unitPoint_mumfordSection_swap`,
`unitSection_mumfordDiagonal`, `unitSection_snd`, `mumfordDiagonal_homFamilySpaceMap_swap`,
`mumfordSection_snd_swap`.

## Section `Swap`

- `swapTensorIso preservation sw add fst snd hadd hfst hsnd P M` constructs an isomorphism
  `(add^* P ⊗ fst^* M) ⊗ snd^* M ≅ sw^* ((add^* P ⊗ fst^* M) ⊗ snd^* M)`. It applies when
  `sw ≫ add = add`, `sw ≫ fst = snd` and `sw ≫ snd = fst`. It is built from the tensor
  associator and symmetry, the comparisons `compIso`, and the inverse of the pullback–tensor
  comparison of `sw`. The comparison is invertible by the constructor hypothesis
  `preservation`.
- `mumfordSwapCarrierIso`: the resulting isomorphism `(𝟙 Z)^* C ≅ (mumfordSwap A)^* C` for the
  carrier of `mumfordBundle`. It is used as `τ`; only its existence matters.

## Section `Main`

The variables are those of the reduction module (the inputs of the target statement).
`DA` denotes `dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
stability composition unitCoherence associativity comparison symmetry`.

- `mumfordMultiplicationPullback_nonempty lam hlam n`: let `lam : A ⟶ DA` with
  `(groupHom lam).hom.hom = φ`, where `φ = mumfordSchemeMapOfLineBundle …`. Then there is an
  isomorphism of rigidified families
  `(homFamilyPullback [n] A.X).obj Λ ≅ (RigidifiedLineBundle.relativePullback … nA).obj Λ`.

  Proof. First, `φ ≫ dualSchemeMap homPicardZeroPullback [n] hA hA = nA ≫ φ`. Over `S`,
  the dual map of `[n]` is multiplication by `n` on `DA`
  (`relativeDualAbelianSchemeMap_multiplication`), and `lam` commutes with multiplication by
  `n` (`multiplication_comp_hom`). The isomorphism is the composite of:
  - `mumfordSchemeMapOfLineBundlePullbackIso` (`Λ` is the Poincaré pullback along `φ`);
  - `dualPointFamily_dualSchemeMap_nonempty` (the `[n]`-pullback of the Poincaré pullback
    along `φ` is the Poincaré pullback along `φ ≫ dualSchemeMap [n]`);
  - `eqToIso` of the equation above;
  - `dualPointFamilyPullbackIso` and `mumfordSchemeMapOfLineBundlePullbackIso` again.

- `mumfordKernelPointTrivialization_of_hom lam hlam n x` (main result): for `lam`, `hlam` as
  above, every `n : ℕ`, every `T : Over S` and every `x : T ⟶ A[n]`,
  `MumfordKernelPointTrivialization preservation A L B evaluationB M evaluation n x` holds. It
  is checked with `set_option maxHeartbeats 2000000`.

  Proof. Apply `transport_eq_of_constancy` with:
  - `C` the carrier of `Λ`, and `pr`, `p`, `mx`, `m1`, `d = mumfordDiagonal A T`, `sn = pr₂`,
    `e`, `xs`, `ε`, `hfs`, `mn`, `sw = mumfordSwap A`, `xl = x̄.left`, `u0 = 1.left` as in the
    table;
  - `R1 = sectionMap Λ.obj`;
  - `Ψ` the carrier morphism of the isomorphism of `mumfordMultiplicationPullback_nonempty`;
  - `τ = mumfordSwapCarrierIso`;
  - `R2 = Φ0 ≫ (pullbackUnitIso m1).inv`, with `Φ0` the carrier morphism of the published
    rigidified trivialization `mumfordZeroParameterIso` at the zero parameter.

  The remaining inputs are supplied as follows:
  - `pr.appTop` is an isomorphism by the Library's `universalGlobalFunctions A T`.
  - The rank-one hypotheses are `Λ.property.pullback _` and
    `(LineBundle.trivial _).property.pullback _`.
  - `F1x` and `F1u` are `transport_sectionMap_comp_of_hom_comp` along `x̄.left` and `1.left`.
    They use that the isomorphism defining `Ψ` is a rigidified isomorphism.
  - `F2` is `transport_sectionMap_comp_of_trivial` for `mumfordZeroParameterIso`.

  `equalCompositeUnitAut_eq_refl_of_transport` turns the conclusion into the required
  equation `equalCompositeUnitAut p e xs _ α = Iso.refl _`, where
  `α = compIso p mx (p ≫ mx) rfl C ≪≫ asIso α' ≪≫ pullbackUnitIso m1` and
  `α' = transport mx Ψ ≫ R2`.
