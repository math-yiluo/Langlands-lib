# Unramified Galois actions on geometric CM torsion cohomology

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `HarrisCMCohomologyUnramifiedStatement`,
about Worker 57's étale cohomology of the geometric CM levels with torsion
coefficients. Fix a small CM level `U`, write `F̄ = AlgebraicClosure F` and
`X̄_U = X_U ×_{Spec F} Spec F̄`, and let `B_r` be the `r`-th stage of Worker
57's original stable-lattice torsion coefficient system pulled back to
`X̄_U`. Worker 57 constructs an action of `F̄ ≃ₐ[F] F̄` on every cohomology
module `H^d(X̄_U, B_r)`. The proposition says that there is one finite set
`S` of finite places of `F` such that for every degree `d`, every stage `r`
and every finite place `w ∉ S`, this action is unramified at `w`: the
inertia subgroup of the completion `F_w` acts trivially. The set `S` does not
depend on `d` or `r`. Unramifiedness is the predicate `IsUnramifiedAt` of the
published `Langlands.Shimura.DecompositionGroupAction`. Nothing is proved
here.

The published companion
[HarrisCMCohomology](../HarrisCMCohomology/Statement.md), by the same
author, states that the same modules are finite and that the same action is
smooth for the Krull topology.

## Objects

All arithmetic types live in `Type` (universe zero), as in Worker 57's
modules. The binders are copied from
`Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology`, as in the
companion. They are:

- number fields `E` (totally real) and `F` (totally complex CM, quadratic
  over `E`), the algebra `A` with its compatible `E`-, `F`- and
  `ℚ`-algebra structures, and `D : CentralSimpleUnitaryData E F A n`;
- an imaginary quadratic number field `L` with `[Algebra L F]`, an
  embedding `τ₀ : L →+* ℂ`, and the signature charts `C`;
- the named premises `preservation`, `composition`, `unitCoherence`,
  `associativity`, `comparison`, `symmetry`, `stability`, `square`,
  `universality`, `dualityNaturality`, `polarizationStability`,
  `compatibility`, `h : Global.RationalProfiniteIntegerAdeleComparison` and
  `htor : TorsionFiniteEtaleStatement.{0}`;
- the representability premise
  `q : CMRepresentabilityStatement D C ... h htor`;
- `U : SmallCMLevel D` and `[Module.Finite ℚ A]`;
- a number field `K`, a finite-dimensional `K`-vector space `W`, an
  algebraic representation
  `ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`, a
  rational finite place `p`, a natural number `m` with `hm : m ≠ 0`, and the
  premises `existence`, `geometry` and `hRigid` (coarse rigidity at `U.obj`);
- the instances
  `[HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X̄_U R)]` and
  `[HasDerivedCategory.{wR} (ModuleCat.{0} R)]`, which Worker 57's action
  needs. They fix sizes of localizations and do not change the module
  `H^d(X̄_U, B_r)`. The proposition has the universe parameters `wS` and
  `wR` of these instances.

### Proof status of the premises

The Lean definition keeps every premise as an explicit hypothesis, as Worker
57's modules do. That a premise is a parameter does not mean that it is
unproved. In Library commit `568f1cff4df2c51ba08b932716bf99235d0032c7`,
thirteen of the premise types have published proofs, so a user can pass these
theorems as the corresponding arguments. Check `5377f756` (see the checks
below) confirms that each theorem, at universe zero, has the premise type.

| Premise | Type | Library theorem | Module |
| --- | --- | --- | --- |
| `preservation` | `pullbackTensorComparisonIsIsoStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorProof` |
| `composition` | `PullbackTensorCompositionStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorComposition` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs` |
| `unitCoherence` | `PullbackTensorUnitCoherenceStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorUnitCoherence` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs` |
| `associativity` | `ExplicitPullbackTensorAssociativityStatement.{0}` | `Langlands.Scheme.Modules.explicitPullbackTensorAssociativity` | `Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs` |
| `comparison` | `TensorMonoidalLeftUnitorComparisonStatement.{0}` | `Langlands.Scheme.Modules.tensorMonoidalLeftUnitorComparison` | `Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs` |
| `symmetry` | `PullbackTensorSymmetryStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorSymmetry` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs` |
| `stability` | `PicardZeroPullbackStatement.{0}` | `Langlands.AbelianScheme.picardZeroPullback` | `Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof` |
| `universality` | `PicardZeroUniversalBaseChangeStatement.{0}` | `Langlands.AbelianScheme.picardZeroUniversalBaseChange` | `Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof` |
| `dualityNaturality` | `DualAbelianBaseChangeNaturalityStatement.{0}` | `Langlands.AbelianScheme.dualAbelianBaseChangeNaturality` | `Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof` |
| `polarizationStability` | `PolarizationBaseChangeStatement.{0}` | `Langlands.AbelianScheme.polarizationBaseChange` | `Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeProof` |
| `compatibility` | `RelativeFiniteWeilTransitionStatement.{0}` | `Langlands.AbelianScheme.relativeFiniteWeilTransition` | `Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionProof` |
| `h` | `Global.RationalProfiniteIntegerAdeleComparison` | `Langlands.Global.rationalProfiniteIntegerAdeleComparison` | `Langlands.Global.RationalProfiniteIntegerComparisonProof` |
| `htor` | `TorsionFiniteEtaleStatement.{0}` | `Langlands.AbelianScheme.torsionFiniteEtale` | `Langlands.AbelianScheme.TorsionFiniteEtale` |

These proof modules are not imported here. Five premises have no proof in
that commit: a search of its Lean sources found no theorem whose conclusion
is the premise type.

- `square : MumfordBundlePicardZeroStatement.{0}`. The Library derives it only
  conditionally. `Langlands.AbelianScheme.MumfordPicardZero.mumfordBundlePicardZero_of_cube`
  (module `Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction`)
  proves it from `FieldCubePullbackStatement` and
  `FieldLineBundleTrivialityStatement`. The second is proved
  (`Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality`). The first
  is derived only from the unproved `FieldCubeIsomorphismStatement`, by
  `Langlands.GroupScheme.fieldCubePullbackOfIsomorphism` (module
  `Langlands.AbelianScheme.FieldCubePullbackAssembly`).
- `q : CMRepresentabilityStatement ...`, representability of the CM moduli
  problem. Its division-algebra case is stated separately as
  `DivisionCMRepresentabilityStatement`, which is also unproved there.
- `existence : RelativeDualSchemeExistenceStatement.{0}` and
  `geometry : RelativeDualSchemeGeometryStatement.{0}`.
- `hRigid`, coarse rigidity at the level `U.obj`. This is a condition on the
  level, not a general theorem. The docstring of `CMGeometricCoarseRigidity`
  says that it "is not inferred from sufficiently small level", and every
  Library module that uses it takes it as a hypothesis.

Since `q` is unproved, the proposition is a statement about the objects that
any witness `q` produces. A proof must work for every such witness.

### Notation

As in the companion and Worker 57's Markdown:

- `X_U = (cmSchemeTower ... q).obj U`, the scheme chosen from `q`. The
  witness `q U` provides a smooth structure morphism `X_U ⟶ Spec F` and an
  `IsHProjective` witness for it
  (`HarrisTaylorCMRepresentabilityStatement`, fields `smooth` and
  `projective`).
- `X̄_U = (cmGeometricSchemeTower ... q).obj U`; by
  `cmGeometricSchemeTower_isPullback` it is the fibre product
  `X_U ×_{Spec F} Spec F̄`. Let `π : X̄_U ⟶ X_U` be the first projection.
- `R = HarrisCoefficientIntegers K p`, the product of the coefficient
  valuation rings `O_l` over the places `l` of `K` above `p`.
- `A_r = (cmHarrisCoefficientSystem ... q U ρ p m hm existence geometry
  hRigid).obj r`, a sheaf of `R`-modules on the small étale site of `X_U`,
  and `B_r = π^* A_r`, its inverse image under the Library's
  `EtaleInverseImage.inverseImage π R`.
- `H_d = EtaleDerivedSections.cohomology X̄_U R d`, the `d`-th right derived
  functor of global sections on sheaves of `R`-modules on the small étale
  site of `X̄_U` (Worker 13).
- `G = F̄ ≃ₐ[F] F̄`. For `σ ∈ G`, `g_σ : X̄_U ⟶ X̄_U` is the identity on the
  factor `X_U` times `Spec σ` on `Spec F̄`, and `Ψ_σ` is the canonical
  isomorphism `g_σ^* B_r ≅ B_r`.
- `cmHarrisGeometricGaloisCohomologyAction ... d : ℕᵒᵖ ⥤ Action (ModuleCat R) G`
  is Worker 57's action. Its object at `r` has underlying module
  `H_d(B_r)`, and `σ` acts by
  `cohomologyPullbackWithCoefficients g_σ R d (Ψ_σ.hom.app r)`: pullback
  along `g_σ` followed by `Ψ_σ`. The companion's Markdown explains this
  action in detail.

The predicate:

- `Global.FinitePlace F` is the Library's type of finite places of `F`, the
  height-one primes of the ring of integers.
- `DecompositionGroupAction.IsUnramifiedAt V w M`, for an object `M` of
  `Action V (Field.absoluteGaloisGroup F)`, says that every element of
  `localInertia w`, the kernel of the action of the absolute Galois group of
  the completion `F_w` on the residue field of its algebraic closure (Worker
  41's `Langlands.Galois.CompatibleFamily`), acts trivially on `M` after
  restriction to `Gal(F̄/F)` along Mathlib's chosen closure embedding. The
  published theorem `isUnramifiedAt_iff_along` shows that the condition does
  not depend on the closure embedding.
- Mathlib defines `Field.absoluteGaloisGroup F` as
  `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, with the same group
  structure. So Worker 57's action, an object of `Action (ModuleCat R) G`,
  is passed to `IsUnramifiedAt` without any conversion; Lean accepts it by
  definitional unfolding.

## The proposition

```lean
def HarrisCMCohomologyUnramifiedStatement : Prop :=
  ∃ S : Set (Global.FinitePlace F), S.Finite ∧
    ∀ (degree : ℕ) (r : ℕᵒᵖ) (w : Global.FinitePlace F), w ∉ S →
      DecompositionGroupAction.IsUnramifiedAt (ModuleCat.{0} Rcoeff) w
        ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition
          unitCoherence associativity comparison symmetry stability square universality
          dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
          existence geometry hRigid degree).obj r)
```

Here `Rcoeff` is local notation for `HarrisCoefficientIntegers K p`.

In words: there is a finite set `S` of finite places of `F` such that for
every degree `d`, every coefficient stage `r` and every finite place
`w ∉ S`, the inertia subgroup at `w` acts trivially on `H^d(X̄_U, B_r)`. The
set `S` comes before `d` and `r` in the quantifiers.

## Consequence for Frobenius elements

The test lemma `frobenius_eq_of_unramified` of check `5377f756` (below)
proves that the proposition gives a finite set `S` such that for every
degree, every stage, every finite place `w ∉ S` and every closure embedding
`ι` at `w`, every geometric Frobenius lift `g` at `w`
(`IsGeometricFrobeniusLift w g`) acts on `H^d(X̄_U, B_r)` by the single
endomorphism `DecompositionGroupAction.geometricFrobenius ... w M ι`. The
proof combines `isUnramifiedAt_iff_along` with the published
`geometricFrobenius_eq_of_lift`.

## Relation to other modules

- The published [HarrisCMCohomology](../HarrisCMCohomology/Statement.md)
  states finiteness and Krull smoothness for the same modules and action.
  The present statement is independent of it.
- The candidates `c1c7da7d-650b-424c-a2c5-a19a36cab4c0`
  (`GaloisCohomologyUnramifiedStatement`) and
  `13557424-c36b-4129-8ddd-01aa8d416fe0`
  (`GaloisCohomologyGoodReductionStatement`), by the same author, approved
  and not yet in Library `568f1cff`, state unramifiedness for Worker 13's
  `galoisCohomologyRep`. That object has constant coefficients on a scheme
  over a number field. It is not Worker 57's action on the CM levels:
  Worker 13 reports that no comparison between the two actions is available
  yet. So these statements do not apply here.
- `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology` (no Author
  line) restricts the Galois actions on the shrinking-level and prime-to-`m`
  colimit cohomology of the CM tower to decomposition groups. Its Frobenius
  lemma `cmPrimeToHeckeFrobenius_eq_of_lift` takes unramifiedness as a
  hypothesis. Those colimits over levels can be ramified at places dividing
  the levels, so no unramifiedness is stated for them here. The present
  statement is at one fixed level `U`.

## Why the statement is expected to hold

This argument is derived. It combines Library facts with the cited sources;
none of them states the proposition. Let `S` be the set of places of `F`
dividing `p N` for an integer `N ≥ 1` chosen in step 4. The argument uses
only that `q U` gives a smooth projective `X_U` with a universal class, and
Worker 57's construction of the coefficient system.

1. *The coefficient covers.* Fix a stage `k`. Worker 57's
   `HarrisTaylorCMCoefficientReduction` defines
   `V_k = cmHarrisCoefficientLevel ... k`, the sublevel of `U` cut out by
   `cmHarrisCongruenceKernel ... k`, the kernel of the action of `U` on the
   finite coefficient module `M_k` (`cmHarrisFiniteTorsionAction`). This
   kernel is normal (`cmHarrisCongruenceKernel_normal`) and open
   (`cmHarrisCongruenceKernel_isOpen`), and `M_k` is finite
   (`cmHarrisFiniteTorsionAction_finite`). By
   `mem_cmHarrisCongruenceKernel` membership is tested at the places of `K`
   above `p`. The adelic group acts on the coefficients through its component
   at `p` (docstring of `placeAction`, `Langlands.Shimura.Coefficients.Algebraic`).
   So `V_k` contains every element of `U` whose component at `p` is `1`.
   `M_k` is a finite `R`-module, and every prime number other than `p` is a
   unit in `R`, so `M_k` has `p`-power order.

   Worker 57's `HarrisTaylorCMCoefficientSystem.md` describes the cover:
   `Y_k`, the scheme of the tower at `V_k`, with the forgetful map
   `Y_k ⟶ X_U`, is a finite geometric torsor under the finite group
   `SmallCMResidualGroup D U V_k`, the quotient `U / V_k`. It is étale and
   covers the final object (`cmHarrisCoefficientEtaleDiagram_coversTop`).
   `A_k` is the sheaf associated with this torsor and the `U / V_k`-module
   `M_k` (`cmHarrisCoefficientSystem_obj`), and
   `cmHarrisCoefficientSystemTrivialization` identifies the restriction of
   `A_k` to `Y_k` with the constant sheaf `M_k`.

2. *Monodromy.* `X_U` is noetherian, so it has finitely many connected
   components `X_c`, which are open. Each is smooth over `F`, hence regular
   (Stacks 056S), normal (0569) and, being connected, integral (033O). By
   `q` and the presheaf `HarrisTaylorCMPolarizedDisconnectedPresheaf`, which
   is a product over connected components, `X_c` carries the universal
   class: an abelian scheme `A_c` (a representative of the isogeny class)
   with a level structure. Harris–Taylor III.1, p.91, define this level
   structure as a "`π_1(S,s)`-invariant `U`-orbit of isomorphisms
   `η : V ⊗ A^∞ → V A_s`". They also note that for normal `V ⊆ U` "the
   finite etale cover `X_V → X_U` is Galois with group `U/V`", which gives
   "a continuous homomorphism `π_1(X_U,x) → U`". Fix a geometric point `x̄`
   of `X_c` and write `u : π_1(X_c, x̄) ⟶ U` for this homomorphism, so that
   `γ ∘ η = η ∘ u(γ)` as maps `V ⊗ A^∞ → V A_x̄`. The Library records the same translation
   rule for frame coordinates (`harrisIntegralCMFrameEquiv_monodromy`,
   module `HarrisIntegralCMLevelMonodromy`). The fibre of `Y_k` at `x̄` is
   `U / V_k`, and `γ` acts on it by translation by `u(γ)`. Since `V_k` is
   normal, `γ` acts trivially on this fibre if and only if `u(γ) ∈ V_k`. Let
   `H_k = u^{-1}(V_k)`, the stabilizer of every point of this fibre. By
   SGA 1 V §7, `H_k` is the image of the fundamental group of each connected
   component of `Y_k ×_{X_U} X_c`. The restriction of `A_k` to such a
   component is constant, so `H_k` acts trivially on the fibre `M_k` of
   `A_k` at `x̄`.

3. *Control by `p`-power torsion.* Let `G_p` be the group of `ℚ_p`-points
   of the similitude group. It is a closed subgroup of `GL(V ⊗ ℚ_p)` (the
   similitude factor is determined by the action on `V`). Since `V_k` is
   open in the finite adelic group, its image under the projection to `G_p`
   is open. Choose a lattice `Λ ⊂ V ⊗ ℚ_p`. The subgroups
   `Γ_n = {g ∈ G_p : (g - 1) Λ ⊆ p^n Λ}` form a basis of neighbourhoods of
   `1`, so `Γ_n` lies in the image of `V_k` for some `n`. If `g ∈ U` has
   `p`-component in the image of `V_k`, then `g ∈ V_k`, because `V_k`
   contains all elements of `U` with trivial `p`-component (step 1). Choose
   `a, b` with `p^a T_p ⊆ η_p(Λ) ⊆ p^{-b} T_p`, where `T_p` is the Tate
   module of `A_x̄`. If `γ` acts trivially on `A_c[p^j](x̄) = T_p / p^j T_p`
   with `j = n + a + b`, then `(γ - 1) η_p(Λ) ⊆ p^n η_p(Λ)`. So
   `u(γ)_p ∈ Γ_n`, and therefore `u(γ) ∈ V_k`. Hence for every `k` there is
   a `j` such that every `γ` acting trivially on `A_c[p^j](x̄)` lies in
   `H_k`.

4. *Spreading out.* `Spec F` is the limit of the schemes
   `T_N = Spec O_F[1/N]`. By Stacks Lemma 32.10.1 (tag 01ZM), parts (1) to
   (3), and tags 0C0C and 081F, there are `N` and for each component a smooth
   proper `𝒳_c → T_N` with generic fibre `X_c`, and a smooth proper
   commutative group scheme `𝒜_c → 𝒳_c` that extends `A_c`. Part (1) gives
   the schemes, part (2) the multiplication, inverse and unit, and part (3)
   the group axioms and commutativity, each after enlarging `N`. `N` does
   not depend on `k` or `d`.

   *The fibres of `𝒜_c` are geometrically connected after enlarging `N`.*
   Let `f : 𝒜_c → 𝒳_c` be the structure map. Over `X_c` the fibres of `A_c`
   are proper, geometrically reduced (Stacks 056T) and geometrically
   connected, so their global functions are the residue fields (Stacks 0BUG)
   and `f_* O = O` over `X_c` (Stacks 0E62). On every affine open of
   `𝒳_c`, `f_* O` is the quasi-coherent sheaf of a finite module (Stacks
   Lemma 30.19.2, tag 02O3), so it is coherent. Since `X_c → 𝒳_c` is flat,
   flat base change (Stacks 02KH) identifies the restriction of `f_* O` to
   `X_c` with the direct image for `A_c`. The kernel and cokernel of
   `O → f_* O` are coherent, so their supports form a closed set that misses
   `X_c`. Its image in `T_N` is closed, as `𝒳_c → T_N` is proper, and does
   not contain the generic point. So it is a finite set of closed points.
   After enlarging `N`, `f_* O = O`, and the Stein factorization (Stacks
   Theorem 37.53.4, tag 03H0) shows that the fibres of `f` are geometrically
   connected. So `𝒜_c` is an abelian scheme.

   *Properties of the model.* `𝒳_c` is normal, since it is smooth over the
   normal scheme `T_N` (Stacks 033C). It is flat over `T_N`, so its generic
   points lie over the generic point of `T_N`, that is, in the irreducible
   `X_c`. So `𝒳_c` is irreducible, hence integral (033O). Let
   `𝒳'_c = 𝒳_c ×_{T_N} T'`, where `T' = Spec O_F[1/pN]`. Since `p` is
   invertible on `𝒳'_c`, `𝒜_c[p^j]` is finite étale over `𝒳'_c` for every
   `j` (Milne, Proposition 20.7).

5. *Descent of the coefficients.* By SGA 1 V Proposition 8.2, applied to the
   connected normal schemes `X_c` and `𝒳'_c` with the same function field,
   the map `π_1(X_c, x̄) → π_1(𝒳'_c, x̄)` is surjective. Let `Q_c` be its
   kernel. Elements of `Q_c` act trivially on the fibres of every finite
   étale cover of `X_c` that extends to `𝒳'_c` (SGA 1 V §7), in particular
   on every `A_c[p^j](x̄)`. By step 3, `Q_c ⊆ H_k` for every `k`. The sheaf
   `A_k` is locally constant with finite stalks, so it is represented by a
   finite étale `R`-module scheme over `X_U` (SGA 4 IX 2.2). By step 2,
   `Q_c` acts trivially on its fibre at `x̄`. By the equivalence of SGA 1 V
   §7, compatible with fibre products, it extends to a finite étale
   `R`-module scheme over `𝒳'_c`. So there is a locally constant
   constructible sheaf `𝒜_k` of `R`-modules on `𝒳' = ⊔_c 𝒳'_c` whose
   restriction to `X_U` is `A_k`. It is `p`-power torsion.

6. *Specialization.* `𝒳' → T'` is smooth and proper. By SGA 4 XV Théorème
   2.1 a smooth morphism is locally acyclic for the primes invertible on its
   source, which include `p`. By SGA 4 XVI Théorème 2.1, applied to the
   constructible, locally constant, `p`-power torsion sheaf `𝒜_k`, the
   sheaves `R^d f'_* 𝒜_k` on `T'` are constructible and locally constant,
   and their stalk at a geometric point `ȳ` is `H^d(𝒳'_ȳ, 𝒜_k)`. For the
   geometric point `Spec F̄ → T'` the geometric fibre is `X̄_U` and the
   restriction of `𝒜_k` is `π^* A_k = B_k`. The Library inverse image is left
   adjoint to the direct image, so it agrees with that of SGA 4. The
   cohomology of a sheaf of `R`-modules is that of its underlying abelian
   sheaf (SGA 4 V 4.1, 4.4 and 4.6, and Tôhoku §2.4, Remark 3), as in step 5
   of the companion's finiteness argument. The Lean `cohomologyPullback` is
   the pullback map of SGA 4: both are morphisms of δ-functors in the
   coefficient sheaf that agree in degree zero, and the source is a
   universal δ-functor (Tôhoku Proposition 2.2.1).

7. *Inertia acts trivially.* The argument is that of steps 4 and 5 for
   `GaloisCohomologyGoodReductionStatement` (candidate `13557424`), with
   `T'` in place of its base. For `σ ∈ Gal(F̄/F)`, `Spec σ` is an
   automorphism of the geometric point `Spec F̄ → T'`, and the identification
   of step 6 is natural in the geometric point. So the action of `σ` on the
   stalk `H^d(X̄_U, B_k)` is the pullback along `g_σ` followed by the
   canonical coefficient isomorphism, Worker 57's action, possibly with `σ`
   replaced by `σ⁻¹`. Such an inversion does not change which subgroup acts
   trivially. The stalk of the locally constant constructible sheaf
   `R^d f'_* 𝒜_k` is a `π_1(T')`-set (SGA 1 V §7, SGA 4 IX 2.2), so
   `Gal(F̄/F)` acts through `π_1(Spec F) → π_1(T')`. `T'` is connected,
   noetherian and normal, so by SGA 1 V Proposition 8.2 the kernel of this
   map corresponds to the composite of the finite extensions of `F` inside
   `F̄` that are unramified over `T'`. This composite is generated by finite
   Galois subextensions `L` unramified over `T'`. Let `w ∉ S`, let `ι` be a
   closure embedding at `w` and `g ∈ localInertia w`. Then `w` is a point of
   `T'`, and the extension `ι(L) F_w` of `F_w` is finite, Galois and
   unramified, so `g` fixes it pointwise. As `ι (σ x) = g (ι x)` for
   `σ = localRestriction w ι g` (`localRestriction_commutes`) and `ι` is
   injective, `σ` fixes `L`. So `σ` acts trivially on `H^d(X̄_U, B_k)`.

`S` is the set of places dividing `pN`. It is finite and depends neither on
the degree nor on the stage, which proves the proposition.

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), §5, printed p.313: "we will be considering λ-adic representations
σ of Gal(F̄/F) which are unramified at all but finitely many places and pure
of weight m". Theorem 5.7 there concerns the representation of
`Gal(F̄/F)` on `H^{n-1}(S_K(N), W)[π]`, the cohomology of a unitary Shimura
variety with coefficients in a coefficient system. Harris–Taylor (2001),
III.1-III.2, pp.89-97, construct these Shimura varieties and their
coefficient systems; Worker 57's construction follows them.

The proposition is the finite-level, torsion-coefficient input to such
`λ`-adic statements, for the Library's objects:

- Harris's `S_K(N)` and sheaves are not the Library's `X̄_U` and `B_r`;
  Worker 57's levels are the Harris–Taylor CM PEL levels, conditional on the
  premises above;
- the statement is at one fixed level `U` and for each coefficient stage
  `r`, with one exceptional set for all stages and degrees. The `λ`-adic
  representation, an inverse limit over `r`, is not constructed here;
- nothing is said about purity, Frobenius eigenvalues or Euler factors, or
  about which places lie in `S`.

| Lean | Source |
| --- | --- |
| `∃ S, S.Finite ∧ ∀ degree r w, w ∉ S → IsUnramifiedAt ...` | Harris 1999 §5, p.313, "unramified at all but finitely many places", for all torsion stages at once |
| `X̄_U`, `B_r`, the action of `F̄ ≃ₐ[F] F̄` | Harris–Taylor III.1-III.2, as constructed by Worker 57 |
| truth argument | Harris–Taylor III.1 p.91 (monodromy); Stacks 01ZM, 0C0C, 081F, 03H0 (model); SGA 1 V 8.2; SGA 4 XV 2.1 and XVI 2.1 |

## Scope

The statement does not cover:

- limits or colimits over levels `U`, ℓ-adic or rational coefficients, or
  the inverse limit over `r`;
- any description of `S` beyond its finiteness, such as the places of bad
  reduction;
- Frobenius eigenvalues, purity, Euler factors, or local-global
  compatibility, including Harris 1999 Theorem 5.7 itself;
- Hecke operators, compact supports, or intersection cohomology;
- a proof of any premise. The open premises `square`, `q`, `existence`,
  `geometry` and `hRigid` stay open, and the proved ones are not
  instantiated here.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`; §5,
  printed p.313 (PDF p.15), read in the text layer. Provenance only.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`: Harris–Taylor
  2001, PDF SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`
  (printed page = PDF page - 8); III.1, printed p.91 (PDF p.99), read in the
  text layer. Truth argument (step 2) and provenance.
- `stacks-limits-of-schemes-a04446e5`: Stacks Project, Chapter 32 Limits of
  Schemes, `limits.tex` at commit
  `a04446e57ec1fbc252a871afcec7752fb2807b14` (file SHA-256
  `dccddc3622ebad21dd6219ea50b157fcf20c574e82b9e920b7f4d1ed127e0aa4`);
  Lemma 32.10.1 (tag 01ZM, label `lemma-descend-finite-presentation`,
  line 2370) parts (1) to (3), tag 0C0C (label `lemma-descend-smooth`,
  line 1931) and tag 081F (label `lemma-eventually-proper`, line 3265).
  Step 4.
- `stacks-smooth-connected-integral-2026-10-24`: Stacks tags 056S, 0569 and
  033O, original HTML pages. Steps 2 and 4.
- `stacks-global-functions-field-and-fibre-criterion-2026-10-23`: Stacks
  tags 0BUG, 056T and 0E62, original HTML pages. Step 4.
- `stacks-very-ampleness-support-2026-10-29`: Stacks Lemma 30.19.2
  (tag 02O3), file `02O3.html`, SHA-256
  `ce0b5617576dbec3ff067a98e5f6b4316a4bdc98264f9efe4e7a2af3526bfcf4`.
  Step 4.
- `stacks-flat-base-change-projection-formula-2026-11-02`: Stacks Lemma
  30.5.2 (tag 02KH). Step 4.
- `stacks-03h0-stein-factorization-2026-11-07`: Stacks Theorem 37.53.4
  (tag 03H0), file `03H0.html`, SHA-256
  `dac42f128e663313c962f5a814bd8b7623d433acef47513a8630ca60283bfc45`, with
  the comments on Section 37.53 (`03GX.html`), none of which affects the
  theorem. Step 4.
- `stacks-033c-smooth-over-normal-2026-11-07`: Stacks Lemma 10.163.9
  (tag 033C). Step 4.
- `milne-abelian-varieties-1986-author-2022`: J. S. Milne, *Abelian
  Varieties*, author revision of 2 January 2022, PDF SHA-256
  `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`
  (printed page = PDF page); Proposition 20.7, p.44. Step 4.
- `sga1-arxiv-math-0206203v2`: SGA 1, recomposed edition (arXiv
  math/0206203v2), PDF SHA-256
  `8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`
  (printed page = PDF page - 16 in Exposé V); Exposé V §7 and Proposition
  8.2, printed p.117 (PDF p.133), read in the text layer. Steps 2, 5 and 7.
- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4 Tome 3, Lecture Notes
  in Mathematics 305, original scan, PDF SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`
  (PDF page = printed page + 3), read on rendered page images: Exposé IX
  (Artin) 2.2, printed p.8; Exposé XV (Artin) Théorème 2.1, printed p.192;
  Exposé XVI (Artin) Théorème 2.1, printed p.213. Steps 5 to 7.
- `sga4-1972-tome2-verdier-v-original-scan`: SGA 4 Tome 2, Lecture Notes in
  Mathematics 270, original scan, PDF SHA-256
  `7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`;
  Exposé V (Verdier) 4.1, 4.4 and 4.6, printed pp.28-31. Step 6.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), SHA-256
  `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`;
  Proposition 2.2.1, printed p.141 (PDF p.23), and §2.4, Remark 3 after
  Theorem 2.4.1, printed p.148 (PDF p.30). Step 6.

## Formal dependencies and checks

Direct project imports, in Library commit
`568f1cff4df2c51ba08b932716bf99235d0032c7` and the workspace:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology` | Worker 57 | `e7f01f64e60e606662cb0adeebb1c8c49573b552311129ee4ff8c5bbb3213f27` | `66fae2ad97f30b2658051f14135ae87e7e339b1455f95fcda9ff597be7ec9cde` |
| `Langlands.Shimura.DecompositionGroupAction` | no Author line | `9a5ae46b57a07e743845d7980e90a00a4db618f2e14fee54dc16f303e91cda43` | `317291d8aad940a67f73157ad08598516b9d3cb5731f195dd524085ac58b4cfc` |

Through these imports the module uses Worker 13's `EtaleDerivedSections`,
the Library's `EtaleInverseImage`, and Worker 41's
`Langlands.Galois.ClosureRestriction` (`chosenClosureEmbedding`) and
`Langlands.Galois.CompatibleFamily` (`localInertia`). The truth argument
also cites `HarrisTaylorCMCoefficientReduction`,
`HarrisTaylorCMCoefficientSystem`, `HarrisTaylorCMCoefficientSchemes`,
`HarrisTaylorCMPolarizedDisconnectedPresheaf` and
`HarrisIntegralCMLevelMonodromy`. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Checks against Library `568f1cff`. None reported errors or warnings.

- `5377f756-b049-44a0-8d48-ca0bf23024d8` compiled the file from a draft
  directory together with two test files, neither part of the candidate:
  `Langlands/Inspect/HarrisCMCohomologyUnramifiedPrint.lean` (SHA-256
  `be228c0d647bd14b0213d5fdd7c23293080dfcd09ec88d12497b3c2fca89cf3f`) and
  `Langlands/Inspect/CMCohomologyUnramifiedPremises.lean` (SHA-256
  `923a7876ed63d4e84188bc988c35e1412f6be645410afcde59604fef282c6c6b`). It
  printed `HarrisCMCohomologyUnramifiedStatement` with universes: a
  `Prop`-valued definition with the universe parameters `wS` and `wR`. It
  proved `frobenius_eq_of_unramified`. For each of the thirteen proved
  premises in the table above, an `example` with the premise type at
  universe zero is closed by the cited theorem. `#print axioms` shows that
  `frobenius_eq_of_unramified` and the thirteen theorems depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
- `066927d8-ccc8-401e-b0bf-267ddc9d216b` built the same Lean file (SHA-256
  `1c0576c7d6f3a1117a2507c2bf4d1e7c626d0055e557cf03ba533b2a77e37e51`) with
  Lake from the workspace and inspected
  `HarrisCMCohomologyUnramifiedStatement`: a `Prop`-valued definition with
  universe parameters `wS` and `wR`, depending only on `propext`,
  `Classical.choice` and `Quot.sound` (type hash
  `81a08f9911f781791b46d56969d5cb01e709441312d8f37a0cd7f0e42fa48daf`).

This establishes a well-formed statement. It does not prove it.
