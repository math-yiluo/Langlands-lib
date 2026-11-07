# Canonical lattice comparison on the separate geometric coefficient covers

Author: Worker 57.

This internal construction compares the associated systems of the two canonical
Harris lattices constructed independently at nested small CM levels `V ≤ U`.
It uses their actual common coefficient kernels to construct two changes of
covers. Each change of covers retains its coefficient system. Composing these
isomorphisms with the actual descended lattice inclusion gives a morphism from
the original system at `V` to the system with the original `U` coefficients on
the coarse intersection covers over `V`.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact inputs and retained premises

The arithmetic inputs are totally real and CM number fields `E` and `F`,
respectively, with `F` totally complex, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has its `E`, `F` and rational algebra
structures and scalar towers `E → F → A`, `ℚ → E → A`, and `ℚ → F → A`.
Fix `n : ℕ` and `D : CentralSimpleUnitaryData E F A n`. A further CM number
field `L` satisfies `IsQuadraticExtension ℚ L` and has an algebra structure
on `F`. Fix `τ₀ : L →+* ℂ` and the original charts
`C : HarrisSignatureCharts D.toSecondKindInvolution n
(harrisCMSection E (algebraMap L F) τ₀)`.

The exact scheme tower retains the named premises
`pullbackTensorComparisonIsIsoStatement`,
`PullbackTensorCompositionStatement`, `PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`, `PicardZeroPullbackStatement`,
`MumfordBundlePicardZeroStatement`, `PicardZeroUniversalBaseChangeStatement`,
`DualAbelianBaseChangeNaturalityStatement`, `PolarizationBaseChangeStatement`,
`RelativeFiniteWeilTransitionStatement`,
`Global.RationalProfiniteIntegerAdeleComparison`, and
`TorsionFiniteEtaleStatement`. Fix
`q : CMRepresentabilityStatement ...` for exactly these data and premises.
Write `Sbar = cmGeometricSchemeTower ... q`. It is the existing base change
of the represented CM scheme tower from `Spec F` to
`Spec (AlgebraicClosure F)`, using the same chosen representations of the
exact constructed CM class presheaves at every level. Put `X_V = Sbar(V)`.

Fix `U V : SmallCMLevel D` and `hVU : V.obj.subgroup ≤ U.obj.subgroup`.
The coefficient data additionally retain `Module.Finite ℚ A`, a number field
`K`, a finite-dimensional `K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
a rational finite place `p`, and `m : ℕ` with `hm : m ≠ 0`. The scalar ring
throughout is `R = HarrisCoefficientIntegers K p`.

The canonical lattices `Λ_V` and `Λ_U` are those constructed separately at
`CompactOpenLevel.inverseOpposite V.obj` and
`CompactOpenLevel.inverseOpposite U.obj` in the same ambient tensor module.
Their original power quotients, all exponent reductions and the original
inverse-unop coefficient actions are retained. Write these full coefficient
functors as `M^V` and `M^U`.

The small-etale covers use the explicit premises
`RelativeDualSchemeExistenceStatement`,
`RelativeDualSchemeGeometryStatement`, and
`hRigid : CMGeometricCoarseRigidity ... V.obj`. The last predicate has the
original signature, tensor, Picard-zero, Weil, adelic and torsion arguments
shown in Lean; `q`, `dualityNaturality` and `polarizationStability` are not
additional arguments of that predicate. Rigidity at `U` is not required by
any declaration of this unit. The imported normal-torsor constructions use
the published dominant-unramified-etale proof; the other named premises
remain explicit. No desired cover comparison or coefficient map is supplied
as a premise.

## Actual cover maps and actions

Let `V_k` and `U_k` denote the original coefficient kernel levels for `Λ_V`
and `Λ_U`, and put

\[
T_k=V\cap U_k,\qquad N_k=V_k\cap T_k.
\]

The arithmetic common-kernel construction proves that these are literal
small-level intersections, normal inside `V`, and constructs their finite
residual groups

\[
G^V_k=V/(V_k\operatorname{.subgroupOf}V),\quad
H_k=V/(T_k\operatorname{.subgroupOf}V),\quad
Q_k=V/(N_k\operatorname{.subgroupOf}V).
\]

Its natural quotient maps `α_k : Q_k → G^V_k` and `β_k : Q_k → H_k`
send the class of `g ∈ V` to the class of that same `g`. The original own,
coarse and common small-etale diagrams over `X_V` have covers

\[
Y_k=Sbar(V_k),\qquad Z_k=Sbar(T_k),\qquad C_k=Sbar(N_k).
\]

They carry the original inverse-right normal deck actions and the original
geometric forgetting maps at every exponent. Their already constructed
finite geometric torsor properties are reused for the exact same objects,
structure maps and actions.

For `s = Own` and `s = Coarse`, the following declarations form two parallel
constructions. In the first column of the construction below, the target
cover is `Y_k`, the group map is `α_k`, and the coefficients are `M^V_k`.
For the second construction, the target cover is `Z_k`, the group map is
`β_k`, and the coefficients are `M^U_k` with their original action restricted
to `V`.

- `cmHarrisGeometricLatticeCommonOwnCoverMap` and
  `cmHarrisGeometricLatticeCommonCoarseCoverMap` are the actual maps
  `a_k : C_k → Y_k` and `b_k : C_k → Z_k` in `X_V.Etale`. They use
  `Sbar.map (smallCMInclusion D ...)` for the proved inclusions
  `N_k ≤ V_k` and `N_k ≤ T_k`. Composition of these original inclusions
  proves the required over-category equations. Their `left` lemmas
  identify the underlying scheme maps by reflexivity.
- Their `CoverMap_naturality` theorems assert, for every `f : i ⟶ j` in
  `ℕᵒᵖ`, `c_f ; a_j = a_i ; y_f` and `c_f ; b_j = b_i ; z_f`.
  The proof uses over-category extensionality, explicitly identifies each
  exponent map with its original inclusion, and applies functoriality and
  `smallCMInclusion_trans` to both composites.
- Their `ActionMap` declarations have these same maps as underlying maps
  and are equivariant through `α_k` and `β_k`, respectively. Quotient
  induction reduces equivariance to the same representative `g ∈ V`.
  `smallCMNormalInverseArrow_inclusion` and functoriality of `Sbar` then
  prove the square for the original inverse-right deck maps.

No normality of `V` in `U` is used. Every exponent, including zero, occurs.

## Associated systems and changes of covers

Put `J = Scheme.smallEtaleTopology X_V`. Write `L(B,M)` for the existing
associated invariant sheaf on a cover action `B` with coefficient action `M`.
The original and common systems used here are exactly:

| Notation | Lean definition | Component |
| --- | --- | --- |
| `F_V` | `cmHarrisGeometricAssociatedCoefficientSystem` at `V` | `L(Y_k,M^V_k)` |
| `F_U` | `cmHarrisGeometricCoarseAssociatedSystem` | `L(Z_k,M^U_k)` |
| `F_C^V` | `cmHarrisGeometricLatticeCommonOwnSystem` | `L(C_k,res_α M^V_k)` |
| `F_C^U` | `cmHarrisGeometricLatticeCommonOriginalSystem` | `L(C_k,res_β M^U_k)` |

These are actual functors from `ℕᵒᵖ` to `Sheaf J (ModuleCat R)`.
Their transitions are the original coefficient reductions followed by the
inverse of the proved comparison of covers, as constructed by
`etaleAssociatedVaryingSystem`.

`cmHarrisGeometricLatticeCommonOwnAssociatedComparison k` constructs
`A_k : (F_V)_k → (F_C^V)_k`. Its coarse analogue constructs
`B_k : (F_U)_k → (F_C^U)_k`. Each is `etaleCrossCoverMap` for the actual
quotient map and equivariant cover map above, with the identity on the
restricted original coefficient action. The two `AssociatedComparison_isIso`
theorems apply `etaleAssociatedCoverComparison` to the existing exact finite
geometric torsors. This step changes the cover while retaining coefficients.
It requires no claim about invertibility of the lattice inclusion.

Write `e^Y_k`, `e^Z_k`, `e^{C,V}_k` and `e^{C,U}_k` for the canonical
invariant inclusions into the product sheaves of their respective constant
coefficient sheaves. The two `AssociatedComparison_inclusion` theorems are
`etaleCrossCoverMap_identity_inclusion` and give the exact normalizations

\[
 A_k\,;\,e^{C,V}_k=e^Y_k\,;\,\operatorname{cp}(a_k,M^V_k),\qquad
 B_k\,;\,e^{C,U}_k=e^Z_k\,;\,\operatorname{cp}(b_k,M^U_k).
\]

Here `cp` is the existing `coverPullback`. Thus both maps keep the original
coefficient and pull the actual cover coordinate.

The two `AssociatedComparison_naturality` theorems prove

\[
 t_V(f)\,;\,A_j=A_i\,;\,t_{C,V}(f),\qquad
 t_U(f)\,;\,B_j=B_i\,;\,t_{C,U}(f).
\]

For either side, `etaleAssociatedTransition_hom_ext` detects equality after
the common invariant inclusion and pullback along `c_f`. Substituting the
comparison normalization and the original transition-inclusion equations
reduces the claim to the actual cover square. `coverPullback_comp` transports
that square, and `coverPullback_natural` moves the original coefficient
reduction past the remaining cover pullback. This proves naturality with
all original exponent reductions, rather than only component invertibility.

`cmHarrisGeometricLatticeCommonOwnAssociatedCoverIso` and
`cmHarrisGeometricLatticeCommonCoarseAssociatedCoverIso` assemble these maps
with `NatIso.ofComponents` into `A : F_V ≅ F_C^V` and
`B : F_U ≅ F_C^U`. Their `hom_app` lemmas are reflexive identifications
with `A_k` and `B_k`. Their `inv_transition` theorems give naturality of the
categorical inverses for every exponent arrow.

## The original lattice inclusion on the separate covers

Let `c : F_C^V → F_C^U` be exactly the imported
`cmHarrisGeometricLatticeCommonCoefficientInclusion`. This is association of
the actual inclusion `Λ_V ≤ Λ_U` on the common covers, with its original
coefficient class formula and every original exponent map.

The entry definition `cmHarrisGeometricLatticeCoefficientComparison` is

\[
 d:F_V\longrightarrow F_U,\qquad d=A.\mathrm{hom}\,;\,c\,;\,B.\mathrm{inv}.
\]

Its `app` theorem identifies each component with exactly these three legs.
Its `transition` theorem is the naturality equation
`t_V(f) ; d_j = d_i ; t_U(f)` for every `f : i ⟶ j` in `ℕᵒᵖ`.
Its `common` theorem gives

\[
 d\,;\,B.\mathrm{hom}=A.\mathrm{hom}\,;\,c.
\]

The proof unfolds this composite and cancels `B.inv ; B.hom` with the
isomorphism law. This equation identifies the transported comparison with
the same original descended coefficient inclusion on the common covers.

## Provenance and remaining scope

This is an internal deduction from
`HarrisTaylorCMGeometricLatticeComparison`,
`HarrisTaylorCMGeometricCoarseAssociatedSystem` and
`HarrisTaylorCMGeometricAssociatedSystem`. These direct imports supply the
literal common levels, the full coefficient diagrams and their actual
inclusion, the exact finite geometric torsors, and the original associated
systems. The original inclusion arrows construct the two new cover maps;
quotient induction proves their equivariance. The imported generic
associated-cover comparison proves component invertibility. The section
normalizations and the implemented argument above construct the required
whole-system isomorphisms and the transported lattice comparison. No new
external-literature assertion is introduced.

The output is a morphism of integral coefficient systems on the separate
original own and coarse covers over `X_V`. It does not assert injectivity
or invertibility of the reduced lattice map, equality of the two lattices,
or independence of arbitrary lattices or rational adic systems. Identifying
the coarse system with inverse image of the original system at `U` is a
separate composition and additionally uses the original rigidity premise at
`U`. Exact representability, the named moduli premises, arithmetic existence,
source comparison and canonical-model geometry remain explicit or unfinished
obligations of the containing task.
