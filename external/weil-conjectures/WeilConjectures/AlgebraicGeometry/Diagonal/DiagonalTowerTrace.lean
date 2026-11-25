/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSources
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceResultExistence
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegrationSystems
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleFaithful

/-! # The completed projective-line trace
Source: blueprint main-20261015, sk-prop-diagonal-tower-trace, proof steps 1--8
(blueprint: proposition-ell-adic-cycle-class-diagonal).

## Main declarations
- `diagonalTraceFirstModel` and `diagonalTraceSecondModel` specify both product projections.
- `DiagonalTrace.NormalizedSource` and `DiagonalTrace.SupportedSource` fix the supported source.
- `diagonalTower_trace` states the three completed traces and both integration identities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u w v a b c va vb vc wa wb wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

open DiagonalTrace

set_option linter.unusedVariables false in
/-- The strict unit/section splitting defines the completed projective-line trace;
its finite reductions are the torsion traces and the two diagonal integrals are one.

Source: blueprint main-20261015, chap-Construction-of-f,
sk-prop-diagonal-tower-trace.md, clauses 1--2
(blueprint: proposition-ell-adic-cycle-class-diagonal).

Proof plan from the DAG:

1. Put $P=\mathbf P^1_Y$. The first-Chern-class construction of [proposition-sp-tower-geometric](2),
specialized to $E=\mathbf Q_\ell$ and $L=\mathcal O_P(1)$, supplies a single morphism of
varying-coefficient derived systems, not merely a compatible family in the individual derived
categories. Use its adjoint and the unit to form $b_\bullet=(1,h_\bullet)$. For the standard
section $s=[1:0]:Y\hookrightarrow P$, its image has equations $t_0=x_1/x_0$ on $U_0=(x_0\ne0)$
and $t_1=1$ on $U_1=(x_1\ne0)$. The generators $e_i=t_i^{-1}$ of its Cartier line bundle satisfy
$e_0=(x_0/x_1)e_1$ on the overlap, which is the transition of $\mathcal O_P(1)$. Thus $\mathcal
O_P(s(Y))=\mathcal O_P(1)$. Uses: proposition-sp-tower-geometric,
lem-pur-coefficient-system-derived-comparison, lemma-cohomology-projective-line-trace.

2. For each $n\geq1$, apply [lemma-cycle-class-cartier-divisor] with $Z=P$, $D=s(Y)$, $r=n$, and
$R=\Lambda=\mathbf Z/\ell^n\mathbf Z$. This is a finite commutative $R$-algebra; $\ell$ is
invertible on $P$. The section is effective Cartier: $x_1/x_0$ is the polynomial coordinate on
$U_0$, hence a non-zero-divisor over any base ring, and its ideal is the unit ideal on $U_1$.
The cited theorem uses the ordinary small pro-etale module category and the finite line
$\nu_P^*(\mu_{\ell^n}\otimes_{A_{n,P}}A_{n,P})$. The canonical tensor-unit isomorphism $z\otimes
a\mapsto az$ identifies this with $\nu_P^*\mu_{\ell^n}=A_{n,P}(1)$, so both the coefficient
category and the target of its Cartier morphism are exactly the ones used here. Extension from
$R$ to $\Lambda=R$ is the identity scalar-extension functor under that same tensor-unit
identification. Its composite with the restriction unit is the Kummer boundary of the generator
torsor of $\mathcal O_P(s(Y))=\mathcal O_P(1)$, so it is the evaluated Chern class used in
$b_n$. This agrees with the positive Cartier normalization $t^{-1}\mapsto+1$ recorded in
[proposition-ell-adic-cycle-class-diagonal]. This invocation is only at finite levels: the coherent
system morphism itself was supplied by [proposition-sp-tower-geometric](2), not inferred from
equality of finite-level derived morphisms. Uses: lemma-cycle-class-cartier-divisor,
proposition-ell-adic-cycle-class-diagonal, proposition-sp-tower-geometric.

3. Exactness and cohomology in the varying-coefficient system category are levelwise by
[prose-09-21]. Evaluation of derived direct image is levelwise by
[lem-pur-coefficient-system-derived-comparison], including its unit. At level $n$,
[lemma-cohomology-projective-line-trace] with $r=n$ and $\Lambda=\mathbf Z/\ell^n$ identifies $b_n$
as an isomorphism. The cone of $b_\bullet$ therefore has every cohomology system zero, so
$b_\bullet$ is an isomorphism. Finally restrict scalars from the ring system $A_\bullet$ to the
constant system $\underline{\mathbf Z_\ell}$; restriction is exact, since kernels and cokernels keep
their underlying groups. The canonical direct-image comparisons in
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition], applied on the tower topoi also to
these restriction-of-scalars morphisms, identify the resulting map with the asserted map in the
constant-coefficient tower category. No faithfulness of derived evaluation is used. Uses:
prose-09-21, lem-pur-coefficient-system-derived-comparison,
lemma-cohomology-projective-line-trace, lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

4. The twisting and second-summand projection in [proposition-sp-tower-geometric](4), for $E=\mathbf
Q_\ell$, give the system trace $t_{q,\bullet}$. Concretely the twisted isomorphism has source
$A_{\bullet,Y}(1)[2]\oplus A_{\bullet,Y}$ and target $Rq_*A_{\bullet,P}(1)[2]$; compose its
inverse with $\operatorname{pr}_2$. This is the twist of the map just constructed, with the
inverse-image/direct-image projection identification built into that cited splitting. Its
evaluation is the projection defining the finite trace in [lemma-cohomology-projective-line-trace],
because evaluation preserves composition, inverses, units and the prescribed twisting construction.
The same construction applies to $p_1,p_2$, which are projective lines over $P$. Thus all three
traces are morphisms of systems before taking a limit. Uses: proposition-sp-tower-geometric,
lemma-cohomology-projective-line-trace, lem-pur-coefficient-system-derived-comparison.

5. Write $C_T=\underline{\mathbf Z_\ell}$ and $R_T=\Zl_T$. For the coefficient tower the
quotient maps are epimorphisms; for its twist the maps are epimorphisms by
[lem-pur-twist-sheaf-locally-free](1). Therefore [proposition-milnor-sequence--3], with ring sheaf
$C_T$, identifies $R\varprojlim A_{\bullet,T}=R_T$ and $R\varprojlim A_{\bullet,T}(1)=R_T(1)$,
for $T=Y,P,W$. The latter also identifies the transition maps with the roots-of-unity power
maps. Apply $R\varprojlim$ to $t_{q,\bullet}$. The canonical natural comparison
[lem-weil-ringed-tower-pushforward-limit-comparison], applied with constant coefficient sheaves
$C_P,C_Y$, identifies the resulting source with $Rq_*\operatorname{Res} R_P(1)[2]$ and the
target with $\operatorname{Res} R_Y$. It commutes with all tower projections. This is a trace
over the discrete constant ring at this point. The completed coefficient identification is
[lemma-comparison-completed-coefficients--1] with $E=\mathbf Q_\ell$. Uses:
lem-pur-twist-sheaf-locally-free, proposition-milnor-sequence--3,
lem-weil-ringed-tower-pushforward-limit-comparison, lemma-comparison-completed-coefficients--1.

6. We now obtain the asserted completed-coefficient trace and check its reductions as actual
morphisms. The source coefficient line $R_P(1)$ is derived complete and has derived reduction
$A_{n,P}(1)$ by [lem-pur-twist-sheaf-locally-free](4). The target $R_Y$ is also derived
complete: its ordinary reductions are $A_{n,Y}$ by
[lem-weil-pbc-constant-completion-equivalence], its derived reductions are ordinary since it is
the free rank-one module over itself, and the preceding epimorphic-tower limit computation
identifies its canonical completion unit with an isomorphism. Apply
[proposition-proper-base-change-complete-integral--1] in its completed-coefficient categories to
$R_P(1)[2]$; it makes $Rq_*R_P(1)[2]$ complete. Its coefficient-datum hypotheses for $(\mathbf
Z_\ell,(\ell))$ hold: [lemma-reduction-derived-nakayama--1] gives the finite perfect quotients, and
[lem-weil-l-adic-extension-integers-dvr](2), with $E=\mathbf Q_\ell$, makes $\mathbf Z_\ell$ a
principal ideal domain. Every ideal is therefore generated by one element, which is the
Noetherian condition. Uses: lem-pur-twist-sheaf-locally-free,
lem-weil-pbc-constant-completion-equivalence, proposition-proper-base-change-complete-integral--1,
lemma-reduction-derived-nakayama--1, lem-weil-l-adic-extension-integers-dvr.

7. Restriction to constant coefficients commutes with derived direct image by the ringed-topos
composition comparison of [lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. The
equivalence [lemma-integral-models](1), with $E=\mathbf Q_\ell$, therefore lifts the trace of
step 5 uniquely to $\operatorname{Tr}_q:Rq_*R_P(1)[2]\to R_Y$. Uses:
lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lemma-integral-models.

8. The finite-reduction and limit-unit comparisons of
[lem-weil-pbc-constant-completion-equivalence], together with the projection-compatible
finite-reduction isomorphisms of [proposition-proper-base-change-complete-integral--1], identify its
reduction with $t_{q,n}$. Indeed the square for $R\varprojlim t_{q,\bullet}$ and the $n$th tower
projections commutes by naturality; the derived scalar-extension/restriction adjunction of
[lem-weil-derived-scalar-extension-restriction-adjunction], with $E=\mathbf Q_\ell$, identifies
a projection to level $n$ with its finite-reduction adjoint. Under the finite-reduction
comparisons above this adjoint is exactly the reduced map, and the just cited comparisons
identify the two adjoints with $t_{q,n}$. By step 4 this is the torsion trace of
[lemma-cohomology-projective-line-trace]. This argument also applies to $p_1,p_2$. Uses:
lem-weil-pbc-constant-completion-equivalence, proposition-proper-base-change-complete-integral--1,
lem-weil-derived-scalar-extension-restriction-adjunction, lemma-cohomology-projective-line-trace.

9. Let $c_\bullet$ be the system diagonal class of [proposition-ell-adic-cycle-class-diagonal](4),
and form $e_{i,\bullet}=t_{p_i,\bullet}\circ Rp_{i*}c_\bullet$ after the canonical source
identification $Rp_{i*}\Delta_*A_{\bullet,P}=A_{\bullet,P}$. This identification follows from
$p_i\Delta=\mathrm{id}_P$ and [lem-weil-pbc-ringed-topoi-derived-pushforward-composition]. The
replacement of $R\Delta_*$ by $\Delta_*$ is justified by
[proposition-extension-zero-restriction-closed-subscheme--4]: the diagonal is the closed Cartier
divisor cut out by $x_0y_1-x_1y_0$, and its complement is quasi-compact since $W$ is Noetherian.
Apply this exactness first in the category of varying-coefficient systems $A_\bullet$: kernels and
cokernels are levelwise by [prose-09-21], so $\Delta_{A,*}$ is exact there and
$R\Delta_{A,*}A_{\bullet,P}=\Delta_{A,*}A_{\bullet,P}$. Let $U_T$ be restriction from
$A_{\bullet,T}$-modules to towers of $C_T=\underline{\mathbf Z_\ell}$-modules. It is exact on
underlying sheaves. The equality of underived composites $U_W\Delta_{A,*}=\Delta_{C,*}U_P$,
together with the ringed-topos composition comparison just cited, gives
$R\Delta_{C,*}A_{\bullet,P}=U_W\Delta_{A,*}A_{\bullet,P}=\Delta_*A_{\bullet,P}$. Thus the needed
identification in the constant-coefficient tower category does not require exactness of
$\Delta_*$ on arbitrary $C_T$-module sheaves. Uses: proposition-ell-adic-cycle-class-diagonal,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
proposition-extension-zero-restriction-closed-subscheme--4, prose-09-21.

10. The varying-coefficient source identifications commute with evaluation by
[lem-pur-coefficient-system-derived-comparison]; their restrictions do so by the same
composition comparisons. Evaluate the constant-coefficient composite, using
[lem-weil-ringed-tower-pushforward-limit-comparison] for levelwise derived direct image. At
level $n$ the class is the torsion diagonal class by [proposition-ell-adic-cycle-class-diagonal](4),
the trace is $t_{p_i,n}$ by step 4, and restriction of the finite-coefficient equality of
[det-sp-p1-trace](3) gives $e_{i,n}=\mathrm{id}$ in $D(P_{\mathrm{proet}},C_P)$. This last
citation is explicitly a pro-etale finite-coefficient assertion; it is not an unproved transport
of the ordinary etale identity. Uses: lem-pur-coefficient-system-derived-comparison,
lem-weil-pbc-ringed-topoi-derived-pushforward-composition,
lem-weil-ringed-tower-pushforward-limit-comparison, proposition-ell-adic-cycle-class-diagonal,
det-sp-p1-trace.

11. The source and target of $e_{i,\bullet}$ are the system $A_{\bullet,P}$ in degree zero.
Apply [lem-weil-pbc-derived-single-fully-faithful] to the abelian category of system sheaves. It
identifies $e_{i,\bullet}$ with a unique actual system-sheaf endomorphism. Such a morphism is a
family commuting with the quotient transitions; equality is componentwise by the definition of
that category. Apply the same degree-zero full faithfulness in the abelian category of
$C_P$-module sheaves at each level: step 10 then says every actual component is the identity,
hence $e_{i,\bullet}=\mathrm{id}$ already in the system derived category. Apply $R\varprojlim$.
The natural direct-image/limit comparison [lem-weil-ringed-tower-pushforward-limit-comparison]
carries this composite to $\operatorname{Tr}_{p_i}\circ Rp_{i*}(\delta_{\Zl})$, since
[proposition-ell-adic-cycle-class-diagonal](3) identifies $R\varprojlim c_\bullet$ with
$\delta_{\Zl}$. Its source identification is the same one obtained by limiting the composition
identification in step 9. Thus the composite is the identity after restriction to constant
coefficients. The equivalence on complete objects [lemma-integral-models](1) is faithful, so the
identity holds over the completed coefficient sheaf as claimed. Equality of arbitrary morphisms of
derived systems was never inferred from their evaluated equalities: the degree-zero full
faithfulness is essential here. Uses: lem-weil-pbc-derived-single-fully-faithful,
lem-weil-ringed-tower-pushforward-limit-comparison, proposition-ell-adic-cycle-class-diagonal,
lemma-integral-models. -/
theorem diagonalTower_trace (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
    [IsNoetherian (diagonalSurface Y)] (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : IsDiagonalLimit l Y hY D δ) :
    ∃ (tq : Result l (ULift.{u} (Padic l)) (ProjectiveLine Y ↘ Y))
      (t₁ : Result l (ULift.{u} (Padic l))
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
      (t₂ : Result l (ULift.{u} (Padic l))
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))),
      tq.model.model = Iso.refl (ProjectiveLine Y) ∧
      t₁.model.model = diagonalTraceFirstModel Y ∧
      t₂.model.model = diagonalTraceSecondModel Y ∧
      ∃ (a₁ : SupportedSource l Y
          (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₁.Rc)
        (a₂ : SupportedSource l Y
          (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) t₂.Rc),
        IsIntegration t₁.Rc.R a₁.hom t₁.trace δ ∧
        IsIntegration t₂.Rc.R a₂.hom t₂.trace δ := by
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) :=
    (map_natCast (ProjectiveLine Y ↘ Y).appTop.hom l) ▸
      hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hfirst : (diagonalTraceFirstModel Y).hom ≫
      (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) =
        pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) := by
    exact IsPullback.isoPullback_inv_fst _
  have hsecond : (diagonalTraceSecondModel Y).hom ≫
      (ProjectiveLine (ProjectiveLine Y) ↘ ProjectiveLine Y) =
        pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) := by
    simp only [diagonalTraceSecondModel, Iso.trans_hom, Category.assoc, hfirst,
      pullbackSymmetry_hom_comp_fst]
  obtain ⟨tq, hq⟩ := exists_diagonalTraceResult l (ProjectiveLine Y ↘ Y)
    (Iso.refl _) (Category.id_comp _) hY
  obtain ⟨t₁, h₁⟩ := exists_diagonalTraceResult l
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (diagonalTraceFirstModel Y) hfirst hP
  obtain ⟨t₂, h₂⟩ := exists_diagonalTraceResult l
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (diagonalTraceSecondModel Y) hsecond hP
  obtain ⟨a₁, s₁, _, _⟩ := diagonalTrace_integrationSystems l Y hY D δ hδ
    _ (Or.inl rfl) t₁
  obtain ⟨a₂, s₂, _, _⟩ := diagonalTrace_integrationSystems l Y hY D δ hδ
    _ (Or.inr rfl) t₂
  refine ⟨tq, t₁, t₂, hq, h₁, h₂, a₁, a₂, ?_, ?_⟩
  · apply diagonalTrace_single_map_injective l (ProjectiveLine Y)
      (a₁.hom ≫ t₁.Rc.R.map δ ≫ t₁.trace) (𝟙 _)
    exact s₁.eq_id.trans ((diagonalCompletedUnderlying l (ProjectiveLine Y)).map_id _).symm
  · apply diagonalTrace_single_map_injective l (ProjectiveLine Y)
      (a₂.hom ≫ t₂.Rc.R.map δ ≫ t₂.trace) (𝟙 _)
    exact s₂.eq_id.trans ((diagonalCompletedUnderlying l (ProjectiveLine Y)).map_id _).symm

end AlgebraicGeometry.ProEtale
