/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
public import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphUnitTensor
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso

/-! # The graph comparison and the etale projection formula over arbitrary bases

Source: blueprint `sec-six-functors-basics/sk-prop-cohsm/thm-asd-smooth-tensor.proof.md`,
paragraph 3; Stacks Tag 0GKF, lemma-f-shriek-projection
(auxiliary; not a blueprint node).

The graph comparison is the upstream `compactificationEtaleComparison`, constructed
from clopen graph transfer and inverse proper exchange. The helpers merely insert the
canonical exact/left-derived comparison into the existing projection maps.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The inverse tensor comparison for exact inverse image, transported from derived pullback.
Source: Stacks Tag 0GKF and blueprint paragraph 3
(auxiliary; not a blueprint node).
This is mu, using precisely the canonical exact/left-derived comparison in both inputs
and in their tensor product. Its coefficient-unit normalization is etaleSumPullbackUnitIso.
It is the existing `supportExactPullbackTensorIso` (owner
def-pur-supported-localization-comparisons) at the coefficients `ModuleCat A`. -/
noncomputable abbrev sfEtaleExactPullbackTensorIso
    (A : Type (u + 1)) [CommRing A] {V W : Scheme.{u}} (e : V ⟶ W)
    (B K : DerivedCategoryModule A W) :
    D((e)^*[ModuleCat.{u + 1} A]).obj
        (((derivedTensor (ModuleCat.{u + 1} A) W).obj B).obj K) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) V).obj
        (D((e)^*[ModuleCat.{u + 1} A]).obj B)).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K) :=
  supportExactPullbackTensorIso (ModuleCat.{u + 1} A) e B K

/-- The specified unit-adjunct tensor action kappa for exact etale sum extension.
Source: Stacks Tag 0GKF and blueprint paragraph 3
(auxiliary; not a blueprint node).
This is the inverse Hom transpose of the sum/evaluation unit tensored with the identity,
followed by the inverse of mu. No choice of a projection isomorphism is made. -/
noncomputable def sfEtaleSumExactTensorMap
    (A : Type (u + 1)) [CommRing A] {V W : Scheme.{u}} (e : V ⟶ W) [Etale e]
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    D(etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K)) ⟶
      ((derivedTensor (ModuleCat.{u + 1} A) W).obj
        (D(etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M)).obj K :=
  ((derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e).homEquiv _ _).symm
    (((derivedTensor (ModuleCat.{u + 1} A) V).map
        ((derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e).unit.app M)).app _ ≫
      (sfEtaleExactPullbackTensorIso A e
        (D(etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).obj M) K).inv)

/-- The proper-counit/open-tensor projection P, in the exact inverse-image model.
Source: Stacks Tag 0GKF and blueprint paragraph 3
(auxiliary; not a blueprint node).
The existing ambient theorem supplies invertibility of the specified projection.
Only its target is transported along the canonical Le* to D(e*) comparison. -/
noncomputable def sfEtaleExactProjectionIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} {e : V ⟶ W} (c : Compactification e)
    (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W) :
    ((derivedTensor (ModuleCat.{u + 1} A) W).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M)).obj K ≅
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
          (D((e)^*[ModuleCat.{u + 1} A]).obj K)) :=
  haveI := (sfEtaleAmbientAdjointProjection A c).2 M K
  asIso (((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso
      (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).mapIso
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).app K))

private theorem graphUnit_exact
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] (c : Compactification e)
    (M : DerivedCategoryModule A V) :
    (derivedEtaleLowerShriekMapAdjunction (ModuleCat.{u + 1} A) e).unit.app M ≫
        D((e)^*[ModuleCat.{u + 1} A]).map
          ((compactificationEtaleComparison A e c).app M) =
      (compactificationEtaleUnit A e c).app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).hom.app _ := by
  have h := unit_map_compactificationEtaleComparison A e c M
  simp only [derivedEtaleLowerShriekAdjunction, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom] at h
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} A) e).hom.naturality ((compactificationEtaleComparison A e c).app M)
  dsimp at hn
  rw [← h]
  simp only [Category.assoc]
  erw [hn]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem exactTensor_inv_naturality
    (A : Type (u + 1)) [CommRing A]
    {V W : Scheme.{u}} (e : V ⟶ W)
    {B B' : DerivedCategoryModule A W} (f : B ⟶ B')
    (K : DerivedCategoryModule A W) :
    (sfEtaleExactPullbackTensorIso A e B K).inv ≫
        D((e)^*[ModuleCat.{u + 1} A]).map
          (((derivedTensor (ModuleCat.{u + 1} A) W).map f).app K) =
      ((derivedTensor (ModuleCat.{u + 1} A) V).map
        (D((e)^*[ModuleCat.{u + 1} A]).map f)).app _ ≫
          (sfEtaleExactPullbackTensorIso A e B' K).inv := by
  let H := D((e)^*[ModuleCat.{u + 1} A])
  let J := L((e)^*[ModuleCat.{u + 1} A])
  let τ := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
  let T := derivedTensor (ModuleCat.{u + 1} A) W
  let T' := derivedTensor (ModuleCat.{u + 1} A) V
  let δ := (Functor.postcompose₂.mapIso τ.symm).app T ≪≫
    leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) e ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategoryModule A V)).mapIso τ).app J).app T' ≪≫
    (((Functor.whiskeringLeft₂ (DerivedCategoryModule A V)).obj H).mapIso τ).app T'
  exact (NatTrans.congr_app (δ.inv.naturality f) K).symm

/-- The specified graph comparison is a natural isomorphism, and intertwines the
proper-counit/open-tensor projection with the sum/evaluation unit-adjunct tensor action.
Source: blueprint thm-asd-smooth-tensor.proof.md, paragraph 3; Stacks Tag 0GKF,
lemma-f-shriek-projection
(auxiliary; not a blueprint node).

The comparison a is exactly compactificationEtaleComparison: its graph transfer uses
compactificationEtaleGraphIso, the clopen unit and counit, followed by the ordinary
pullback/direct-image unit and inverse proper exchange in compactificationEtaleUnit.
The upstream adjunction is transported from the termwise sum/evaluation adjunction,
so its transpose is the specified exact-model transpose after canonical transport.

Proof plan, step by step (the accepted DAG proof):
1. Check the graph geometry. The base change $q$ of $r$ is proper and hence separated. Since
   $q\sigma=1$, the section lemma makes $\sigma$ closed. The base change $q_Z$ of $e$ is etale;
   $q_Z\sigma=j$ is etale because $j$ is open. Etale cancellation makes $\sigma$ etale. A
   section is a monomorphism: apply $q$ to cancel it. By the definition of etale, $\sigma$ is
   flat and locally of finite presentation, so the flat locally finitely presented monomorphism
   lemma makes it open. No quasi-compactness of $j$ was used. Uses: lem-weil-pbc-proper-base-
   change, def-weil-proper-morphism, lem-weil-pbc-section-separated-closed-immersion, lem-weil-
   pbc-etale-base-change-finite-limits, definition-torsion-sheaves--3, def-weil-
   etale-morphism, lem-pe-flat-lfp-monomorphism-open.
2. For a clopen decomposition $X=U\amalg C$, the cited sheaf equivalence extends from abelian
   sheaves to constant-$A$ modules: the endomorphisms giving the action of each $a\in A$, and
   their equations, are recovered componentwise by full faithfulness. Restriction and inverse
   gluing are exact, since kernels and cokernels are componentwise. Apply them degreewise to
   complexes. Their inverse-composite isomorphisms and triangle identities are degreewise those
   of the sheaf equivalence. Exactness lets the functors descend, and the localization universal
   property descends those isomorphisms and their identities. Thus restriction gives an
   equivalence $D(X_{\rm et},A)\simeq D(U_{\rm et},A)\times D(C_{\rm et},A)$, fully faithful on
   morphisms. Extension from $U$ is insertion $(L,0)$ by its restriction and zero-extension
   description. Neither piece needs be quasi-compact. Uses: lem-weil-pbc-etale-sheaf-clopen-
   product, lem-weil-pbc-exact-functor-derived-functor, lem-weil-pbc-localization-universal-
   property, lem-weil-pbc-extension-by-zero-exact.
3. For a clopen inclusion $s:U\hookrightarrow X$ and $\psi:s^*L\to s^*H$, its transfer
   $T_s(\psi):L\to s_!s^*L\to s_!s^*H\to H$ is $(\psi,0)$ under step 2: the unit of $s^*\dashv
   s_!$ projects onto the first factor, and the counit of $s_!\dashv s^*$ inserts that factor,
   as their product-category Hom bijections show. Transfer is therefore natural. By the derived-
   pullback tensor comparison, $T_s(\psi)\otimes1_N$ restricts to $\psi\otimes1_{s^*N}$ on $U$
   and to zero on $C$, so is its transfer, with the canonical tensor comparisons inserted. For a
   base change $h:X'\to X$, $h^*T_s(\psi)$ is likewise the transfer on $h^{-1}U$: its
   restrictions to $h^{-1}U,h^{-1}C$ are respectively the pulled-back $\psi$ and zero, using
   pullback composition. Full faithfulness in step 2 proves these equalities of derived
   morphisms. Geometric stalks are not used to test equality. Uses: lem-weil-pbc-ringed-topoi-
   derived-tensor-pullback, lem-kun-derived-pullback-composition-monoidal.
4. Put $H_M=Dj_!M$, $J=EK$ and $M_K=M\otimes J$. In this step and below use the exact/left-
   derived transport and the unit and composition comparisons specified in the cited definition.
   The monoidal comparison lemma makes these the canonical monoidal compositors; insert them in
   all displayed formulas. Let $\gamma_M:H_M\otimes r^*K\cong H_{M_K}$ be the specified open
   tensor comparison, and let $d:q_Z^*H_M\otimes q^*J\to q_Z^*H_{M_K}$ be its pullback. Then
$$t_{M_K}=d(t_M\otimes1)\mu_q,$$
where $\mu_q:q^*(M\otimes J)\cong q^*M\otimes q^*J$. Indeed on $\sigma(V)$ transfer is the
   identification $M\cong j^*H_M$, and $j^*\gamma_M$ is the canonical tensor identification
   under $j^*j_!\cong1$; on the complementary open both transfers are zero. Step 2 gives the
   equality. The normalization of $\gamma$ is the sheaf tensor identity in the open tensor
   lemma; its compatibility with the open unit and pullback is the cited open-unit mate and open
   projection/exchange equation. Thus these are the specified identifications, not arbitrarily
   chosen isomorphisms. Uses: def-pur-etale-exact-pullback-unit-composition-comparisons, lem-
   sfb-ringed-derived-monoidal-comparisons, lem-pur-etale-open-derived-tensor, lem-asd-open-
   projection-exchange, lem-asd-open-base-change-unit-mate, lem-kun-derived-pullback-
   composition-monoidal.
5. Write $R=Rq_*$, $Q=q^*$, $\eta:1\to RQ$, and $\pi_q$ for the counit-defined projection map.
   If $\tau:QM\otimes QJ\to Q(M\otimes J)$ is the inverse tensor comparison, then
$$R(\tau)\pi_q(QM,J)(\eta_M\otimes1_J)=\eta_{M\otimes J}.$$
Transpose under $Q\dashv R$. By the defining adjunct of $\pi_q$, the transpose of the left side
   is $\tau(\varepsilon_{QM}Q\eta_M\otimes1)\mu_q=1$, by the triangle identity. The transpose of
   the right side is also $1$. Apply $R(t_{M_K})$, step 4 and naturality of $\pi_q$. As maps
   $M\otimes J\to Rq_*q_Z^*H_{M_K}$ this yields
$$Rq_*(t_{M_K})\eta_{M_K}=Rq_*(d)\pi_q(q_Z^*H_M,J)((Rq_*t_M\eta_M)\otimes1_J).$$ Uses: def-kun-
   projection-formula-map, definition-derived-base-change-map.
6. A finite ring is torsion: its finite additive group kills $1$. Proper base change is
   therefore invertible for $r$. Apply exchange/projection compatibility to the square
   $(r,q,e,q_Z)$, with $H_M,K$. It gives
$$\operatorname{Ex}_{r,H_{M_K}}E(P_{M,K})\mu_{FM,K}^{-1}
=Rq_*(d)\pi_q(q_Z^*H_M,EK)(\operatorname{Ex}_{r,H_M}\otimes1).$$
The proper part is the cited ringed exchange/tensor equation. The open part of $P$ is
   $Rr_*(\gamma_M)$; its contribution is $Rq_*q_Z^*(\gamma_M)$ by naturality of exchange, namely
   $Rq_*(d)$ with its tensor comparison. Open projection/exchange fixes the same open
   comparison. Monoidal pullback composition identifies $q^*e^*K$ with $q_Z^*r^*K$. Substitute
   step 5 and cancel exchange to obtain the exact unit identity
$$u_{M\otimes EK}=E(P_{M,K})\mu_{FM,K}^{-1}(u_M\otimes1_{EK}).\tag{*}$$ Uses: lem-kun-proper-
   base-change-torsion-ring, lem-weil-pbc-ringed-exchange-tensor-coherence, lem-asd-open-
   projection-exchange, lem-kun-derived-pullback-composition-monoidal, lem-sf-etale-ambient-
   adjoint-projection.
7. Naturality of transfer, the adjunction unit, proper exchange and its inverse proves
   naturality of $u$ and hence of $a$. Transpose $P_{M,K}(a_M\otimes1)\kappa_{M,K}$ under
   $S\dashv E$. The defining adjunct of $\kappa$ and naturality of $\mu$ give its transpose as
$$E(P_{M,K})E(a_M\otimes1)\mu_{SM,K}^{-1}(v_M\otimes1)
=E(P_{M,K})\mu_{FM,K}^{-1}((Ea_M)v_M\otimes1)
=E(P_{M,K})\mu_{FM,K}^{-1}(u_M\otimes1).$$
By (*) this is $u_{M\otimes EK}$, whose adjunct is $a_{M\otimes EK}$. Injectivity of the Hom
   bijection and composition with $P^{-1}$ give the required tensor square. No invertibility of
   $a$ was used for this equality. Uses: lem-pur-unit-adjunct-tensor-action, lem-sf-etale-
   ambient-adjoint-projection.
8. Let $g:W'\to W$ be any map, with base changes $h:V'\to V$, $z:Z'\to Z$, $b:B'\to B$ and
   primes on the pulled-back data. Let $C_F:g^*FM\cong F'h^*M$ be proper exchange followed by
   open base change, $C_S:S'h^*M\cong g^*SM$ exact sum base change, and $c:E'g^*\cong h^*E$ the
   pullback square comparison. We check
$$C_Fg^*a_MC_S=a'_{h^*M}.\tag{**}$$
The sum base-change map is the mate of the pullback square. Its unit equation is
   $E'C_Sv'=c^{-1}h^*v$; obtain this first on sheaves by the mate formula in the cited
   definition, then descend by exactness and localization. Thus the transpose of the left side
   of (**) is $E'C_Fc^{-1}h^*u_M$. Expand $u_M=\operatorname{Ex}_r^{-1}Rq_*t_M\eta_q$. Mate
   pasting for the cube formed by base-changing $Z\times_WV$ identifies the exchanges for two
   successive base changes of $r$ in either order. For the unit factor, the mate identity for
   the square with vertical edge $q$ says that exchange after the pulled-back $\eta_q$ is the
   primed unit followed by the pullback square comparison. For the transfer factor, step 3 gives
   $t'_{h^*M}$: the identification $z^*j_!M\cong j'_!h^*M$ restricts to the same $j^*j_!$ unit
   by the cited open-unit equation. Pasting these three factors therefore gives precisely
   $u'_{h^*M}$. All inverse proper exchanges cancel by their invertibility. Transpose back to
   prove (**). Uses: lem-weil-pbc-etale-shriek-base-change-modules, def-weil-pbc-etale-shriek-
   base-change-map, lem-weil-pbc-exact-functor-derived-functor, lem-weil-pbc-localization-
   universal-property, lem-weil-pbc-mate-pasting, definition-derived-base-change-map,
   lem-asd-open-base- change-unit-mate, lem-kun-proper-base-change-torsion-ring,
   lem-kun-derived-pullback- composition-monoidal.
9. Take $W'=P=\operatorname{Spec}\Omega$ for a geometric point with $\Omega$ algebraically
   closed. The proper fibre $Z_P$ is finite type over the Noetherian affine $P$, hence quasi-
   compact and locally Noetherian. Choose a finite affine Noetherian cover: each member has
   Noetherian underlying space, and so does their finite union. Every subset of $|Z_P|$ is
   consequently quasi-compact, including $j_P(V_P)$. The etale fibre $V_P$ is discrete, a
   disjoint union of spectra of finite separable extensions of $\Omega$. Each extension is
   $\Omega$, since a minimal polynomial over an algebraically closed field has degree one.
   Quasi-compactness of this discrete space makes its set $I$ of points finite, by its singleton
   cover. Thus $V_P=\coprod_{i\in I}P$. Each composite $s_i:P\to V_P\to Z_P$ is open and is a
   section of the separated map $r_P$, so has closed image. These are pairwise disjoint clopen
   sections. This uses no quasi-compactness hypothesis on $j$ itself. Uses: lem-weil-pbc-proper-
   base-change, def-weil-proper-morphism, lem-weil-pbc-finite-type-over-noetherian, pqf-def-
   locnoeth, lem-sc-affine-noetherian-underlying-space, lem-kun-finite-union-noetherian, lem-
   sfb-noetherian-space-compact-subsets, lem-weil-pbc-etale-fibre-discrete-separable-points,
   lem-weil-pbc-section-separated-closed-immersion.
10. Write $M_i=M_P|_{P_i}$. The clopen-section evaluation lemma identifies $F'M_P$ with
   $\prod_iM_i$ and $S'M_P$ with $\bigoplus_iM_i$, with its specified derived restriction
   normalization. Compute our $a'$ by restricting its adjunct $u'$ to $P_i\subset V_P$. The
   space $B_P=Z_P\times_PV_P$ is a copy of $Z_P$ for each $i$; its graph in the $i$-th copy is
   exactly $s_i(P)$. Transfer is identity on $M_i$ there and zero on every $s_k(P)$ for $k\ne i$
   and on the complement. The unit $M_i\to Rr_{P*}r_P^*M_i$ and the counit normalization of
   exchange for identity base change give $u'_i:M_i\to\prod_kM_k$ whose $k$-entry is $1$ for
   $k=i$ and $0$ otherwise: after restriction to $s_k$, the composite $r_Ps_k=1$ and the
   adjunction triangle identity give the identity entry. The sum/evaluation unit into $E'S'$
   inserts the same $i$-th summand. Hence $a'$ has identity diagonal and zero off diagonal. It
   is the canonical finite sum-to-product map, invertible by the cited evaluation lemma. For
   $I=\varnothing$ both sides are zero. This is a computation of derived morphisms using step 2
   and the normalized evaluation lemma; it does not assume bounded resolutions or faithfulness
   of stalks on derived Hom groups. Uses: lem-asd-clopen-geometric-sections-derived-evaluation,
   lemma-acyclicity-pulled-back-injectives, lemma-acyclicity-pulled-back-injectives, def-kun-
   unbounded-exchange, lem-weil-pbc-mate-pasting.
11. Apply (**) at all algebraic-closure geometric points of $W$. The maps $C_F,C_S$ are
   isomorphisms and all fibre comparisons from step 10 are isomorphisms. Thus every such inverse
   image makes $a_M$ invertible. They form a small jointly surjective family in the fixed
   universe, so unbounded derived conservativity gives that $a_M$ is invertible. Exact inverse
   image agrees with its left derived functor by exact descent, as required by that lemma.
   Naturality was proved in step 7, so $a$ is a natural isomorphism. Together with step 7 this
   proves the entire assertion, including empty schemes, the zero coefficient ring and arbitrary
   unbounded complexes. Uses: lem-etale-derived-jointly-surjective-conservative, lem-weil-pbc-
   exact-functor-derived-functor.
-/
theorem sfEtaleGraphProjectionArbitraryBase
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V W : Scheme.{u}} (e : V ⟶ W) [Etale e] [IsSeparated e] (c : Compactification e) :
    IsIso (compactificationEtaleComparison A e c) ∧
      ∀ (M : DerivedCategoryModule A V) (K : DerivedCategoryModule A W),
        (compactificationEtaleComparison A e c).app
              (((derivedTensor (ModuleCat.{u + 1} A) V).obj M).obj
                (D((e)^*[ModuleCat.{u + 1} A]).obj K)) ≫
            (sfEtaleExactProjectionIso A c M K).inv =
          sfEtaleSumExactTensorMap A e M K ≫
            ((derivedTensor (ModuleCat.{u + 1} A) W).map
              ((compactificationEtaleComparison A e c).app M)).app K := by
  refine ⟨isIso_compactificationEtaleComparison A e c, ?_⟩
  intro M K
  apply (cancel_mono (sfEtaleExactProjectionIso A c M K).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ((derivedEtaleLowerShriekMapAdjunction
    (ModuleCat.{u + 1} A) e).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [sfEtaleSumExactTensorMap, Equiv.apply_symm_apply,
    Functor.map_comp, Category.assoc]
  rw [Adjunction.homEquiv_unit, graphUnit_exact, sfEtaleGraphUnitTensor]
  rw [reassoc_of% (exactTensor_inv_naturality A e
    ((compactificationEtaleComparison A e c).app M) K)]
  have hc := congrArg
    (fun f ↦ ((derivedTensor (ModuleCat.{u + 1} A) V).map f).app
      (D((e)^*[ModuleCat.{u + 1} A]).obj K)) (graphUnit_exact A e c M)
  simp only [Functor.map_comp, NatTrans.comp_app] at hc
  rw [reassoc_of% hc]
  simp only [sfEtaleExactProjectionIso, Iso.trans_hom, asIso_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
