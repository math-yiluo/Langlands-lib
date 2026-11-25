/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import WeilConjectures.AlgebraicGeometry.Curve.CoefficientPair
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenVanishingComparison
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison

/-!
# The eight curve assertions on a dense open

Source: Stacks Project, Etale Cohomology, Lemma 0GJA, Situation 0A52
(blueprint: lemma-removing-finitely-many-points).

The unconditional equivalence, without a condition on the torsion of the sheaf, is
`AlgebraicGeometry.IsCurve.assertions_iff_dense_open`, a corollary of the curve package.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The eight assertions transfer from extension by zero of the dense-open restriction to
 the original constructible torsion sheaf. The converse holds for primary or prime-to-the-
 characteristic torsion, and hence for a sheaf killed by a prime.
 Source: Stacks Project, Lemma 0GJA and Situation 0A52, with the converse torsion condition
 recorded in the node (blueprint: lemma-removing-finitely-many-points). The equivalence without the
 torsion condition is `AlgebraicGeometry.IsCurve.assertions_iff_dense_open`: both sides hold by
 the curve package, whose proof goes through the prime-torsion comparison
 `AlgebraicGeometry.IsCurve.assertions_iff_dense_open_prime`.

 Abelian sheaves are converted to modules by precisely the coefficient functor used in
 `IsCurve.finite_pushforward_assertions`; this adds no coefficient structure or hypothesis.

 Proof (following the node's steps):

1. Conventions. Write $F'=j_!j^{-1}F$. As in Stacks, Situation 0A52 ('we will say that statements
(1)-(8) hold if those statements that apply to the given situation are true'), $\mathcal C(X,G)$
for a curve coefficient pair $(X,G)$ is the conjunction of the eight implications $\mathcal
C_1,\dots,\mathcal C_8$ [theorem-cohomology-curves--1]-[theorem-cohomology-curves--8] of
[theorem-cohomology-curves]; Stacks' items (1) item-vanishing, (2)
item-vanishing-affine, (3) item-vanishing-p-p, (4) item-finite-prime-to-p, (5) item-finite-proper,
(6) item-base-change-prime-to-p, (7) item-base-change-proper, (8) item-surjective are $\mathcal
C_1,\dots,\mathcal C_8$ in this order, and Lemma 0GJA covers all eight. For the zero sheaf every
conclusion holds trivially (all cohomology groups and pullback maps are those of $0$). By
[def-weil-pbc-primary-torsion], when $\operatorname{char}k=0$ every torsion sheaf is prime to the
characteristic and $(\mathcal C_3)$ is vacuous; so the case analyses below on '$p$-primary / prime
to $p$' only concern $\operatorname{char}k=p>0$. Dependencies:
theorem-cohomology-curves, theorem-cohomology-curves--1, theorem-cohomology-curves--2,
theorem-cohomology-curves--3, theorem-cohomology-curves--4, theorem-cohomology-curves--5,
theorem-cohomology-curves--6, theorem-cohomology-curves--7, theorem-cohomology-curves--8,
def-weil-pbc-primary-torsion.

2. The closed complement (Stacks 0GJA, proof, first sentence: 'Since $X'$ is dense, we see that
$Z=X\setminus X'$ has dimension $0$ and hence is a finite set of $k$-rational points'). $X$ is of
finite type over $k$, hence Noetherian, with finitely many irreducible components $X_1,\dots,X_n$
and generic points $\eta_a$. The open set $X_a\setminus\bigcup_{b\ne a}X_b$ is nonempty and
contains $\eta_a$; the dense open $X'$ meets it in a point $y$ with $y\in\overline{\{\eta_a\}}$,
so $\eta_a\in X'$ as $X'$ is open. Hence $Z=X\setminus X'$ contains no $\eta_a$: for $z\in Z$
lying in $X_a$, $\overline{\{z\}}$ is a proper irreducible closed subset of $X_a$, which has
dimension $\le1$, so $\overline{\{z\}}=\{z\}$. Thus $Z$, closed in the Noetherian $X$, has
finitely many irreducible components, each a closed point: $Z=\{z_1,\dots,z_n\}$ is finite and
discrete. Give $Z$ its reduced induced structure, with closed immersion $i:Z\hookrightarrow X$
[definition-ind-etale-pro-etale-weakly--3]; $Z$ is a separated $k$-scheme of finite type of
dimension $\le0$ (possibly empty), each $z_m$ has residue field finite over $k$, hence equal to $k$
(Nullstellensatz), so $z_m:\operatorname{Spec}k\to X$ is a geometric point $\bar z_m$
[def-weil-geometric-point], and $i$ is finite (a closed immersion). For every open $U\subseteq X$
the same holds for $Z_U=Z\cap U=U\times_XZ$, an open subscheme of $Z$, with closed immersion
$i_U:Z_U\hookrightarrow U$; and $X'\cap U$ is dense in $U$ (Stacks remark (d)). Dependencies:
theorem-cohomology-curves, definition-ind-etale-pro-etale-weakly--3, def-weil-geometric-point.

3. The exact sequence and stalks (Stacks 0GJA, proof: 'Consider the short exact sequence of Lemma
095L'). Put $E=i^{-1}F$ on $Z_{\Et}$ [def-weil-pbc-inverse-image] and $G=i_*E$
[def-weil-pbc-direct-image]. Since $X'=X\setminus i(Z)$, [lem-weil-pbc-open-closed-short-exact]
gives the exact sequence $0\to F'\xrightarrow{\varepsilon}F\xrightarrow{\eta}G\to0$ in
$\Ab(X_{\Et})$. Geometric stalks [def-weil-pbc-geometric-stalks] are filtered colimits, hence
exact, so for every geometric point $\bar x$ the stalk $F'_{\bar x}$ is a subgroup of $F_{\bar x}$
and $G_{\bar x}$ a quotient of it. Consequently: $F'$ and $G$ are torsion (a local section of the
subsheaf $F'$ is one of $F$; a local section of $G$ lifts locally to $F$), so $(X,F')$, $(X,G)$
are curve coefficient pairs [theorem-cohomology-curves]; if $F$ is $p$-primary (resp. prime to
$p$) [def-weil-pbc-primary-torsion], so are $F'$ and $G$ (their stalk elements are elements, resp.
images of elements, of stalks of $F$). Moreover, if $F$ is prime to $p$ and $F'$ is $p$-primary,
or $F$ is $p$-primary and $F'$ is prime to $p$, then every element of every $F'_{\bar x}$ has
order both a power of $p$ and prime to $p$, so all stalks of $F'$ vanish and $F'=0$ by
[lemma-weil-pbc-geometric-stalk-conservative] applied to $0\to F'$. Dependencies:
lem-weil-pbc-open-closed-short-exact, def-weil-pbc-inverse-image, def-weil-pbc-direct-image,
def-weil-pbc-geometric-stalks, theorem-cohomology-curves, def-weil-pbc-primary-torsion,
lemma-weil-pbc-geometric-stalk-conservative.

4. Cohomology of $G$ (Stacks 0GJA, proof: '$H^q(X,i_*i^{-1}F)=H^q(Z,i^*F)$ ... by Proposition 03QP
and the Leray spectral sequence; since $Z$ is a disjoint union of spectra of algebraically closed
fields, $H^q(Z,i^*F)=0$ for $q>0$ and $H^0=\bigoplus F_{x_i}$, which is finite as $F$ is
constructible'). Since $i$ is finite, [lemma-weil-pbc-finite-direct-image-exact] gives $Ri_*E\cong
i_*E=G$ in $\Dplus(X_{\Et})$, and part 1 of [lem-weil-pbc-cohomology-pullback-derived-unit] (for
$u=i$, $L=E$) gives $\RGamma(X_{\Et},Ri_*E)\cong\RGamma(Z_{\Et},E)$; taking $\mathcal H^q$
[def-weil-pbc-etale-cohomology], $H^q(X,G)\cong H^q(Z,E)$ for all $q$. By
[lemma-sheaves-finite-support-finite-morphisms--1] for the zero-dimensional $Z$ (step 2):
$H^q(Z,E)=0$ for $q>0$ and $H^0(Z,E)=\prod_{m}E_{\bar z_m}$, a finite product. Each $E_{\bar z_m}$
is finite: the geometric fibre of the closed immersion $i$ over $\bar z_m$ is the single geometric
point $\bar z_m$ of $Z$, so [lemma-weil-pbc-finite-stalk-formula] gives $E_{\bar
z_m}\cong(i_*E)_{\bar z_m}=G_{\bar z_m}$, a quotient of $F_{\bar z_m}$ (step 3); and $F_{\bar z_m}$
is finite because $F$ is constructible [def-weil-pbc-constructible-torsion]: $z_m$ lies in a stratum
$S$ of the partition, and the stalk of $F$ at the geometric point $\bar z_m$ of $S$ is the stalk
there of the restriction $F|_S$ [def-weil-pbc-inverse-image] (the inverse image along an immersion
does not change stalks, Stacks 03Q1), which is locally constant with finite stalks. Hence
$H^q(X,G)=0$ for $q\ge1$ and $H^0(X,G)$ is finite. Dependencies:
lemma-weil-pbc-finite-direct-image-exact, lem-weil-pbc-cohomology-pullback-derived-unit,
def-weil-pbc-etale-cohomology, lemma-sheaves-finite-support-finite-morphisms--1,
lemma-weil-pbc-finite-stalk-formula, def-weil-pbc-inverse-image, def-weil-pbc-constructible-torsion.

5. Restriction of $G$ to an open (needed for $(\mathcal C_8)$; Stacks remark (d)). Let
$a:U\hookrightarrow X$ be an open immersion, $Z_U=U\times_XZ$ with $i_U:Z_U\hookrightarrow U$ and
open immersion $a_Z:Z_U\hookrightarrow Z$ (step 2). For an open immersion the inverse image is
restriction: $(a^{-1}H)(V\to U)=H(V\to U\to X)$ for $V\in U_{\Et}$, naturally in $V$ and the sheaf
$H$ (the identification in [lem-weil-pbc-extension-by-zero-adjunction], Stacks 03S3 and the
discussion after it). Hence, using $(i_*E)(W)=E(W\times_XZ)$ [def-weil-pbc-direct-image] and
$V\times_XZ=V\times_U(U\times_XZ)=V\times_UZ_U$, an etale $Z_U$-scheme:
$(a^{-1}G)(V)=E(V\times_XZ)=(a_Z^{-1}E)(V\times_UZ_U)=(i_{U*}a_Z^{-1}E)(V)$, naturally in $V$; so
$a^{-1}G\cong i_{U*}(a_Z^{-1}E)$. As in step 4 (with $U$, $Z_U$, $i_U$ for $X$, $Z$, $i$; $Z_U$ is
zero-dimensional, separated and of finite type over $k$, $i_U$ finite), $H^q(U,a^{-1}G)\cong
H^q(Z_U,a_Z^{-1}E)=0$ for $q\ge1$. Dependencies: lem-weil-pbc-extension-by-zero-adjunction,
def-weil-pbc-direct-image, lemma-weil-pbc-finite-direct-image-exact,
lem-weil-pbc-cohomology-pullback-derived-unit, lemma-sheaves-finite-support-finite-morphisms--1.

6. The assertions for $G$ (Stacks 0GJA, proof, remark (c):
'$H^0(Z,i^{-1}F)=H^0(Z_{k'},i^{-1}F|_{Z_{k'}})$'; written via Lemma 0A5D). $(Z,E)$ is a curve
coefficient pair: $E=i^{-1}F$ is torsion, as the inverse image of a torsion sheaf (it is the
sheafification of a presheaf whose values are colimits of groups of sections of $F$,
[def-weil-pbc-inverse-image]). $\mathcal C(Z,E)$ holds: by step 4 the groups $H^q(Z,E)$ vanish for
$q\ge1$ and $H^0(Z,E)$ is finite, which gives the conclusions of $(\mathcal C_1)$-$(\mathcal C_5)$
whatever the hypotheses; every open $Z''\subseteq Z$ is again zero-dimensional, so
$H^2(Z'',E|_{Z''})=0$ by [lemma-sheaves-finite-support-finite-morphisms--1] and $(\mathcal C_8)$
holds; $(\mathcal C_6)$ and $(\mathcal C_7)$ hold by
[lemma-sheaves-finite-support-finite-morphisms--2] ($\rho^q_{k'/k}(Z,E)$ is an isomorphism for every
$q$ and every algebraically closed $k'/k$). Since $i:Z\to X$ is a finite morphism of separated
finite-type $k$-schemes of dimension $\le1$, the finite-pushforward case of the curve assertions
(Stacks 0A5D) gives $\mathcal C(X,G)=\mathcal C(X,i_*E)$. In particular $\rho^q_{k'/k}(X,G)$ is an
isomorphism for all $q$ when $X$ is proper ($\mathcal C_7$), or when $G$ is prime to $p$ ($\mathcal
C_6$). Dependencies: theorem-cohomology-curves, def-weil-pbc-inverse-image,
lemma-sheaves-finite-support-finite-morphisms--1, lemma-sheaves-finite-support-finite-morphisms--2,
theorem-cohomology-curves, theorem-cohomology-curves--6, theorem-cohomology-curves--7.

7. Long exact sequences and ladders (Stacks 0GJA, proof: 'The long exact cohomology sequence gives
an exact sequence $0\to H^0(X,j_!j^{-1}F)\to H^0(X,F)\to H^0(Z,i^{-1}F)\to H^1(X,j_!j^{-1}F)\to
H^1(X,F)\to0$ and isomorphisms $H^q(X,j_!j^{-1}F)\to H^q(X,F)$ for $q>1$'). Apply
[lem-weil-pbc-pullback-cohomology-long-exact-ladder] to the sequence of step 3, once with
$u=\pi_{k'}:X_{k'}\to X$ for an algebraically closed $k'/k$ (the pullback maps $u^*$ of
[def-weil-pbc-cohomology-pullback] are then the maps $\rho^q_{k'/k}$ of
[theorem-cohomology-curves--7]) and once with $u=a:U\hookrightarrow X$ an open immersion: the
pulled-back sequences $0\to u^{-1}F'\to u^{-1}F\to u^{-1}G\to0$ are exact, and the long exact
cohomology sequences on $X$ and on $X_{k'}$ (resp. $U$) are connected by a morphism of long exact
sequences given by $\rho$ (resp. $a^*$). With step 4 ($H^q(X,G)=0$ for $q\ge1$) the sequence on
$X$ yields: (i) $H^q(X,F')\to H^q(X,F)$ is an isomorphism for $q\ge2$; (ii) $0\to H^0(X,F')\to
H^0(X,F)\to H^0(X,G)\to H^1(X,F')\to H^1(X,F)\to0$ is exact. With step 5 ($H^1(U,a^{-1}G)=0$) the
sequence on $U$ yields: (iii) $H^2(U,a^{-1}F')\to H^2(U,a^{-1}F)$ is injective. Dependencies:
lem-weil-pbc-pullback-cohomology-long-exact-ladder, def-weil-pbc-cohomology-pullback,
theorem-cohomology-curves--7, def-weil-pbc-etale-cohomology.

8. Part 1: $\mathcal C(X,F')\Rightarrow\mathcal C(X,F)$ (Stacks writes 'at this point it is easy
to deduce each of (1)-(8) holds for $F$ if and only if it holds for $j_!j^{-1}F$'; this direction
is the dévissage of Lemma 0A5C, outer terms to middle). The sequence $0\to F'\to F\to G\to0$ of
step 3 is a short exact sequence of torsion sheaves on $X_{\Et}$; $\mathcal C(X,F')$ holds by
hypothesis and $\mathcal C(X,G)$ by step 6. Hence [lemma-weil-pbc-eight-curve-devissage] (Stacks
0A5C) gives $\mathcal C(X,F)$. Dependencies: lemma-weil-pbc-eight-curve-devissage,
lem-weil-pbc-open-closed-short-exact.

9. Part 2, assertions $(\mathcal C_1)$, $(\mathcal C_2)$, $(\mathcal C_3)$. The converse cannot
use Lemma 0A5C (that lemma passes from the outer terms to the middle, and here $F'$ is the sub);
Stacks deduces it from the cohomology sequence, assertion by assertion, which is done here and in
the next three steps. Assume $\mathcal C(X,F)$ and that $F$ is $p$-primary or prime to $p$.
$(\mathcal C_1)$: for $q>2$, $H^q(X,F')\cong H^q(X,F)=0$ by step 7(i) and $\mathcal C_1(X,F)$
[theorem-cohomology-curves--1]. $(\mathcal C_2)$: if $X$ is affine, for $q>1$, $H^q(X,F')\cong
H^q(X,F)=0$ by 7(i) and $\mathcal C_2(X,F)$ [theorem-cohomology-curves--2]. $(\mathcal C_3)$
[theorem-cohomology-curves--3]: let $\operatorname{char}k=p>0$ and $F'$ be $p$-primary. If $F$ is
$p$-primary, $H^q(X,F')\cong H^q(X,F)=0$ for $q>1$ by 7(i) and $\mathcal C_3(X,F)$; if $F$ is prime
to $p$, then $F'=0$ by step 3 and the conclusion is trivial. (The hypothesis on $F$ is what makes
this possible: without it, $F$ could be $j_!j^{-1}$ of a $p$-primary sheaf plus a sheaf supported on
$Z$ that is not $p$-primary, and then $\mathcal C(X,F)$ says nothing about $H^q(X,F')$ unless $X$ is
affine; this is a gap in the 'if and only if' of Stacks 0GJA for general torsion $F$, filled by this
hypothesis, which every use of the lemma satisfies.) Dependencies: theorem-cohomology-curves--1,
theorem-cohomology-curves--2, theorem-cohomology-curves--3, def-weil-pbc-primary-torsion.

10. Part 2, assertions $(\mathcal C_4)$, $(\mathcal C_5)$ (Stacks remark (b) and the finiteness of
$H^0(Z,i^{-1}F)$). Let $F'$ be constructible and either prime to $p$ (for $\mathcal C_4$
[theorem-cohomology-curves--4]) or $X$ be proper (for $\mathcal C_5$
[theorem-cohomology-curves--5]). For $(\mathcal C_4)$: if $F$ is $p$-primary (so
$\operatorname{char}k=p>0$), $F'=0$ by step 3 and the conclusion is trivial; otherwise $F$ is prime
to $p$ and constructible (hypothesis of the lemma), so $H^q(X,F)$ is finite for all $q$ by $\mathcal
C_4(X,F)$. For $(\mathcal C_5)$: $F$ is constructible and $X$ proper, so $H^q(X,F)$ is finite by
$\mathcal C_5(X,F)$. In both cases: $H^0(X,F')$ is a subgroup of the finite $H^0(X,F)$ by 7(ii);
$H^1(X,F')$ is an extension of a subgroup of $H^1(X,F)$ by a quotient of the finite group $H^0(X,G)$
(step 4) by 7(ii), hence finite; and $H^q(X,F')\cong H^q(X,F)$ is finite for $q\ge2$ by 7(i).
Dependencies: theorem-cohomology-curves--4, theorem-cohomology-curves--5,
def-weil-pbc-constructible-torsion.

11. Part 2, assertions $(\mathcal C_6)$, $(\mathcal C_7)$ (Stacks remark (c)). Let $k'/k$ be
algebraically closed and either $F'$ prime to $p$ (for $\mathcal C_6$
[theorem-cohomology-curves--6]) or $X$ proper (for $\mathcal C_7$ [theorem-cohomology-curves--7]).
In case $\mathcal C_6$ with $F$ $p$-primary, $F'=0$ (step 3) and the maps $\rho^q_{k'/k}(X,F')$ are
isomorphisms between zero groups. Otherwise ($F$ prime to $p$, hence $G$ prime to $p$ by step 3,
resp. $X$ proper) $\rho^q_{k'/k}(X,F)$ is an isomorphism for all $q$ by $\mathcal C_6(X,F)$ resp.
$\mathcal C_7(X,F)$, and $\rho^q_{k'/k}(X,G)$ for all $q$ by step 6. In the morphism of long exact
sequences of step 7 consider, for each $q\ge0$, the segment $H^{q-1}(F)\to H^{q-1}(G)\to H^q(F')\to
H^q(F)\to H^q(G)$ over $X$ and its counterpart over $X_{k'}$ (with $H^{-1}=0$); the four outer
vertical maps are isomorphisms, so the five lemma [lem-weil-pbc-five-lemma] shows that
$\rho^q_{k'/k}(X,F')$ is an isomorphism. Dependencies: theorem-cohomology-curves--6,
theorem-cohomology-curves--7, lem-weil-pbc-pullback-cohomology-long-exact-ladder,
lem-weil-pbc-five-lemma.

12. Part 2, assertion $(\mathcal C_8)$ (Stacks remark (d)). Let $a:U\hookrightarrow X$ be open and
$b'\in H^2(U,a^{-1}F')$; let $b$ be its image in $H^2(U,a^{-1}F)$. By $\mathcal C_8(X,F)$
[theorem-cohomology-curves--8] there is $c\in H^2(X,F)$ with $a^*c=b$; by 7(i) $c$ is the image of
some $c'\in H^2(X,F')$. By the commutativity of the ladder for $u=a$ (step 7), $a^*c'$ and $b'$ have
the same image $b$ in $H^2(U,a^{-1}F)$, so $a^*c'=b'$ by 7(iii). Hence $a^*:H^2(X,F')\to
H^2(U,a^{-1}F')$ is surjective. With the previous three steps, $\mathcal C(X,F')$ holds
[theorem-cohomology-curves], which is part 2; parts 1 and 2 give the final equivalence,
since a sheaf killed by a prime $r$ is $p$-primary if $r=p$ and prime to $p$ otherwise
[def-weil-pbc-primary-torsion]. Dependencies: theorem-cohomology-curves--8,
lem-weil-pbc-pullback-cohomology-long-exact-ladder, theorem-cohomology-curves,
def-weil-pbc-primary-torsion.
-/
theorem IsCurve.dense_open_assertions {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let F' := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj F'
    (IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G →
      IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F) ∧
    ((Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
      ∃ p : ℕ, p.Prime ∧ CharP k p ∧
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
      IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G) ∧
    (∀ r : ℕ, r.Prime → r • 𝟙 P.F = 0 →
      (IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F ↔
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G)) :=
  by
    dsimp only
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let T := sheafCompose P.C.smallEtaleTopology E
    let F := T.obj P.F
    let G := T.obj ((Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F))
    obtain ⟨hhigh, hprimary₁, hprimary₂⟩ :=
      IsCurve.dense_open_vanishing_comparison P U hU
    obtain ⟨hfinite₁, hfinite₂, hproperFinite₁, hproperFinite₂⟩ :=
      IsCurve.dense_open_finiteness_comparison P hP U hU
    obtain ⟨hbase₁, hbase₂, hproperBase₁, hproperBase₂⟩ :=
      IsCurve.dense_open_baseChange_comparison P U hU
    have hrestrict := IsCurve.dense_open_restriction_comparison P U hU
    have hforward : IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F :=
      fun h ↦ (IsCurve.assertions_iff _ _ _).mpr
      ⟨(fun q hq ↦ ((hhigh q (by omega)).some.toEquiv.subsingleton_congr).mp
          (h.subsingleton_of_two_lt q hq)),
       (fun q hq ↦ ((hhigh q hq).some.toEquiv.subsingleton_congr).mp
          (h.subsingleton_of_one_lt_of_isAffine q hq)),
       hprimary₁ h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf,
       hfinite₁ (@h.finite_of_isTorsionSheafOfInvertibleOrder),
       hproperFinite₁ (@h.finite_of_isProper),
       hbase₁ (@h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder),
       hproperBase₁ (@h.bijective_cohomologyMap_of_isProper),
       hrestrict.mpr h.surjective_cohomologyMap_of_isOpenImmersion⟩
    have hreverse :
        (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F ∨
          ∃ p : ℕ, p.Prime ∧ CharP k p ∧
            Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) F p) →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec F →
        IsCurve.Assertions (ULift.{u + 1} ℤ) P.toSpec G :=
      fun ht h ↦ (IsCurve.assertions_iff _ _ _).mpr
      ⟨(fun q hq ↦ ((hhigh q (by omega)).some.toEquiv.subsingleton_congr).mpr
          (h.subsingleton_of_two_lt q hq)),
       (fun q hq ↦ ((hhigh q hq).some.toEquiv.subsingleton_congr).mpr
          (h.subsingleton_of_one_lt_of_isAffine q hq)),
       hprimary₂ ht h.subsingleton_of_one_lt_of_isPrimaryTorsionSheaf,
       hfinite₂ ht (@h.finite_of_isTorsionSheafOfInvertibleOrder),
       hproperFinite₂ ht (@h.finite_of_isProper),
       hbase₂ ht (@h.bijective_cohomologyMap_of_isTorsionSheafOfInvertibleOrder),
       hproperBase₂ ht (@h.bijective_cohomologyMap_of_isProper),
       hrestrict.mp h.surjective_cohomologyMap_of_isOpenImmersion⟩
    refine ⟨hforward, hreverse, ?_⟩
    intro r hr hkill
    have : (forget₂ (ModuleCat.{u + 1} ℤ)
        AddCommGrpCat.{u + 1}).asEquivalence.functor.Additive := by
      change (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).Additive
      infer_instance
    have : (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv.Additive :=
      (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence.inverse_additive
    have : E.Additive := inferInstance
    have : T.Additive := by
      dsimp [T, sheafCompose]
      infer_instance
    have hkillF : r • 𝟙 (T.obj P.F) = 0 := by
      have hh := congrArg T.map hkill
      rw [T.map_nsmul, T.map_id, T.map_zero] at hh
      exact hh
    have hstalk (Ω : Type u) [Field Ω] [IsSepClosed Ω]
        (s : Spec (.of Ω) ⟶ P.C)
        (x : ↥((Scheme.pointSmallEtale s).sheafFiber.obj (T.obj P.F))) : r • x = 0 := by
      let S := (Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      have : Limits.HasLimitsOfSize.{u, u}
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
        ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
      have : Limits.HasFiniteLimits
          (Sheaf P.C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :=
        inferInstance
      have : S.Additive := by
        exact @GrothendieckTopology.Point.sheafFiber_additive.{u, u + 1, u + 2, u, u + 1}
          _ _ _ (Scheme.pointSmallEtale s) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
          (ModuleCat.moduleCategory.{u + 1, u + 1} (ULift.{u + 1} ℤ))
          inferInstance inferInstance inferInstance inferInstance
      have hh := congrArg S.map hkillF
      rw [S.map_nsmul, S.map_id, S.map_zero] at hh
      simpa using congrArg (fun f : S.obj (T.obj P.F) ⟶ S.obj (T.obj P.F) ↦ f.hom x) hh
    have ht : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (T.obj P.F) ∨
        ∃ p : ℕ, p.Prime ∧ CharP k p ∧
          Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) (T.obj P.F) p := by
      by_cases hrk : (r : k) = 0
      · exact Or.inr ⟨r, hr, (CharP.charP_iff_prime_eq_zero hr).mpr hrk,
          fun Ω _ _ s x ↦ ⟨1, by simpa using hstalk Ω s x⟩⟩
      · refine Or.inl ⟨fun Ω _ _ s x ↦ ⟨r, hr.pos, ?_, hstalk Ω s x⟩⟩
        simpa using (isUnit_iff_ne_zero.mpr hrk).map
          (Scheme.ΓSpecIso (.of k)).inv.hom
    exact ⟨hreverse ht, hforward⟩

end AlgebraicGeometry
