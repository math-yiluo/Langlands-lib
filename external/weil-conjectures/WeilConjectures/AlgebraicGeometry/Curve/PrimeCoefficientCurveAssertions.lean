/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.Curve.Reductions
import WeilConjectures.ConstructibleSheaf.LocallyConstantReduction
import WeilConjectures.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions
import WeilConjectures.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-! # Eight assertions for constructible prime coefficients on reduced curves

Source: Stacks Project, 03SC (theorem-vanishing-affine-curves),
03SD (lemma-vanishing-easier), 0A3Q (lemma-somewhat-easier), 03SG (lemma-even-easier).
(blueprint: e1-prime-coefficient-curve-assertions)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

/-- All eight assertions for a constructible prime-field sheaf on a reduced curve.

Source: Stacks Project, 03SC (theorem-vanishing-affine-curves), constructible prime-field
case; 03SD (lemma-vanishing-easier), 0A3Q (lemma-somewhat-easier), 03SG (lemma-even-easier).
(blueprint: e1-prime-coefficient-curve-assertions)

Proof, matching the nine steps of the node. The auxiliary claims in steps 1--8 concern
all separated finite-type reduced curves, so they can also be applied to the nonproper
opens, finite covers and normalizations occurring in the reduction.

1. Zero-dimensional schemes (Stacks, proof of Lemma 0A5B, first paragraph: higher etale cohomology
of any sheaf on a point vanishes). Let $Z$ be a separated finite-type $k$-scheme of dimension
$\le0$ and $G$ a torsion sheaf on $Z_{\Et}$. By [lemma-sheaves-finite-support-finite-morphisms--1],
$H^q(Z,G)=0$ for $q>0$ and $H^0(Z,G)=\prod_{z\in|Z|}G_{\bar z}$, a finite product; this gives
(C1), (C2), (C3) (all groups in degrees $\ge2$ vanish), and (C4), (C5): if $G$ is constructible
its restriction to each stratum of a finite partition is locally constant with finite stalks, so
each $G_{\bar z}$ is finite. Every open $U\subseteq Z$ is again of dimension $\le0$, so
$H^2(U,G|_U)=0$ and the restriction in (C8) is surjective. (C6) and (C7) are
[lemma-sheaves-finite-support-finite-morphisms--2]. Hence $\mathcal C(Z,G)$ holds
[theorem-cohomology-curves].

Dependency nodes: lemma-sheaves-finite-support-finite-morphisms--1,
lemma-sheaves-finite-support-finite-morphisms--2, theorem-cohomology-curves.

2. Smooth constant coefficients and extension by zero (Stacks 03SG, lemma-even-easier, and 0A5B,
lemma-constant-smooth-statements). Let X be smooth, separated and of finite type over the
algebraically closed k, with dimension at most one. It is Noetherian by
[lem-weil-pbc-finite-type-over-noetherian] and has finitely many irreducible components by
[lem-weil-pbc-noetherian-finitely-many-components]. Its local rings are normal domains by
[lemma-proper-smooth-model--1]. Two distinct irreducible components cannot meet: at an intersection
the local ring would have two distinct minimal primes, contrary to being a domain. Thus the
components are pairwise disjoint; each is open because its complement is the finite union of the
other closed components. Write their inclusions as i_a:X_a -> X, which are closed immersions and
hence finite. For a prime r, if r is nonzero in k, apply
[lemma-weil-pbc-smooth-curve-kummer-localization] to each X_a; otherwise k has characteristic r and
apply [lemma-weil-pbc-smooth-curve-artin-schreier]. These statements supply all eight assertions for
the constant prime-field sheaf, including for points; their smooth-curve calculations follow
[proposition-p-torsion-smooth-proper-curve--1]. For an open j:U -> X, put U_a = U intersect X_a. If
U_a is empty, its extension by zero is zero and all assertions hold. Otherwise U_a is dense in the
irreducible X_a; apply [lem-weil-pbc-curve-assertions-dense-open] to its constant sheaf, which is
constructible and killed by r. This gives the assertions for extension by zero from U_a. Their
finite pushforwards along i_a satisfy the assertions by the finite-pushforward case of the curve
assertions. The stalk formula for [proposition-extension-zero-restriction-closed-subscheme--7]
identifies j_! of the constant sheaf with the finite direct sum of these pushforwards. Split short
exact sequences and [lemma-weil-pbc-eight-curve-devissage] assemble the sum. Zero-dimensional pieces
also follow from step 1.

Dependency nodes: lemma-weil-pbc-smooth-curve-kummer-localization,
lemma-weil-pbc-smooth-curve-artin-schreier, proposition-p-torsion-smooth-proper-curve--1,
def-sc-constant-sheaves, def-weil-pbc-constructible-torsion,
proposition-extension-zero-restriction-closed-subscheme--7,
lem-weil-pbc-curve-assertions-dense-open, lemma-weil-pbc-eight-curve-devissage,
lem-weil-pbc-noetherian-finitely-many-components, lemma-proper-smooth-model--1,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-closed-immersion-finite.

3. Reduced case for $j_!\mathbf F_\ell$ (Stacks Lemma 0A3Q). Claim: if $X$ is a reduced separated
finite-type $k$-scheme with $\dim X\le1$, $j:U\hookrightarrow X$ an open immersion and $\ell$ a
prime, then $\mathcal C(X,j_!\underline{\mathbf Z/\ell})$ holds. Proof. By
[lem-weil-pbc-reduced-curve-normalization] there are a smooth separated finite-type $k$-scheme
$X^\nu$ of dimension $\le1$, a finite morphism $\nu:X^\nu\to X$ and a dense open
$j':X'\hookrightarrow X$ with $\nu^{-1}(X')\to X'$ an isomorphism. Let
$j^\nu:U^\nu=\nu^{-1}(U)\hookrightarrow X^\nu$. By step 2, $\mathcal
C(X^\nu,j^\nu_!\underline{\mathbf Z/\ell})$ holds, hence by the finite-pushforward case of the
curve assertions so does $\mathcal C(X,\nu_*j^\nu_!\underline{\mathbf Z/\ell})$. Over $X'$ the
two sheaves agree: for $W\to X'$ etale, $(\nu_*E)(W)=E(W\times_X X^\nu)$
[def-weil-pbc-direct-image] and
$W\times_XX^\nu=W\times_{X'}\nu^{-1}(X')\cong W$, while extension by zero commutes with
restriction to opens (stalk formula of
[proposition-extension-zero-restriction-closed-subscheme--7]); hence
$j'^{-1}\nu_*j^\nu_!\underline{\mathbf Z/\ell}\cong j'^{-1}j_!\underline{\mathbf Z/\ell}$ (both are
the extension by zero of $\underline{\mathbf Z/\ell}$ from $U\cap X'$). Both sheaves are
constructible [def-weil-pbc-constructible-torsion]: $j_!\underline{\mathbf Z/\ell}$ and
$j^\nu_!\underline{\mathbf Z/\ell}$ are constant on the strata $U$ and its closed complement
(constructible in a Noetherian scheme), and $\nu_*j^\nu_!\underline{\mathbf Z/\ell}$ is then
constructible by [lemma-detection-proper-direct-image--1]. Applying
[lem-weil-pbc-curve-assertions-dense-open] twice for the dense open $j'$: $\mathcal
C(X,\nu_*j^\nu_!\underline{\mathbf Z/\ell})$ gives $\mathcal
C(X,j'_!j'^{-1}\nu_*j^\nu_!\underline{\mathbf Z/\ell})=\mathcal C(X,j'_!j'^{-1}j_!\underline{\mathbf
Z/\ell})$, which gives $\mathcal C(X,j_!\underline{\mathbf Z/\ell})$.

Dependency nodes: lem-weil-pbc-reduced-curve-normalization, def-weil-pbc-direct-image,
proposition-extension-zero-restriction-closed-subscheme--7, def-weil-pbc-constructible-torsion,
lemma-detection-proper-direct-image--1,
lem-weil-pbc-curve-assertions-dense-open.

4. Locally constant coefficients on an irreducible open, trace reduction (Stacks Lemma 03SD, first
paragraph). Let $X$ be a reduced separated finite-type $k$-scheme with $\dim X\le1$,
$j:U\hookrightarrow X$ an open immersion with $U$ irreducible, $\ell$ a prime and $G$ a finite
locally constant sheaf of $\mathbf F_\ell$-vector spaces on $U$; we prove $\mathcal C(X,j_!G)$ in
this and the next three steps. By [lemma-weil-pbc-curve-locally-constant-reduction] there is a
connected finite etale $v:V\to U$ of degree prime to $\ell$ such that $v^{-1}G$ has a finite
filtration with quotients $\underline{\mathbf Z/\ell}_V$, and the unit and trace
$G\xrightarrow{\eta}v_*v^{-1}G\xrightarrow{\operatorname{tr}}G$ compose to
$\deg(v)\cdot\mathrm{id}_G$, an automorphism since $\ell\nmid\deg v$ and $\ell G=0$. Applying the
additive functor $j_!$, the maps $a=j_!\eta:j_!G\to H:=j_!v_*v^{-1}G$ and $b=j_!\operatorname{tr}$
satisfy $b\circ a=\deg(v)\,\mathrm{id}$. Both sheaves are killed by $\ell$, so each is torsion
prime to $p=\operatorname{char}k$ if $\ell\neq p$ and $p$-primary if $\ell=p$
[def-weil-pbc-primary-torsion]; and $H$ is constructible: $v^{-1}G$ is finite locally constant on
the Noetherian $V$ (one stratum), $v_*v^{-1}G$ is constructible on $U$ by
[lemma-detection-proper-direct-image--1] ($v$ is finite), and its extension by
zero is constructible on $X$ (the strata of $U$ together with the closed complement $X\setminus
U$, on which it is $0$) [def-weil-pbc-constructible-torsion]. By
[lem-weil-pbc-curve-assertions-retract] it suffices to prove $\mathcal C(X,j_!v_*v^{-1}G)$.

Dependency nodes: lemma-weil-pbc-curve-locally-constant-reduction, def-weil-pbc-primary-torsion,
lemma-detection-proper-direct-image--1, def-weil-pbc-constructible-torsion,
lem-weil-pbc-curve-assertions-retract.

5. Compactifying $V$ over $X$ (Stacks Lemma 03SD, Zariski's main theorem). The composite $j\circ
v:V\to X$ is quasi-finite (finite etale followed by an open immersion), separated (finite
morphisms and immersions are separated) and of finite type, and $X$ is quasi-compact and
quasi-separated (Noetherian). By [thm-pqf-zmt-factorization] it factors as
$V\xrightarrow{j_0}T\xrightarrow{p}X$ with $j_0$ a quasi-compact open immersion and $p$ finite.
Let $Y\subseteq T$ be the closure of $j_0(V)$ with its reduced induced structure; $Y$ is closed in
$T$, so $\bar f=p|_Y:Y\to X$ is finite, and $Y$ is a separated finite-type $k$-scheme of dimension
$\le\dim X\le1$ (finite morphisms are integral, so they do not raise dimension). $V$ is reduced
(etale over the reduced $U$), so $j_0$ factors through an open immersion $j':V\hookrightarrow Y$
with dense image, and $\bar f\circ j'=j\circ v$. The square with sides $j',v,\bar f,j$ is
cartesian: $j'(V)\subseteq\bar f^{-1}(U)$ is open; the $U$-morphism $V\to\bar f^{-1}(U)$ goes from
a finite $U$-scheme to a separated $U$-scheme, so it is finite, in particular closed; its image is
open, closed and dense in $\bar f^{-1}(U)$, hence all of it, and as both are reduced open
subschemes of $Y$ with the same underlying set, $V=U\times_XY$. The dimension bound follows on
affine charts from [lem-weil-pbc-integral-incomparability]: a strict chain of primes in a finite
algebra contracts to a strict chain in the base. Reduced closure means the radical of the
closed-image ideal; on V that ideal is zero because V is reduced. Thus the inclusion of V remains
an open immersion after this replacement. Finiteness of V -> inverse-image(U) uses
[lem-weil-pbc-finite-permanence-over-separated], and closedness uses
[lem-weil-pbc-finite-closed-map-finite-fibres]. Since this inclusion is both open and closed and
dense, its image is the whole inverse image. A surjective open immersion is an isomorphism,
proving the cartesian assertion without identifying schemes merely by their underlying sets.

Dependency nodes: thm-pqf-zmt-factorization, etale-proposition-etale-reduced,
lemma-schematic-closure-uniqueness--1, def-weil-pbc-scheme-reduction,
lem-weil-pbc-closed-immersion-finite, lem-weil-pbc-finite-composition,
lem-weil-pbc-finite-over-separated-finite-type, lem-weil-pbc-integral-incomparability,
lem-weil-pbc-finite-permanence-over-separated, lem-weil-pbc-finite-closed-map-finite-fibres,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-qc-open-immersion-finite-type.

6. Exchange of $j_!$ and finite direct image (Stacks Lemma 0GJ1, as used in 03SD). For the
cartesian square of step 5 (open immersions $j'$, $j$; $\bar f$ finite; $v$ its base change),
[lemma-weil-pbc-finite-pushforward-extension-zero] says that the comparison morphism
$\beta:j_!v_*E\to\bar f_*j'_!E$ of [lemma-normalization-constant-sheaf--1] is an isomorphism for
every abelian sheaf $E$ on $V_{\Et}$. With $E=v^{-1}G$ this gives $j_!v_*v^{-1}G\cong\bar
f_*j'_!v^{-1}G$. By the finite-pushforward case of the curve assertions for the finite
$\bar f:Y\to X$, it suffices to prove $\mathcal C(Y,j'_!v^{-1}G)$.

Dependency nodes: lemma-weil-pbc-finite-pushforward-extension-zero,
lemma-normalization-constant-sheaf--1.

7. Filtration and reduction to the constant sheaf (Stacks Lemma 03SD, end). Let $0=E_0\subset
E_1\subset\cdots\subset E_m=v^{-1}G$ be the filtration of step 4, with
$E_i/E_{i-1}\cong\underline{\mathbf Z/\ell}_V$. Since $j'_!$ is exact
[proposition-extension-zero-restriction-closed-subscheme--7], $0=j'_!E_0\subset\cdots\subset
j'_!E_m=j'_!v^{-1}G$ is a filtration with quotients $j'_!\underline{\mathbf Z/\ell}$, i.e. there are
short exact sequences $0\to j'_!E_{i-1}\to j'_!E_i\to j'_!\underline{\mathbf Z/\ell}\to0$. Step 3,
applied to the reduced curve $Y$ and the open immersion $j'$, gives $\mathcal
C(Y,j'_!\underline{\mathbf Z/\ell})$, and induction on $i$ with
[lemma-weil-pbc-eight-curve-devissage] gives $\mathcal C(Y,j'_!E_i)$ for all $i$, in particular
$\mathcal C(Y,j'_!v^{-1}G)$. By steps 6 and 4, $\mathcal C(X,j_!G)$ holds.

Dependency nodes: proposition-extension-zero-restriction-closed-subscheme--7,
lemma-weil-pbc-eight-curve-devissage.

8. Constructible $\mathbf F_\ell$-coefficients on a reduced curve (Stacks Theorem 03SC, proof,
third and fourth paragraphs). Let $X$ be a reduced separated finite-type $k$-scheme with $\dim
X\le1$, $\ell$ a prime and $G$ a constructible sheaf of $\mathbf F_\ell$-vector spaces on
$X_{\Et}$. By [theorem-cohomology-curves] there is a dense open
$U=\coprod_aU_a\subseteq X$, a finite disjoint union of irreducible open subschemes
$j_a:U_a\hookrightarrow X$, on which $G$ is finite locally constant, such that $\mathcal C(X,G)$
holds if and only if $\mathcal C(X,j_{a,!}(G|_{U_a}))$ holds for every $a$. Each $G|_{U_a}$ is a
finite locally constant sheaf of $\mathbf F_\ell$-vector spaces on the irreducible $U_a$, so steps
4 to 7 give $\mathcal C(X,j_{a,!}(G|_{U_a}))$. Hence $\mathcal C(X,G)$ holds; in particular, when
$X$ is proper over $k$, its seventh conjunct $\mathcal C_7(X,G)$
[theorem-cohomology-curves] holds.

Dependency nodes: theorem-cohomology-curves, theorem-cohomology-curves.

9. Coefficient bookkeeping. Put R = ULift(F_r). In every R-module stalk multiplication by r is
zero because r = 0 in R, so the underlying abelian sheaf is torsion. The finite coefficient field
is Noetherian, as required by short-exact devissage. The prime-field module structure is uniquely
determined by the abelian group, and [lem-weil-pbc-constructible-torsion-modules-agree] identifies
the finite-stalk constructible stratifications used above with constructibility as modules.
Forgetting modules to abelian groups preserves the local trivializations, inverse image, finite
direct image and extension by zero: the latter two are respectively finite products on stalks and
the original stalk or zero. Hence the eight assertions in step 8 are exactly IsCurve.Assertions R
f F, whose cohomology and all comparison maps are defined on the underlying abelian sheaf
[theorem-cohomology-curves]. This proves the assertion package without selecting only
C7.

Dependency nodes: lem-weil-pbc-constructible-torsion-modules-agree,
theorem-cohomology-curves, def-weil-pbc-etale-constructible-sheaf,
proposition-extension-zero-restriction-closed-subscheme--7, def-weil-pbc-direct-image.
-/
theorem primeCoefficientCurveAssertions {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f] [IsReduced C]
    {r : ℕ} [Fact r.Prime]
    (F : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsConstructibleSheaf F] :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f F := by
  classical
  let R := ULift.{u + 1} (ZMod r)
  have hF : r • 𝟙 F = 0 := by
    have hr : (r : R) = 0 := by simp [R]
    rw [← Nat.cast_smul_eq_nsmul R, hr, zero_smul]
  obtain ⟨n, U, _hdense, _hdisjoint, hirr, _hdim, hlc, hlocal⟩ :=
    exists_dense_assertions_iff_forall_lowerShriek R f r F hF
  apply hlocal.mpr
  intro a
  have : IrreducibleSpace (U a) := Subtype.irreducibleSpace (hirr a)
  have := hlc a
  let G := (Etale.upperStar (ModuleCat.{u + 1} R) (U a).ι).obj F
  obtain ⟨V, v, hvfinite, hvetale, _hconnected, _d, _hdegree, _hfibres,
    ⟨m, W, ι, hzero, hend, hquot⟩, ρ, hρ⟩ :=
    Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_reduction r G
  have := hvfinite
  have := hvetale
  exact filteredFiniteCoverLowerShriekTransfer f (U a).ι r G v m W ι hzero hend hquot
    ρ hρ (by
      intro Y T g _ _ b _
      exact reducedConstantLowerShriekAssertions g b r)

end AlgebraicGeometry.IsCurve
