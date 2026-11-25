/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal

/-! # Kummer and diagonal classes of coefficient towers

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: proposition-sp-tower-geometric).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale

open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (S : Scheme.{u})

/-- The four canonical constructions of the classes unit, in the actual coefficient
system category and its ordinary unbounded derived category. All named maps above
are definitions; the fields below assert the specified normalizations and that
b_q, formed from the unit and the hyperplane Chern class, is an isomorphism.
Source: blueprint main-20261015, chap-Smooth-purity,
sk-prop-sp-tower-geometric-classes (blueprint: proposition-sp-tower-geometric).
Proof plan from the DAG:

1. Kummer exactness on the pro-etale site is a local consequence of
[lemma-cycle-class-cartier-divisor]. For a pro-etale object $U\to S$ and $u\in\Gamma(U,\mathcal
O_U)^\times$, apply that lemma on the scheme $U$ with exponent $\ell^n$. It supplies an etale cover
of $U$ on which $u$ is an $\ell^n$th power. Such a cover is also a cover in the pro-etale site
[def-weil-pbc-proetale- site], so the power map on the specified pro-etale units sheaf is an
epimorphism. Its kernel is $\mu_{\ell^n}$ by [definition-tate-twists--1]. Kernels and cokernels of
inverse systems are levelwise, as for the system topos in [prose-09-21]. The maps form a
sequence of towers because $(u^\ell)^{\ell^n}=u^{\ell^{n+1}}$, and a root of unity maps to its
$\ell$th power. This proves (1); no change-of-site identification of the entire units sheaf is
being assumed.

2. Construct the integral class of $L$ before introducing finite coefficients. On a Zariski
trivializing cover choose frames $e_a$ of $L$ and let its transition units be defined by
$e_b=g_{ab}e_a$, so $g_{ab}g_{bc}=g_{ac}$. The section $(u,m)_a$ below is to be read as the
frame $ue_a^{m}$ of $L^{\otimes m}$; then $ue_b^m=g_{ab}^mue_a^m$ gives the gluing rule, and
this direction of the transitions is the one for which the construction is the class of $L$
rather than of $L^{-1}$. Glue the sheaves $\mathbf G_m\times\mathbf Z$ with abelian group law
$(u,m)(v,k)=(uv,m+k)$ by $(u,m)_b\mapsto(g_{ab}^{m}u,m)_a$. The cocycle identity gives the
gluing identity; the kernel at $m=0$ is $\mathbf G_m$, and the projection to $m$ is locally
split. Thus this explicitly constructs an extension $0\to\mathbf G_m\to E_L\to\mathbf Z\to0$ on
the pro-etale site. Its connecting morphism $\lambda_L:\mathbf Z\to\mathbf G_m[1]$ exists and is
the extension class by [lem-weil-pbc-ext-one-extension-classification]. Changing frames gives an
isomorphic extension fixing endpoints. On the etale site the identical construction is precisely
the line-bundle torsor class, by the named construction in
[lemma-cohomology-multiplicative-group--3] and the line- bundle/torsor correspondence
[lemma-cohomology-multiplicative-group--3]; both statements allow arbitrary schemes. Hence the
pro-etale extension just written fixes the same Kummer sign and convention, without assuming a
pro-etale Picard comparison theorem. Taking constant towers is exact (all kernels and cokernels are
levelwise), so the constant extension and its connecting morphism define the line-bundle class in
the tower category.

3. Make coefficient linearity part of the construction. Let $\mathscr X$ be the topos of inverse
systems of sheaves on $S_{\mathrm{proet}}$ supplied by [prose-09-21].
Apply [lem-pur-derived-change-of-rings] on a site presenting this topos to the ring map $\mathbf
Z_\bullet\to R_\bullet$. It gives the exact functor $T_R(K)=R_\bullet\otimes^L_{\mathbf
Z_\bullet}\operatorname{const}(K)$ with values in $D(\operatorname{Mod}_{R_\bullet}(\mathscr
X))$, not merely in abelian systems. To check its evaluations, choose a K-flat resolution with
flat terms on $S_{\mathrm{proet}}$. The constant-system functor is inverse image of a geometric
morphism: it preserves finite limits and is left adjoint to inverse limit. By [lem-weil-pbc-
ringed-topoi-derived-tensor-pullback] it preserves these K-flat resolutions. Constant flat terms
remain flat since tensor and exactness of systems are componentwise. Thus a single model
$P\otimes R_\bullet$ computes $T_R(K)$ and all evaluations $P\otimes\mathbf Z/\ell^n$. The
evaluation isomorphisms commute with transitions because the latter maps are the actual quotient
maps in this model.

4. Compute the target of $T_R(\lambda_L)$. After forgetting the new scalar action, resolve
$R_\bullet$ by the two-term system $Q_n=[\mathbf Z\xrightarrow{\ell^n}\mathbf Z]$ in degrees
$-1,0$, with transition $(\ell,1):Q_{n+1}\to Q_n$. Each term is a flat system (tensor and
exactness are levelwise). This bounded complex is K-flat directly: tensoring with any acyclic
system is the cone of a map between two acyclic systems, hence acyclic. Therefore the K-flat
tensor construction of [lem-pur-derived-change-of-rings] computes the underlying $T_R(\mathbf
G_m)$ by $[\mathbf G_m\xrightarrow{\ell^n}\mathbf G_m]_n$. By the Kummer-exactness step its only
cohomology is $(\mu_{\ell^n})_n$ in degree $-1$, with transition $\zeta\mapsto\zeta^\ell$. Use
the positive kernel inclusion $(\mu_{\ell^n})_n[1]\to[\mathbf G_m\xrightarrow{\ell^n}\mathbf
G_m]_n$ for this cohomology identification. Define the identification $T_R(\mathbf
G_m[1])\simeq(\mu_{\ell^n})_n[2]$ by shifting this identification through the exact functor's
shift isomorphism; this fixes its sign. These are identifications inside the module derived
category: canonical truncation identifies an object with its unique nonzero cohomology, and
[definition-tate-twists] identifies that cohomology's level-$n$ action with its
unique $\mathbf Z/\ell^n$ action. Also $T_R(\mathbf Z)=R_\bullet$. Apply $T_R$ to $\lambda_L$ to
obtain the stated $R_\bullet$-linear Chern morphism.

5. Check the abelian boundary, rather than identifying arbitrary abelian Ext with module Ext.
The ordinary tensor units of [sk-def-sfb-change-of-scalars] on K-flat resolutions define a
natural map from a complex to the scalar-forgotten derived extension: for a K-flat resolution
$P\xrightarrow{\sim}K$ use the roof $K\xleftarrow{\sim}P\to P\otimes R_\bullet$; naturality and
independence follow from the resolution comparisons in [lem-pur-derived-change-of-rings].

6. Check its sign first before shifting. Write $0\to U\xrightarrow{i}M\xrightarrow{f}N\to0$ for
the Kummer tower sequence of the Kummer-exactness step, so $U=(\mu_{\ell^n})_n$, $M$ has power
transitions, and $N$ has identity transitions. Set $C=[U\xrightarrow{i}M]$ and
$D=[M\xrightarrow{f}N]$ in degrees $-1,0$. The augmentation $v:C\to N$ is $f$ in degree zero,
and the cone projection is $p:C\to U[1]$. With the convention of [def-weil-abstract-derived-
category] and [lem-sf-derived-ses-triangle], the boundary is $\delta=-p v^{-1}$. Let $a:N\to D$
be the degree-zero inclusion and $j:U[1]\to D$ the positive kernel inclusion. The map
$av+jp:C\to D$ is null-homotopic: take the sole nonzero homotopy $h^0=1_M:C^0\to D^{-1}$; then
$d_Dh+hd_C$ has components $i$ in degree $-1$ and $f$ in degree zero. Hence
$j^{-1}a=-pv^{-1}=\delta$ in the derived category of abelian systems. In the model $N\otimes Q$
of the two-term target-computation step, the tensor unit is precisely $a$. Shift this equality
using the target normalization fixed in the two-term target-computation step to obtain
$\delta[1]$ for $\mathbf G_m[1]$. The homotopy is a map of entire systems, since its middle term
has the power transitions on both sides.

7. Naturality of the tensor unit gives $\operatorname{Res}(T_R(\lambda_L))\circ(\mathbf
Z_\bullet\to R_\bullet)=\delta[1]\circ\operatorname{const}(\lambda_L)$. Thus precomposition with
the integral generator realizes the Chern morphism as the boundary in (2). Evaluation gives the
identical formula for the finite Kummer boundary, with the same transition $(\ell,1)$ on its
two-term models. The scalar-extension adjunction is used in the abelian sheaf setting of the
integral and scalar-extension constructions, where finite colimits exist; the revised finite-
colimit proviso for right exactness imposes no additional hypothesis here.

8. Extend $T_R(\lambda_L)$ along $R_\bullet\to A_\bullet$ using [lem-pur-derived-change-of-
rings], on the same inverse-system topos. This constructs an $A_\bullet$-linear morphism, and
evaluation computes finite scalar extension by the K-flat model argument of the K-flat scalar-
extension step; the source becomes $A_\bullet$. Apply [definition-tate-twists](1)
with $X=S$ and the fixed prime $\ell$ and extension $E$, choosing an auxiliary algebraic closure
containing $E$ as in that node's preamble. Its clause (1) supplies one pro-etale cover
$\widetilde S\to S$ and generators $\zeta_n$ with $\zeta_{n+1}^\ell=\zeta_n$. The maps
$a\mapsto\zeta_n^a$ identify the entire root tower with $R_\bullet$ on that cover: the
transition sends $\zeta_{n+1}^a$ to $\zeta_n^{\bar a}$, where $\bar a$ is reduction modulo
$\ell^n$. Thus the root tower is locally free of rank one over $R_\bullet$, and tensoring with
it is exact because exactness and tensor are computed levelwise. Its derived extension is
therefore the degree-zero tower $A_\bullet(1)$, and its dual is the inverse line tower. At each
level the finite ring $A_n=\mathcal O_E/\ell^n$ is commutative and killed by $\ell^n$; taking
$A=A_n$ and $r=n$ is precisely the finite-coefficient convention of [definition-tate-twists],
where finite discrete coefficient rings have constant coefficient sheaves. Its displayed
$B_{E,n}$ is this $A_n$, and its transition $u\otimes a\mapsto u^\ell\otimes\bar a$ is exactly
the transition of our $A_\bullet(1)$. The isomorphism of clause (2) of [det-def-sp-tate-twist-
locally-free] also identifies any larger annihilating level with this one. No assertion about
the integral, rational or algebraically closed bounded constructible categories in that node's
revised clause (3) is used. Step 7 evaluated at $n$ is now the finite scalar-extended Kummer
class, proving all of (2), with the power transitions on roots and quotient transitions on
coefficients.

9. Fix $W=P\times_SP$ and $F=\Delta_*\mathbf Z_P$. In the current statement of [det-prop-
diagonal-tower-system], the units in the exact pole extension are $B=\nu_W^{-1}\mathbf
G_{m,W,\mathrm{et}}$, rather than the sheaf $G=\mathbf G_{m,W}$ of all pro-etale units. Let
$a:B\to G$ be the map adjoint to the identity on units on etale objects, using [def-weil-pbc-
site-comparison-morphism]. Clause (1) supplies $0\to B\to\mathcal M_\Delta\to F\to0$, with
$t^{-1}\mapsto+1$. Put $C_\Delta=[B\to\mathcal M_\Delta]$ in degrees $-1,0$, with quotient
quasi-isomorphism $v:C_\Delta\to F$ and positive projection $p:C_\Delta\to B[1]$. By the cone
convention in [def-weil-abstract-derived-category] and [lem-sf-derived-ses-triangle] its
connecting morphism is $\beta_B=-pv^{-1}$. Define $\beta_\Delta=a[1]\beta_B$. Clause (3) of the
diagonal-system statement supplies only the source reduction $T(F)\simeq\Delta_*R_\bullet$ used
below. We do not use its target-system identification or clause (4). The target normalization is
fixed by the two-term computation; the finite Cartier comparison is applied below.

10. Check the normalization directly. Let $\rho:\mathbf Z_W\to F$ send $1$ to $1$ on the
diagonal. On etale charts with equations $t_b=g_{ab}^{-1}t_a$, the lifts $s_a=t_a^{-1}$ have
ratios $s_b/s_a=g_{ab}$, the transitions of $\mathcal O_W(\Delta)$. The pullback of the pole
extension along $\rho$ is locally $B\times\mathbf Z$, with $(b,m)_b\mapsto(g_{ab}^m b,m)_a$; the
map to the pole sheaf sends $(b,m)$ to $b t_a^{-m}$. This is an isomorphism onto the pullback: a
section over a fixed exponent differs from its chosen lift by a unique section of the kernel
$B$. The maps $(b,m)\mapsto(a(b),m)$ define a morphism from this extension to the explicitly
constructed full-units extension $E_{\mathcal O_W(\Delta)}$ in the integral line-bundle-
extension step. They commute with the transitions because $a(g_{ab})=g_{ab}$, and have endpoint
maps $a$ and the identity of $\mathbf Z$. Naturality of connecting morphisms, or the commuting
maps of the two cones with their negative projections, gives $a[1]\beta_B\rho=\lambda_{\mathcal
O_W(\Delta)}$. The endpoint convention is the one in [lem-weil-pbc-ext-one-extension-
classification]. No isomorphism $B\simeq G$ is assumed.

11. Apply the module-valued exact functor $T_R$ of the K-flat scalar-extension step to this
corrected integral morphism, using [lem-pur-derived-change-of-rings]. The underlying source
reduction is the cited $T(F)$, and it has only degree-zero cohomology $\Delta_*R_\bullet$.
Truncation inside the module derived category and the unique levelwise quotient actions of [lem-
pur-torsion-sheaf-constant-module] identify the source there. Identify the target with
$(\mu_{\ell^n})_n[2]$ using exactly the positive-kernel identification and shift normalization
of the two-term target-computation step; do not alter that identification for the supported
class. This produces the $R_\bullet$-linear supported morphism
$T_R(\beta_\Delta)=-T_R(a[1])T_R(\partial)$, where $\partial=pv^{-1}$ is the cited positive roof
with target $B[1]$. Applying the additive functor to the preceding integral equality shows that
its composite with $R_{\bullet,W}\to\Delta_*R_{\bullet,P}$ is the Chern morphism of $\mathcal
O_W(\Delta)$. All maps are constructed on entire systems before evaluation.

12. Extend the corrected map $T_R(\beta_\Delta)$ from $R_\bullet$ to $A_\bullet$ using [lem-pur-
derived-change-of-rings]. By [lem-pur-twist-sheaf-locally-free](3), $\mathcal O_E$ is finite
free over $\mathbf Z_\ell$; a fixed basis reduces to compatible bases of $A_n$ over $R_n$. Thus
$A_\bullet$ is finite free over $R_\bullet$, and its tensor functor is exact levelwise. In such
a basis the canonical map $A_\bullet\otimes_{R_\bullet}\Delta_*R_\bullet\to\Delta_*A_\bullet$ is
the identity on the corresponding finite direct sum of copies of $\Delta_*R_\bullet$. Step 8
identifies the target as $A_\bullet(1)[2]$. Define $\delta_\bullet$ by this extension, retaining
the source and target identifications of the integral supported-class construction.

13. Apply [lem-sp-cartier-reduction-site-comparison] with $Z=W$, $D=\Delta$, $r=n$, $R=\mathbf
Z/\ell^n$ and $\Lambda=A_n$. The ring $A_n$ is finite commutative and killed by $\ell^n$ even
for ramified $E$; $\ell$ is invertible on $W$. The compatible charts of [def-nagata-relative-
projective-space] and their identification with $P$ in [def-nagata-projective-space-base-change]
give chart rings $C[x,y]$ over every affine base $\operatorname{Spec}C$. On equal charts the
diagonal equation is $x-y$, monic in $x$. On opposite charts it is $xy-1$; writing $f=\sum
f_k(y)x^k$, the equality $(xy-1)f=0$ gives $f_0=0$ and $f_k=yf_{k-1}=0$. Thus both equations are
non-zero-divisors over arbitrary base rings. The new lemma identifies evaluation of the entire
reduced supported boundary, with precisely the quotient source and positive kernel target fixed
above, with the finite Cartier class. Evaluation commutes with scalar extension by the K-flat
models already constructed. Applying these additive functors to the integral equality
$\beta_\Delta\rho=\lambda_{\mathcal O(\Delta)}$ gives
$\delta_\bullet\circ(A_{\bullet,W}\to\Delta_*A_{\bullet,P})=c_1(\mathcal O_W(\Delta))$. This
proves clause (3) without inferring equality of supported morphisms from this composite alone.

14. By [lemma-nagata-projective-space-base-change-proper] with the two-element index set
$\{0,1\}$, $q:P\to S$ is proper. Use its compactification $q=q\circ\mathrm{id}_P$ when applying
[prose-09-23]. The coefficient sheaf and its twists and shifts are bounded below,
as required by that node's $D^+$ hypothesis. Use the canonical ringed-topos derived adjunction
of [lem-weil-pbc-ringed-projection-mate-exact] for the levelwise morphism of inverse-system
topoi induced by q. The hyperplane line on each affine base open is [def-pc-projective-space-
twist] with $d=1$: its frames satisfy $e_i=(T_i/T_j)e_j$. These transition functions commute
with restriction on the base, so they glue to the specified $\mathcal O_P(1)$. Form $b_q$ by the
tower adjunction unit and the adjoint of the Chern morphism of $\mathcal O_P(1)$, untwisted and
shifted on its source. Clause (1) of [prose-09-23] supplies the bounded-below
direct-image comparison. To check evaluation of the actual adjunction maps, apply [lem-coef-
semilinear-derived-sections] with the strict coefficient system $B_n=(A_n)_S$ and the pro-etale
inverse image of $q$. The pulled-back coefficient system is $(A_n)_P$, since inverse image
preserves constant sheaves. This lemma explicitly preserves evaluation, units, counits, tensor
products and adjunction transposes, so the constructed tower unit/Chern map evaluates to the
same map over $A_n$. The canonical identification of the pulled-back twist with the twist on $P$
follows from the single compatible-generator cover of the compatible-root trivialization step:
its pullback sends each generator to the same root and the local coefficient-line identification
to the identity. No unrestricted projection-formula isomorphism from clause (2)(a) is used.

15. This finite map is invertible without Noetherianity of $S$. Apply [det-sp-p1-trace](1) over
$R_n=\mathbf Z/\ell^n$. Its $h$ and twist are pulled back from the etale site by $\nu_P^*$. For
a line bundle $L$, the step-2 gluing with etale units pulls back to an extension of $\mathbf Z$
by $B=\nu^{-1}\mathbf G_{m,\mathrm{et}}$, and $(b,m)\mapsto(a(b),m)$, $a$ as in (3) [def-weil-
pbc-site-comparison-morphism], maps it to $E_L$ fixing $\mathbf Z$, as $a(g_{ab})=g_{ab}$. The
naturality in [lem-sfb-divisible-extension-derived-reduction] (hypotheses by step 1; $\mathbf Z$
is torsion-free), for this map and exact $\nu^{-1}$, carries the pulled etale Kummer class to
ours through $\nu^{-1}\mu_{\ell^n,\mathrm{et}}\to\mu_{\ell^n}$, an isomorphism fixing etale
local generators [lem-asd-finite-etale-twist-line]; the normalization is that of step 6. On
restricting $A_n$-modules to $R_n$, $A_n$ is a finite direct sum of $R_n$ in the fixed integral
basis. Canonical composition of ringed-topos derived direct images [lem-weil-pbc-ringed-topoi-
derived-pushforward-composition] applied to the two factorizations of the coefficient-change
square identifies restriction of $Rq_{*,A_n}$ with $Rq_{*,R_n}$ of restriction; exact
restriction is its termwise derived functor, as in [sk-def-sfb-change-of-scalars](4). Thus the
restriction of $(b_q)_n$ is the direct sum of these $R_n$ projective-line isomorphisms: on the
$j$th basis vector its Chern component is $e_j\otimes c_1(\mathcal O(1))$ by the compatible-root
trivialization step, and its unit component is $e_j$ times the unit. Finite direct sums commute
with an additive derived direct image. Restriction keeps cohomology sheaves, so it reflects
isomorphisms. Hence $(b_q)_n$ is invertible over $A_n$. Finally [prose-09-23](3)
implies $b_q$ is invertible in the tower module derived category. For clause (4) of the scalar-
change node, the sheaf category is abelian with additive tensor, so its revised clause (2)
proviso holds.

16. Put $V=A_{\bullet,S}(1)[2]$, an invertible object with inverse
$V^{-1}=A_{\bullet,S}(-1)[-2]$ by the compatible-root trivialization step. Write $L=q^{-1}$ and
$R=Rq_{*,\bullet}$ for the derived adjunction of [lem-weil-pbc-ringed-projection-mate-exact];
its pullback tensor comparison gives $L(V^{-1})=(LV)^{-1}$. For any $M$ and $C$, tensoring by
these inverse lines and applying that adjunction gives natural bijections
$$
\operatorname{Hom}(M,RC\otimes V)\cong\operatorname{Hom}(M\otimes
V^{-1},RC)\cong\operatorname{Hom}(LM\otimes LV^{-1},C)\cong\operatorname{Hom}(LM,C\otimes
LV)\cong\operatorname{Hom}(M,R(C\otimes LV)).
$$
The forward map is the counit-tensor transpose
specified in the cited node: transpose, cancel the inverse line and transpose back. Running
these bijections backwards gives its inverse; their composites are identities by the
evaluation/coevaluation cancellations for the line and the adjunction triangle identities. Thus
the projection map is invertible for this $V$ over the arbitrary scheme $S$, without applying
the restricted general projection theorem of [prose-09-23](2)(a). Take
$C=A_{\bullet,P}$ and use $LV=A_{\bullet,P}(1)[2]$ from the generator calculation in the
unit/Chern-map construction. Tensor $b_q$ with $V$ and compose with this projection isomorphism
to obtain $A_{\bullet,S}(1)[2]\oplus A_{\bullet,S}\simeq Rq_{*,\bullet}(A_{\bullet,P}(1)[2])$.
Define $\operatorname{Tr}_{q,\bullet}$ to be the second projection after its inverse. By [lem-
coef-semilinear-derived-sections], evaluation preserves the tensor, counit-tensor transpose,
adjunctions and compositions in this construction, and it preserves inverses by functoriality.
The evaluated splitting is therefore precisely the twist of the finite unit/Chern splitting, so
[det-sp-p1-trace](2) identifies its second projection with the finite trace, extended to $A_n$.
This proves (4) with the stated trace type.
-/
structure TowerClasses (hS : IsUnit (l : Γ(S, ⊤))) where
  base : SpTowerShriek.Base l E
  chernS : Chern l E S
  chernP : Chern l E (ProjectiveLine S)
  chernW : Chern l E (diagonalSurface S)
  chernS_normalized : chernS.Normalized l E
  chernP_normalized : chernP.Normalized l E
  chernW_normalized : chernW.Normalized l E
  /-- Every finite evaluation is the finite Kummer boundary with the quotient
  source and the actual root-tensor target, not a freely chosen Prop. -/
  chernS_levels : FiniteChernNormalization l E chernS
  chernP_levels : FiniteChernNormalization l E chernP
  chernW_levels : FiniteChernNormalization l E chernW
  twistS : Twisting l E chernS
  twistP : Twisting l E chernP
  diagonal : Diagonal l E base S chernW
  diagonal_levels : FiniteDiagonalNormalization l E diagonal
  projective : Projective l E base S chernS chernP twistS twistP
  /-- This is the actual biproduct map defined from the unit and c1(O(1)). -/
  [splitting : IsIso (projective.bq l E)]
  /-- The finite trace vanishes on the finite twisted-unit component. -/
  trace_unit :
    ∀ n : ℕ,
      (SpTowerShriek.Ev l E S n).map (projective.twistedUnit l E) ≫
        (SpTowerShriek.Ev l E S n).map (projective.trace l E) = 0
  /-- The finite trace sends the finite hyperplane class to one. Together with
  the finite projective-line decomposition this characterizes its usual trace. -/
  trace_chern :
    ∀ n : ℕ,
      (SpTowerShriek.Ev l E S n).map (projective.chernAdjoint l E) ≫
        (SpTowerShriek.Ev l E S n).map (projective.trace l E) =
          𝟙 ((SpTowerShriek.Ev l E S n).obj (SpTowerClasses.unit S (Arings l E S)))

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
