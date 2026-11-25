/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionSiteRestriction
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionClosedComparisons
import WeilConjectures.CategoryTheory.Endofunctor.FixedPairCreatedLimits
import WeilConjectures.CategoryTheory.Endofunctor.EquivalenceOrbitInduction
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra

/-! # The ringed site of a site automorphism

The site restriction and closed comparisons are combined with created fixed-pair limits
and exact integer-orbit induction. All data are re-exported from the data module.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

omit [s.functor.IsContinuous J J] in
/-- Canonical small-limit lifting for the module translation forgetful functor.

Source: step 2 of the action-site assembly (step 5 of the detailed proof below), in
`literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/`
`sk-def-ops/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.md`.
(blueprint: lem-sf-twisted-action-ringed-site).

For each diagram, compose the generic full-subcategory and endofunctor-algebra lifts.
The module-sheaf limit exists, and translation preserves it because it is an equivalence.
-/
noncomputable instance translationForgetCreatesLimits [(sigma J s R a).IsEquivalence] :
    CreatesLimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)) := by
  change CreatesLimitsOfSize.{u, u}
    ((Endofunctor.Algebra.IsIsoStr (sigma J s R a)).ι ⋙
      Endofunctor.Algebra.forget (sigma J s R a))
  exact ⟨fun {_} _ ↦ inferInstance⟩

/-- Canonical small-colimit lifting for the module translation forgetful functor.

Source: step 2 of the action-site assembly (step 5 of the detailed proof below), in
`literature/blueprint/latest/blueprint/part-duality-trace-formula/`
`sec-poincare-duality/sec-perfect-complexes-on-the-point-and-two-exchange-formulas/`
`sk-def-ops/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.md`.
(blueprint: lem-sf-twisted-action-ringed-site).

For each diagram, compose the generic full-subcategory and endofunctor-algebra lifts.
The module-sheaf colimit exists, and translation preserves it because it is an equivalence.
-/
noncomputable instance translationForgetCreatesColimits [(sigma J s R a).IsEquivalence] :
    CreatesColimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)) := by
  change CreatesColimitsOfSize.{u, u}
    ((Endofunctor.Algebra.IsIsoStr (sigma J s R a)).ι ⋙
      Endofunctor.Algebra.forget (sigma J s R a))
  exact ⟨fun {_} _ ↦ inferInstance⟩

omit [s.functor.IsContinuous J J] in
private theorem addLimits (P : RestrictionPresentation J s R a) :
    Nonempty (ModulePresentation J s R a) := by
  have : (sigma J s R a).IsEquivalence := by
    rw [← P.translation_eq]
    infer_instance
  have : (sigma J s R a).Additive := by
    constructor
    intro M N f g
    ext X x
    rfl
  exact ⟨{
    toRestrictionPresentation := P
    conservative := inferInstanceAs
      (Endofunctor.IsoAlgebra.forget (sigma J s R a)).ReflectsIsomorphisms
    createsLimits := inferInstanceAs
      (CreatesLimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)))
    createsColimits := inferInstanceAs
      (CreatesColimitsOfSize.{u, u} (Endofunctor.IsoAlgebra.forget (sigma J s R a)))
    exact_limits := inferInstanceAs
      (PreservesFiniteLimits (Endofunctor.IsoAlgebra.forget (sigma J s R a)))
    exact_colimits := inferInstanceAs
      (PreservesFiniteColimits (Endofunctor.IsoAlgebra.forget (sigma J s R a))) }⟩

omit [s.functor.IsContinuous J J] in
private theorem addOrbit (P : ModulePresentation J s R a) :
    Nonempty (OrbitPresentation J s R a) := by
  have : (sigma J s R a).IsEquivalence := by
    rw [← P.translation_eq]
    infer_instance
  have : (sigma J s R a).Additive := by
    constructor
    intro M N f g
    ext X x
    rfl
  have : IsGrothendieckAbelian.{u} (Modules R) :=
    (SheafOfModules.grothendieckAbelian_with_localized_generator J R).1
  obtain ⟨I⟩ := Endofunctor.IsoAlgebra.exists_exactOrbitInduction (sigma J s R a)
  let P' : ModulePresentation J s R a :=
    { P with translation := (sigma J s R a).asEquivalence, translation_eq := rfl }
  exact ⟨{
    toModulePresentation := P'
    induction := I.induction
    inductionAdjunction := I.adjunction
    inductionSum := I.sum
    translationStep := I.step
    induction_shift := I.shift
    induction_zero := I.zero
    induction_add := I.add
    induction_limits := I.limits
    induction_colimits := I.colimits }⟩

/-- The semidirect ringed site, with exact orbit induction and its tensor/Hom calculus.

Source: Stacks Tag 00W0 is motivation only; the twisted assertion is agent-formulated
(blueprint: lem-sf-twisted-action-ringed-site).

Proof plan:

1. Use coherent powers of $s$, inserting the chosen inverse and its coherence isomorphisms in the
formulas. The identity is $(0,1_U)$. Both associations of three arrows $(n,f),(m,h),(l,a)$ have
degree $n+m+l$ and map $s^{n+m}(a)\circ s^n(h)\circ f$, so define a category $D$. Each hom set is
the small union $\coprod_{n\in\mathbf Z}\operatorname{Hom}_C(U,s^nV)$; hence $D$ is small in
[prose-01-10]. Write $a_{n,V}=(n,1_{s^nV}):s^nV\to V$; its inverse is $a_{-n,s^nV}$.
Every arrow $(n,f)$ factors uniquely as $a_{n,V}\circ(0,f)$.

2. A pullback of $(n,f):U\to W$ and $(m,h):V\to W$ is obtained from $P=s^{-n}U\times_Ws^{-m}V$ in
$C$ with projections of degrees $-n,-m$. For a competing cone from $T$, equality of composite
degrees gives a common $l$; translating its two legs by $s^{-l}$ gives a unique map $s^{-l}T\to
P$, hence the unique degree-$l$ map $T\to P$. In particular a degree-zero covering pulled back
along $(n,f)$ has the degree-zero covering $\{U\times_{s^n V}s^nV_i\to U\}$, since $s^n$
preserves coverings. Composites of degree-zero coverings are degree-zero coverings. Together with
singleton isomorphisms these generate a covering basis: pullbacks and composites reduce, by the
displayed factorization, to coverings in $C$. Thus the generated topology on $D$ has exactly the
sheaves whose degree-zero restriction is a $J$-sheaf: the matching and unique-gluing conditions
for a generating covering are those on $C$, and the other basis coverings are isomorphic
translates of these.

3. For a presheaf $F$ on $D$, put $M=F|_C$ and $t_{n,V}=F(a_{n,V}):M(V)\to M(s^nV)$.
Contravariance gives $t_{n+m,V}=t_{n,s^mV}\,t_{m,V}$ and naturality $M(s^nf)t_{n,V}=t_{n,U}M(f)$
for $f:U\to V$. Conversely these formulas and $t_0=1$ define a presheaf by $F(n,f)=M(f)t_{n,V}$:
for composable arrows the restriction composite is $M(f)M(s^nh)t_{n,s^mW}t_{m,W}=M(s^nh\circ
f)t_{n+m,W}$. Negative iterates are forced by inverses. Therefore $t_1$ alone determines the
data. In the inverse-image convention $s^{-1}M(V)=M(s^{-1}V)$, the isomorphism $\theta:s^{-1}M\to
M$ corresponds to $t_{1,V}=\theta_{sV}$. Natural transformations correspond exactly to
intertwining maps. Step 2 restricts this correspondence to sheaves of sets.

4. Apply step 3 to $R$ and its chosen ring isomorphism. All $t_{n,V}$ are ring isomorphisms and
their coherence is forced by iteration, so it gives a ring sheaf $R_{\rtimes}$, restricting
literally to $R$. Apply the same construction to an $R$-module with its semilinear $t_1$. The
equation $t_n(rx)=t_n(r)t_n(x)$ is preserved under composition and inversion and says exactly
that all $F(n,f)$ are semilinear restriction maps. Thus [situation-conventions]
identifies its objects with $R_{\rtimes}$-modules; its morphisms are precisely the intertwining
module morphisms. The constructions are inverse on sections and maps, and respect sums of maps,
proving the additive equivalence with $\mathcal B$.

5. Limits and colimits exist in $\mathcal A$ by [situation-conventions].
The autoequivalence $\sigma$ preserves each: apply its inverse to a test cone or cocone and use
the original universal property. For a diagram of fixed pairs and its underlying limit $L$, there
is a unique $\sigma L\to L$ whose composite with $p_i$ is $\theta_i\sigma(p_i)$; the analogous
construction with the inverse actions is its inverse, since equality is detected by the
projections. Its universal property lifts any equivariant cone, since the two candidate
composites become equal after every $p_i$. For a colimit $Q$, define $\sigma Q\to Q$ by its
values $\iota_i\theta_i$ on $\sigma\iota_i$; the same uniqueness proves invertibility and
equivariance of the universal map. This creates all small limits and colimits, including the
empty diagrams. For an invertible underlying intertwiner $f$, multiplying $f\theta=\theta'\sigma
f$ by inverses shows $f^{-1}$ intertwines. Thus forgetting is conservative. Both categories are
abelian by step 4 and [situation-conventions]; creation of kernels and cokernels
proves exactness.

6. For sheaves of sets the identical limit construction works by [lem-weil-pbc-site-sheaf-sets-
limits-sectionwise]. In particular forgetting preserves finite limits. Put $T=s^{-1}$ on set
sheaves and, for a sheaf $X$, give $QX=\prod_{n\in\mathbf Z}T^nX$ the shift action: after
$TQX\simeq\prod_nT^{n+1}X$, reindex by $n+1$. For $(N,\theta)$ let $\theta_n:T^nN\to N$ be its
iterated action. A map $f:N\to X$ extends to $N\to QX$ with component $T^n(f)\theta_n^{-1}$; the
action equation forces exactly these components, so restriction to component zero is its inverse.
Both assignments commute with composition. By [lem-weil-pbc-adjunction-of-natural-bijection],
forgetting is LEFT adjoint to $Q$. This supplies the geometric morphism $u$ of [def-weil-pbc-
ringed-topos-morphism], with the asserted direction. Applying forgetting to $R_{\rtimes}$ gives
$R$, and the structural map is this identity. Scalar extension along that identity changes no
module, so its module pullback is $U$.

7. Form $I(M)=\bigoplus_{n\in\mathbf Z}\sigma^nM$, which exists by [lem-weil-pbc-module-sheaves-
colimits-forgetful]. Since $\sigma$ preserves coproducts, the specified reindexing gives $\sigma
I(M)\simeq I(M)$, with the $n$th source summand sent identically to the $(n+1)$st target summand.
For $(N,\theta)$ write $\theta_n:\sigma^nN\to N$ for the integer iterates. A map $f:M\to UN$
extends to $I(M)\to N$ by the components $\theta_n\sigma^n f$. They intertwine because
$\theta_{n+1}=\theta\sigma\theta_n$. Conversely this equation forces every component of an
intertwiner from its component at zero, for positive and negative $n$. The two constructions are
inverse and natural. Hence [lem-weil-pbc-adjunction-of-natural-bijection] gives $I\dashv U$ with
the prescribed normalization. The formulas are additive, so $I$ is additive.

8. The category $\mathcal A$ has exact filtered colimits by [lem-pur-ringed-site-grothendieck-
abelian]. A coproduct of short exact sequences is the filtered colimit, over the finite subsets
of its index set, of their finite direct sums. Finite direct sums preserve kernels and cokernels
componentwise, so are exact; the cited exact filtered-colimit assertion makes the coproduct
sequence exact. Each $\sigma^n$ is exact since it and its inverse preserve kernels and cokernels
by their universal properties. Thus the underlying sequence of $I$ applied to a short exact
sequence is exact. Since step 5 creates kernels and cokernels, the sequence of fixed pairs is
exact too. This proves the required exactness of the LEFT adjoint, without asserting exactness of
the orbit product.

9. We need the following sheafification calculation for tensor. For an equivariant presheaf of
$R$-modules $P$, sheafify $P$ on $C$. Translation of coverings by $s$ and $s^{-1}$ preserves the
sheaf matching condition; equivalently, precomposition by either is an inverse equivalence on
both presheaves and sheaves. The universal property in [def-weil-presheaf-modules-
sheafification], applied after either precomposition, therefore identifies the sheafification of
a translated presheaf with the translated sheafification: maps to any sheaf are the same maps
before sheafification. Apply this to the action of $P$ to extend it to $P^\#$. Its action laws
and inverse laws follow from uniqueness, by checking after $P\to P^\#$. Maps $P^\#\to H$ are
equivariant exactly when their restrictions to $P$ are, again by uniqueness. With step 4 this is
precisely the universal property of sheafification on $D$. Consequently restriction identifies
the two module sheafifications and their unit maps.

10. By [def-pur-sheaf-tensor-product], the tensor on $D$ sheafifies the sectionwise tensor
presheaf. On degree-zero arrows this presheaf is $V\mapsto M(V)\otimes_{R(V)}N(V)$, and on
$a_{n,V}$ it sends $x\otimes y$ to $t^M_{n,V}(x)\otimes t^N_{n,V}(y)$. Step 9 therefore
identifies its sheafification with $M\otimes_R N$ and gives the diagonal action. Precomposition
by the site automorphism and its inverse in the same formula gives
$\sigma(M\otimes_RN)\simeq\sigma M\otimes_R\sigma N$. The rank-one module $R_{\rtimes}$ restricts
to $R$ with the original action, giving the stated unit.

11. Apply [lem-sf-integer-action-slice-equivalence] to $D=C\rtimes\mathbf Z$. Its restriction
equivalence of module categories on the slices is fully faithful. Thus [def-pur-sheaf-hom]
identifies the sections over $V$ of the internal Hom on $D$ with
$\operatorname{Hom}_{R|_V}(M|_V,N|_V)$, without imposing equivariance on a slice morphism. For a
degree-zero arrow $W\to V$, the two identifications commute with restriction: both send a family
of local module maps to the same family on $C/W$. Thus these sectionwise bijections form an
isomorphism of $R$-module sheaves, not only a bijection of global Hom sets.

12. To calculate the action on this sheaf Hom, restrict a slice map $\varphi$ along
$a_{1,V}:sV\to V$. The section identifications of step 11 use the action isomorphisms of the
source and target; hence the new slice map on $sV$ is $t_N\,\varphi\,t_M^{-1}$ (with the slices
translated by $s$). Expressed as a $\sigma$-structure this is
$\theta_N\circ\sigma(\varphi)\circ\theta_M^{-1}$. The canonical comparison $\sigma\mathcal
Hom_R(M,N)\simeq\mathcal Hom_R(\sigma M,\sigma N)$ comes from the inverse equivalences of
localized sites induced by $s$ and $s^{-1}$: each sends a local family of linear maps to that
same family on the translated slice, with inverse translation. This verifies the specified
contragredient action and naturality in both modules.

13. Tensor symmetry sends $x\otimes y$ to $y\otimes x$ on the tensor presheaves, so commutes with
the diagonal actions and with the sheafification identifications of step 9. Evaluation on each
slice sends $\varphi\otimes x$ to $\varphi(x)$; after translation its value is $(t_N\varphi
t_M^{-1})(t_Mx)=t_N(\varphi(x))$. It therefore intertwines actions. The comparison maps of steps
10 and 11 preserve exactly these pure tensors and local families of maps, so they take evaluation
to ordinary sheaf evaluation. Equality before sheafification implies equality after it by its
universal property. This proves all symmetry and evaluation compatibilities and completes the
underived assertion.
-/
theorem presentation [HasPullbacks C] : Nonempty (Presentation J s R a) := by
  obtain ⟨P⟩ := siteRestriction J s R a
  obtain ⟨M⟩ := addLimits J s R a P
  obtain ⟨I⟩ := addOrbit J s R a M
  obtain ⟨Q⟩ := closedComparisons J s R a I
  exact ⟨Q.val⟩

end CategoryTheory.TwistedActionRingedSite
