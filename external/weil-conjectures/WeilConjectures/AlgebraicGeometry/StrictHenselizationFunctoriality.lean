/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists

/-! # Strict henselization functoriality

Source: Stacks Project, Tags 04HX, 03PS, 04GU and 08HV
(blueprint: lem-weil-pbc-strict-henselization-functoriality).

Clause (1) is stated for every scheme and geometric point in
`strictHenselizationResidue`. The canonical map `j_Y` is the existing
`Scheme.strictLocalizationToBase`, and the canonical maps `c_V` are the legs of
`Scheme.strictHenselizationAffineCone` followed by `isoSpec.inv`,
over the chosen representatives of the affine pointed neighbourhoods. The functoriality theorem
takes the residue identifications of clause (1) as data tied by their characterizing equations.
The algebra structures on Ω are required to be exactly the geometric-point embeddings.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The strictly henselian ring, canonical base map, and unique pointed residue
identification of clause (1). The factorization condition forces the residue
identification to respect the base residue field; using ring equivalences therefore
also states uniqueness as an equivalence of base-residue-field algebras.
Source: Stacks Project, Tag 04HX and Definition 03PS
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
Proof steps for the node:
1. *Two elementary facts used throughout.* (a) If $X=\operatorname{Spec}B$ with $B$ local and
$\varphi:X\to Z$ is a morphism of schemes whose closed point maps into an open $Z'\subset Z$,
then $\varphi$ factors (uniquely, $Z'\to Z$ being a monomorphism) through $Z'$: every prime of
$B$ lies in the maximal ideal, so every point of $X$ generalizes the closed point, its image
generalizes a point of $Z'$, and open subsets are stable under generization. (b) For an affine
$U=\operatorname{Spec}A$, morphisms $\operatorname{Spec}B\to U$ are the same as ring maps $A\to
B$ [def-weil-affine-spectrum]; for a field $K$ a morphism
$\operatorname{Spec}K\to\operatorname{Spec}B$ is a ring map $B\to K$, whose kernel is the prime
that is the image point, and which factors as $B\to\kappa(\mathfrak q)\to K$ with
$\kappa(\mathfrak q)\to K$ the field map of [def-weil-geometric-point].

2. *$\kappa(\bar x)$ is separably closed (last part of (1)).* $\Omega$ is algebraically closed,
hence separably closed, so by [def-weil-pbc-relative-separable-closure] the separable algebraic
closure $\kappa(\bar x)$ of $\kappa(y)$ in $\Omega$ is separably closed
[def-pc-separably-closed] and separable algebraic over $\kappa(y)$: it is a separable closure of
$\kappa(y)$.

3. *$\mathcal O^{\mathrm{sh}}_{Y,\bar x}$ is strictly henselian, and its residue map (first part
of (1)).* Choose an affine open $U=\operatorname{Spec}A\subset Y$ containing $y$, with prime
$\mathfrak p$ of $y$. By [lem-weil-pbc-etale-local-ring-triples] the affine pointed etale
neighbourhoods of $\bar x$ over $U$ are initial, and $\mathcal O^{\mathrm{sh}}_{Y,\bar
x}=\varinjlim_{(B,\mathfrak q,\phi)}B$ over the triples with $A\to B$ etale, $\mathfrak q$ over
$\mathfrak p$, $\phi:\kappa(\mathfrak q)\to\kappa(\bar x)$ a $\kappa(\mathfrak p)$-map, the
triple of $(V=\operatorname{Spec}B,\bar v)$ being $(B,\mathfrak q_v,\phi_v)$ with $\phi_v$ the
field map of $\bar v$. Apply [lem-weil-pbc-strict-henselization-triples] with $R=A$,
$K=\kappa(\bar x)$ (a separable closure of $\kappa(\mathfrak p)=\kappa(y)$ by the previous
step): the colimit $C=\mathcal O^{\mathrm{sh}}_{Y,\bar x}$ is a strictly henselian local ring
[def-weil-pbc-henselian-terminology], the colimit $\psi:C\to\kappa(\bar x)$ of the maps
$B\to\kappa(\mathfrak q)\xrightarrow{\phi}\kappa(\bar x)$ is surjective with kernel the maximal
ideal $\mathfrak m_C$, so it induces an isomorphism of $\kappa(y)$-algebras
$\bar\psi:C/\mathfrak m_C\to\kappa(\bar x)$, and $\mathfrak m_C\cap A=\mathfrak p$.

4. *The factorization of the neighbourhoods and of $\bar x$ (rest of (1)).* Let
$\lambda:\operatorname{Spec}\Omega\to Y_{(\bar x)}$ be the morphism given by the ring map
$C\xrightarrow{\psi}\kappa(\bar x)\subset\Omega$, i.e.
$\operatorname{Spec}\Omega\to\operatorname{Spec}\kappa(\bar x)\to Y_{(\bar x)}$ with the second
map the closed point (the kernel of $\psi$ is $\mathfrak m_C$) and residue identification
$\bar\psi$. For $(V=\operatorname{Spec}B,\bar v)$ over $U$, $c_V\circ\lambda$ corresponds to
$B\to C\to\Omega$, which by construction of $\psi$ is $B\to\kappa(\mathfrak
q_v)\xrightarrow{\phi_v}\Omega$, the ring map of $\bar v$; so $c_V\circ\lambda=\bar v$. For an
arbitrary affine $(V,\bar v)$, choose by initiality a morphism $(V',\bar v')\to(V,\bar v)$ from
a neighbourhood over $U$; then $c_V=(V'\to V)\circ c_{V'}$ (canonical maps of the limit
[def-weil-pbc-strict-henselization-limit]) and $c_V\circ\lambda=(V'\to V)\circ\bar v'=\bar v$.
Taking $V=U$ (an open immersion is etale, so $(U,\bar x)$ is an affine pointed etale
neighbourhood) gives $j_Y\circ\lambda=\bar x$, hence $j_Y$ maps the closed point (the image of
$\lambda$) to $y$. Uniqueness of the residue isomorphism: if $\sigma:C/\mathfrak
m_C\to\kappa(\bar x)$ is a $\kappa(y)$-isomorphism with the stated factorizations, the morphism
$\lambda_\sigma:\operatorname{Spec}\Omega\to Y_{(\bar x)}$ it defines satisfies
$c_V\circ\lambda_\sigma=\bar v=c_V\circ\lambda$ for all $V$; since $C=\varinjlim A_V$, the two
ring maps $C\to\Omega$ agree on the image of every $A_V$, hence are equal, so $\sigma=\bar\psi$
(both are $C/\mathfrak m_C\to\Omega$ followed by the injective $\kappa(\bar x)\subset\Omega$).

5. *Clause (2).* The point $\bar s=g\circ\bar t$ corresponds [def-weil-geometric-point] to $s$
and the field map $\kappa(s)\to\Omega$ which is the residue map of $g\circ\bar t$ at the point
of $\operatorname{Spec}\Omega$; residue maps of a composite are the composites of the residue
maps (stalk maps of morphisms of locally ringed spaces compose
[def-weil-locally-ringed-space-morphism], and the residue maps are induced by them
[def-weil-residue-field]), so it is $\kappa(s)\to\kappa(t)\to\Omega$ with
$\kappa(s)\to\kappa(t)$ induced by $g$. Hence the image of $\kappa(s)$ in $\Omega$ lies in that
of $\kappa(t)$. An element of $\Omega$ that is a root of a separable polynomial with
coefficients in (the image of) $\kappa(s)$ is a root of the same separable polynomial regarded
over $\kappa(t)$; so $\kappa(\bar s)\subset\kappa(\bar t)$
[def-weil-pbc-relative-separable-closure], and this inclusion is a $\kappa(s)$-algebra map.

6. *Setting up clause (3).* Write $A^{\mathrm{sh}}=\mathcal O^{\mathrm{sh}}_{S,\bar s}$,
$B^{\mathrm{sh}}=\mathcal O^{\mathrm{sh}}_{T,\bar t}$, with maximal ideals $\mathfrak
m_A,\mathfrak m_B$ and the maps $\lambda_S:\operatorname{Spec}\Omega\to S_{(\bar s)}$,
$\lambda_T:\operatorname{Spec}\Omega\to T_{(\bar t)}$ of the factorizations in (1). Choose an
affine open $U_S=\operatorname{Spec}A\subset S$ containing $s$, with prime $\mathfrak p$ of $s$.
By (1) $g\circ j_T$ maps the closed point of $T_{(\bar t)}$ to $g(t)=s\in U_S$, so by step 1(a)
it factors through $U_S$ and is given (step 1(b)) by a ring map $\alpha:A\to B^{\mathrm{sh}}$;
this makes $B^{\mathrm{sh}}$ an $A$-algebra. Likewise $j_S$ factors through $U_S$ as $c_{U_S}$,
given by the colimit map $A\to A^{\mathrm{sh}}$. The composite
$A\xrightarrow{\alpha}B^{\mathrm{sh}}\to B^{\mathrm{sh}}/\mathfrak m_B\cong\kappa(\bar
t)\subset\Omega$ is the ring map of $g\circ j_T\circ\lambda_T=g\circ\bar t=\bar s$ on $U_S$,
whose kernel is $\mathfrak p$ (step 1(b)); so $\alpha^{-1}(\mathfrak m_B)=\mathfrak p$, and the
induced $\kappa(\mathfrak p)=\kappa(s)\to\kappa(\bar t)$ is the embedding of $\kappa(s)$ by
$\bar s$. By steps 3 and 4 and [lem-weil-pbc-etale-local-ring-triples], $A^{\mathrm{sh}}$ is a
filtered colimit of etale $A$-algebras, with maximal ideal $\mathfrak m_A$ lying over $\mathfrak
p$; and $B^{\mathrm{sh}}$ is strictly henselian, in particular henselian
[def-weil-pbc-henselian-terminology]. Under the identifications of (1), the inclusion
$\tau:\kappa(\bar s)\subset\kappa(\bar t)$ of (2) is a homomorphism of $\kappa(\mathfrak
p)$-algebras $A^{\mathrm{sh}}/\mathfrak m_A\to B^{\mathrm{sh}}/\mathfrak m_B$.

7. *Clause (3), existence.* By [lem-weil-pbc-map-into-henselian-colimit] (applied to
$A\xrightarrow{\alpha}B^{\mathrm{sh}}$, the $A$-algebra $A^{\mathrm{sh}}$, its prime $\mathfrak
m_A$ over $\mathfrak p=\alpha^{-1}(\mathfrak m_B)$, and $\tau$) there is an $A$-algebra map
$h:A^{\mathrm{sh}}\to B^{\mathrm{sh}}$ with $h^{-1}(\mathfrak m_B)=\mathfrak m_A$, i.e. $h$ is
local [def-weil-locally-ringed-space-morphism], inducing $\tau$ on residue fields. Since $h$ is
an $A$-algebra map, $c_{U_S}\circ\operatorname{Spec}h$ and the factorization of $g\circ j_T$
through $U_S$ are given by the same ring map $\alpha:A\to B^{\mathrm{sh}}$ (step 1(b)), hence
equal; composing with $U_S\subset S$ gives $j_S\circ\operatorname{Spec}h=g\circ j_T$.

8. *Clause (3), uniqueness.* Let $h':A^{\mathrm{sh}}\to B^{\mathrm{sh}}$ be local with
$j_S\circ\operatorname{Spec}h'=g\circ j_T$ inducing $\tau$. The morphism
$c_{U_S}\circ\operatorname{Spec}h'$ composed with $U_S\subset S$ is $g\circ j_T$; as $U_S\to S$
is a monomorphism, $c_{U_S}\circ\operatorname{Spec}h'$ is the factorization of $g\circ j_T$
through $U_S$, so $A\to A^{\mathrm{sh}}\xrightarrow{h'}B^{\mathrm{sh}}$ is $\alpha$ (step 1(b)):
$h'$ is an $A$-algebra map. Being local, $h'^{-1}(\mathfrak m_B)=\mathfrak m_A$, and it induces
$\tau$. By the uniqueness in [lem-weil-pbc-map-into-henselian-colimit], $h'=h$.

9. *Clause (4).* Let $v,w$ be the images of $\bar v,\bar w$; $w(w)=v$ as $w\circ\bar w=\bar v$.
The point $v$ lies over $s\in U_S$, so choose an affine open $V''=\operatorname{Spec}D\subset V$
containing $v$ and mapping into $U_S$; $V''\to U_S$ is etale (an open immersion followed by the
etale $V\to S$ [def-weil-etale-morphism]), so $A\to D$ is an etale $A$-algebra. Both morphisms
$\varphi_1=w\circ c_W$ and $\varphi_2=c_V\circ\operatorname{Spec}h$ map the closed point of
$T_{(\bar t)}$ to $v$: by (1) $c_W$ maps it to $w$, and $\operatorname{Spec}h$ ($h$ local) maps
it to the closed point of $S_{(\bar s)}$, which $c_V$ maps to $v$. By step 1(a) both factor
through $V''$, given by ring maps $f_1,f_2:D\to B^{\mathrm{sh}}$. (i) Both are $A$-algebra maps
for $\alpha$: composed with $V\to S$, $\varphi_1$ is $(V\to S)\circ w\circ c_W=g\circ(W\to
T)\circ c_W=g\circ j_T$, and $\varphi_2$ is $j_S\circ\operatorname{Spec}h=g\circ j_T$ by (3);
both land in $U_S$, so step 1(b) gives $f_1|_A=f_2|_A=\alpha$. (ii) Both composites
$D\xrightarrow{f_i}B^{\mathrm{sh}}\to\kappa(\bar t)\subset\Omega$ equal the ring map of $\bar v$
(which factors through $V''$): for $f_1$, $\varphi_1\circ\lambda_T=w\circ
c_W\circ\lambda_T=w\circ\bar w=\bar v$ by (1) for $T$; for $f_2$, since $h$ induces $\tau$ on
residue fields, $\operatorname{Spec}h\circ\lambda_T=\lambda_S$, so
$\varphi_2\circ\lambda_T=c_V\circ\lambda_S=\bar v$ by (1) for $S$. Hence $f_1^{-1}(\mathfrak
m_B)=f_2^{-1}(\mathfrak m_B)$ is the prime $\mathfrak q_v$ of $v$ (the kernel of the ring map of
$\bar v$) and $f_1,f_2$ induce the same map $\kappa(\mathfrak q_v)\to B^{\mathrm{sh}}/\mathfrak
m_B$ (both followed by the injective $B^{\mathrm{sh}}/\mathfrak m_B\cong\kappa(\bar
t)\subset\Omega$ give the field map of $\bar v$). The uniqueness in
[lem-weil-pbc-map-into-henselian-colimit] for the single etale $A$-algebra $D$ and the henselian
$B^{\mathrm{sh}}$ gives $f_1=f_2$, so $\varphi_1=\varphi_2$.
-/
theorem strictHenselizationResidue
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y)
    [Algebra (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω]
    (hΩ : algebraMap (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barY)).hom) :
    ∃ (_ : IsLocalRing (Scheme.strictHenselization barY)),
      IsStrictlyHenselianLocalRing (Scheme.strictHenselization barY) ∧
      Scheme.strictLocalizationToBase barY
          (IsLocalRing.closedPoint (Scheme.strictHenselization barY)) =
        barY (IsLocalRing.closedPoint Ω) ∧
      IsSepClosed (separableClosure
        (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω) ∧
      ∃! σ : IsLocalRing.ResidueField (Scheme.strictHenselization barY) ≃+*
          separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω,
        (∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
          Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σ.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barY)))) ≫
            (Scheme.strictHenselizationAffineCone barY).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
            ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left) ∧
        Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σ.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barY)))) ≫
          Scheme.strictLocalizationToBase barY = barY := by
  have hlocal : IsLocalRing (Scheme.strictHenselization barY) := inferInstance
  have hstrict : IsStrictlyHenselianLocalRing (Scheme.strictHenselization barY) :=
    ⟨inferInstance⟩
  let := hlocal
  obtain ⟨ψ, hsurj, hker, hpoint⟩ := strictHenselizationPointedMap barY hΩ
  let σ : IsLocalRing.ResidueField (Scheme.strictHenselization barY) ≃+*
      separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
    (Ideal.quotEquivOfEq hker.symm).trans (ψ.quotientKerEquivOfSurjective hsurj)
  have hσ : σ.toRingHom.comp
      (IsLocalRing.residue (Scheme.strictHenselization barY)) = ψ := by
    ext x
    rfl
  have hpointσ : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY),
      Spec.map (CommRingCat.ofHom
        (((IntermediateField.val
          (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σ.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barY)))) ≫
        (Scheme.strictHenselizationAffineCone barY).π.app (Opposite.op (Opposite.op j)) ≫
        (Spec (Opposite.unop ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.left := by
    simpa only [RingHom.comp_assoc, hσ] using hpoint
  let pointLift := Spec.map (CommRingCat.ofHom
    (((IntermediateField.val
      (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
        σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY))))
  have hbase : pointLift ≫ Scheme.strictLocalizationToBase barY = barY := by
    have hn := (Scheme.strictHenselizationAffineProperties barY).2.1
    let := hn
    let j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barY) :=
      Classical.choice IsCofiltered.nonempty
    have hj := Scheme.strictHenselizationStructuralMap_eq barY j
    have hp := hpointσ j
    have hw := ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).2.w
    change pointLift ≫ Scheme.strictLocalizationToBase barY = barY
    rw [← hj]
    simpa only [pointLift, Scheme.isoSpec_Spec_inv, Category.assoc] using!
      (congrArg (fun f ↦ f ≫ ((Scheme.AffineEtale.Spec Y).obj
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj j).1).hom) hp).trans hw
  have hclosed : pointLift (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (Scheme.strictHenselization barY) := by
    change PrimeSpectrum.comap
      ((((IntermediateField.val
        (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom).comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY)))
      (IsLocalRing.closedPoint Ω) = _
    rw [PrimeSpectrum.comap_comp]
    exact IsLocalRing.PrimeSpectrum.comap_residue _ _
  refine ⟨hlocal, hstrict, ?_, IsSepClosure.sep_closed
    (Y.residueField (barY (IsLocalRing.closedPoint Ω))), σ, ⟨hpointσ, hbase⟩, ?_⟩
  · simpa only [Scheme.Hom.comp_apply, hclosed] using!
      congrArg (fun f ↦ f (IsLocalRing.closedPoint Ω)) hbase
  · intro σ' hσ'
    let f := CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY)))
    let f' := CommRingCat.ofHom
      (((IntermediateField.val
        (separableClosure (Y.residueField (barY (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
          σ'.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barY)))
    have hmaps : Spec.map f' = Spec.map f := by
      obtain ⟨hl⟩ := (Scheme.strictHenselizationAffineProperties barY).2.2
      apply hl.hom_ext
      intro j
      apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barY)).inverse.obj
          j.unop.unop).1.left)).isoSpec.inv).1
      exact (hσ'.1 j.unop.unop).trans (hpointσ j.unop.unop).symm
    have hrings := congrArg CommRingCat.Hom.hom (Spec.map_injective hmaps)
    ext x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective (R := Scheme.strictHenselization barY) x
    exact congrArg (fun q ↦ q r) hrings

/-- Clauses (2)--(4), for the canonical maps and residue identifications of clause (1).
Residue compatibility is expressed after the injective embeddings in Ω: the equality
of the two ring maps to Ω is equivalent to the induced residue map being the inclusion
of the relative separable closures. Uniqueness is asserted with only the locality,
base diagram and residue conditions; neighbourhood compatibility is a separate clause.
Source: Stacks Project, paragraph following Tag 03PS, Tags 04GU, 08HV,
and the proof of Tag 095T
(blueprint: lem-weil-pbc-strict-henselization-functoriality).
Proof steps for the node:
1. *Two elementary facts used throughout.* (a) If $X=\operatorname{Spec}B$ with $B$ local and
$\varphi:X\to Z$ is a morphism of schemes whose closed point maps into an open $Z'\subset Z$,
then $\varphi$ factors (uniquely, $Z'\to Z$ being a monomorphism) through $Z'$: every prime of
$B$ lies in the maximal ideal, so every point of $X$ generalizes the closed point, its image
generalizes a point of $Z'$, and open subsets are stable under generization. (b) For an affine
$U=\operatorname{Spec}A$, morphisms $\operatorname{Spec}B\to U$ are the same as ring maps $A\to
B$ [def-weil-affine-spectrum]; for a field $K$ a morphism
$\operatorname{Spec}K\to\operatorname{Spec}B$ is a ring map $B\to K$, whose kernel is the prime
that is the image point, and which factors as $B\to\kappa(\mathfrak q)\to K$ with
$\kappa(\mathfrak q)\to K$ the field map of [def-weil-geometric-point].

2. *$\kappa(\bar x)$ is separably closed (last part of (1)).* $\Omega$ is algebraically closed,
hence separably closed, so by [def-weil-pbc-relative-separable-closure] the separable algebraic
closure $\kappa(\bar x)$ of $\kappa(y)$ in $\Omega$ is separably closed
[def-pc-separably-closed] and separable algebraic over $\kappa(y)$: it is a separable closure of
$\kappa(y)$.

3. *$\mathcal O^{\mathrm{sh}}_{Y,\bar x}$ is strictly henselian, and its residue map (first part
of (1)).* Choose an affine open $U=\operatorname{Spec}A\subset Y$ containing $y$, with prime
$\mathfrak p$ of $y$. By [lem-weil-pbc-etale-local-ring-triples] the affine pointed etale
neighbourhoods of $\bar x$ over $U$ are initial, and $\mathcal O^{\mathrm{sh}}_{Y,\bar
x}=\varinjlim_{(B,\mathfrak q,\phi)}B$ over the triples with $A\to B$ etale, $\mathfrak q$ over
$\mathfrak p$, $\phi:\kappa(\mathfrak q)\to\kappa(\bar x)$ a $\kappa(\mathfrak p)$-map, the
triple of $(V=\operatorname{Spec}B,\bar v)$ being $(B,\mathfrak q_v,\phi_v)$ with $\phi_v$ the
field map of $\bar v$. Apply [lem-weil-pbc-strict-henselization-triples] with $R=A$,
$K=\kappa(\bar x)$ (a separable closure of $\kappa(\mathfrak p)=\kappa(y)$ by the previous
step): the colimit $C=\mathcal O^{\mathrm{sh}}_{Y,\bar x}$ is a strictly henselian local ring
[def-weil-pbc-henselian-terminology], the colimit $\psi:C\to\kappa(\bar x)$ of the maps
$B\to\kappa(\mathfrak q)\xrightarrow{\phi}\kappa(\bar x)$ is surjective with kernel the maximal
ideal $\mathfrak m_C$, so it induces an isomorphism of $\kappa(y)$-algebras
$\bar\psi:C/\mathfrak m_C\to\kappa(\bar x)$, and $\mathfrak m_C\cap A=\mathfrak p$.

4. *The factorization of the neighbourhoods and of $\bar x$ (rest of (1)).* Let
$\lambda:\operatorname{Spec}\Omega\to Y_{(\bar x)}$ be the morphism given by the ring map
$C\xrightarrow{\psi}\kappa(\bar x)\subset\Omega$, i.e.
$\operatorname{Spec}\Omega\to\operatorname{Spec}\kappa(\bar x)\to Y_{(\bar x)}$ with the second
map the closed point (the kernel of $\psi$ is $\mathfrak m_C$) and residue identification
$\bar\psi$. For $(V=\operatorname{Spec}B,\bar v)$ over $U$, $c_V\circ\lambda$ corresponds to
$B\to C\to\Omega$, which by construction of $\psi$ is $B\to\kappa(\mathfrak
q_v)\xrightarrow{\phi_v}\Omega$, the ring map of $\bar v$; so $c_V\circ\lambda=\bar v$. For an
arbitrary affine $(V,\bar v)$, choose by initiality a morphism $(V',\bar v')\to(V,\bar v)$ from
a neighbourhood over $U$; then $c_V=(V'\to V)\circ c_{V'}$ (canonical maps of the limit
[def-weil-pbc-strict-henselization-limit]) and $c_V\circ\lambda=(V'\to V)\circ\bar v'=\bar v$.
Taking $V=U$ (an open immersion is etale, so $(U,\bar x)$ is an affine pointed etale
neighbourhood) gives $j_Y\circ\lambda=\bar x$, hence $j_Y$ maps the closed point (the image of
$\lambda$) to $y$. Uniqueness of the residue isomorphism: if $\sigma:C/\mathfrak
m_C\to\kappa(\bar x)$ is a $\kappa(y)$-isomorphism with the stated factorizations, the morphism
$\lambda_\sigma:\operatorname{Spec}\Omega\to Y_{(\bar x)}$ it defines satisfies
$c_V\circ\lambda_\sigma=\bar v=c_V\circ\lambda$ for all $V$; since $C=\varinjlim A_V$, the two
ring maps $C\to\Omega$ agree on the image of every $A_V$, hence are equal, so $\sigma=\bar\psi$
(both are $C/\mathfrak m_C\to\Omega$ followed by the injective $\kappa(\bar x)\subset\Omega$).

5. *Clause (2).* The point $\bar s=g\circ\bar t$ corresponds [def-weil-geometric-point] to $s$
and the field map $\kappa(s)\to\Omega$ which is the residue map of $g\circ\bar t$ at the point
of $\operatorname{Spec}\Omega$; residue maps of a composite are the composites of the residue
maps (stalk maps of morphisms of locally ringed spaces compose
[def-weil-locally-ringed-space-morphism], and the residue maps are induced by them
[def-weil-residue-field]), so it is $\kappa(s)\to\kappa(t)\to\Omega$ with
$\kappa(s)\to\kappa(t)$ induced by $g$. Hence the image of $\kappa(s)$ in $\Omega$ lies in that
of $\kappa(t)$. An element of $\Omega$ that is a root of a separable polynomial with
coefficients in (the image of) $\kappa(s)$ is a root of the same separable polynomial regarded
over $\kappa(t)$; so $\kappa(\bar s)\subset\kappa(\bar t)$
[def-weil-pbc-relative-separable-closure], and this inclusion is a $\kappa(s)$-algebra map.

6. *Setting up clause (3).* Write $A^{\mathrm{sh}}=\mathcal O^{\mathrm{sh}}_{S,\bar s}$,
$B^{\mathrm{sh}}=\mathcal O^{\mathrm{sh}}_{T,\bar t}$, with maximal ideals $\mathfrak
m_A,\mathfrak m_B$ and the maps $\lambda_S:\operatorname{Spec}\Omega\to S_{(\bar s)}$,
$\lambda_T:\operatorname{Spec}\Omega\to T_{(\bar t)}$ of the factorizations in (1). Choose an
affine open $U_S=\operatorname{Spec}A\subset S$ containing $s$, with prime $\mathfrak p$ of $s$.
By (1) $g\circ j_T$ maps the closed point of $T_{(\bar t)}$ to $g(t)=s\in U_S$, so by step 1(a)
it factors through $U_S$ and is given (step 1(b)) by a ring map $\alpha:A\to B^{\mathrm{sh}}$;
this makes $B^{\mathrm{sh}}$ an $A$-algebra. Likewise $j_S$ factors through $U_S$ as $c_{U_S}$,
given by the colimit map $A\to A^{\mathrm{sh}}$. The composite
$A\xrightarrow{\alpha}B^{\mathrm{sh}}\to B^{\mathrm{sh}}/\mathfrak m_B\cong\kappa(\bar
t)\subset\Omega$ is the ring map of $g\circ j_T\circ\lambda_T=g\circ\bar t=\bar s$ on $U_S$,
whose kernel is $\mathfrak p$ (step 1(b)); so $\alpha^{-1}(\mathfrak m_B)=\mathfrak p$, and the
induced $\kappa(\mathfrak p)=\kappa(s)\to\kappa(\bar t)$ is the embedding of $\kappa(s)$ by
$\bar s$. By steps 3 and 4 and [lem-weil-pbc-etale-local-ring-triples], $A^{\mathrm{sh}}$ is a
filtered colimit of etale $A$-algebras, with maximal ideal $\mathfrak m_A$ lying over $\mathfrak
p$; and $B^{\mathrm{sh}}$ is strictly henselian, in particular henselian
[def-weil-pbc-henselian-terminology]. Under the identifications of (1), the inclusion
$\tau:\kappa(\bar s)\subset\kappa(\bar t)$ of (2) is a homomorphism of $\kappa(\mathfrak
p)$-algebras $A^{\mathrm{sh}}/\mathfrak m_A\to B^{\mathrm{sh}}/\mathfrak m_B$.

7. *Clause (3), existence.* By [lem-weil-pbc-map-into-henselian-colimit] (applied to
$A\xrightarrow{\alpha}B^{\mathrm{sh}}$, the $A$-algebra $A^{\mathrm{sh}}$, its prime $\mathfrak
m_A$ over $\mathfrak p=\alpha^{-1}(\mathfrak m_B)$, and $\tau$) there is an $A$-algebra map
$h:A^{\mathrm{sh}}\to B^{\mathrm{sh}}$ with $h^{-1}(\mathfrak m_B)=\mathfrak m_A$, i.e. $h$ is
local [def-weil-locally-ringed-space-morphism], inducing $\tau$ on residue fields. Since $h$ is
an $A$-algebra map, $c_{U_S}\circ\operatorname{Spec}h$ and the factorization of $g\circ j_T$
through $U_S$ are given by the same ring map $\alpha:A\to B^{\mathrm{sh}}$ (step 1(b)), hence
equal; composing with $U_S\subset S$ gives $j_S\circ\operatorname{Spec}h=g\circ j_T$.

8. *Clause (3), uniqueness.* Let $h':A^{\mathrm{sh}}\to B^{\mathrm{sh}}$ be local with
$j_S\circ\operatorname{Spec}h'=g\circ j_T$ inducing $\tau$. The morphism
$c_{U_S}\circ\operatorname{Spec}h'$ composed with $U_S\subset S$ is $g\circ j_T$; as $U_S\to S$
is a monomorphism, $c_{U_S}\circ\operatorname{Spec}h'$ is the factorization of $g\circ j_T$
through $U_S$, so $A\to A^{\mathrm{sh}}\xrightarrow{h'}B^{\mathrm{sh}}$ is $\alpha$ (step 1(b)):
$h'$ is an $A$-algebra map. Being local, $h'^{-1}(\mathfrak m_B)=\mathfrak m_A$, and it induces
$\tau$. By the uniqueness in [lem-weil-pbc-map-into-henselian-colimit], $h'=h$.

9. *Clause (4).* Let $v,w$ be the images of $\bar v,\bar w$; $w(w)=v$ as $w\circ\bar w=\bar v$.
The point $v$ lies over $s\in U_S$, so choose an affine open $V''=\operatorname{Spec}D\subset V$
containing $v$ and mapping into $U_S$; $V''\to U_S$ is etale (an open immersion followed by the
etale $V\to S$ [def-weil-etale-morphism]), so $A\to D$ is an etale $A$-algebra. Both morphisms
$\varphi_1=w\circ c_W$ and $\varphi_2=c_V\circ\operatorname{Spec}h$ map the closed point of
$T_{(\bar t)}$ to $v$: by (1) $c_W$ maps it to $w$, and $\operatorname{Spec}h$ ($h$ local) maps
it to the closed point of $S_{(\bar s)}$, which $c_V$ maps to $v$. By step 1(a) both factor
through $V''$, given by ring maps $f_1,f_2:D\to B^{\mathrm{sh}}$. (i) Both are $A$-algebra maps
for $\alpha$: composed with $V\to S$, $\varphi_1$ is $(V\to S)\circ w\circ c_W=g\circ(W\to
T)\circ c_W=g\circ j_T$, and $\varphi_2$ is $j_S\circ\operatorname{Spec}h=g\circ j_T$ by (3);
both land in $U_S$, so step 1(b) gives $f_1|_A=f_2|_A=\alpha$. (ii) Both composites
$D\xrightarrow{f_i}B^{\mathrm{sh}}\to\kappa(\bar t)\subset\Omega$ equal the ring map of $\bar v$
(which factors through $V''$): for $f_1$, $\varphi_1\circ\lambda_T=w\circ
c_W\circ\lambda_T=w\circ\bar w=\bar v$ by (1) for $T$; for $f_2$, since $h$ induces $\tau$ on
residue fields, $\operatorname{Spec}h\circ\lambda_T=\lambda_S$, so
$\varphi_2\circ\lambda_T=c_V\circ\lambda_S=\bar v$ by (1) for $S$. Hence $f_1^{-1}(\mathfrak
m_B)=f_2^{-1}(\mathfrak m_B)$ is the prime $\mathfrak q_v$ of $v$ (the kernel of the ring map of
$\bar v$) and $f_1,f_2$ induce the same map $\kappa(\mathfrak q_v)\to B^{\mathrm{sh}}/\mathfrak
m_B$ (both followed by the injective $B^{\mathrm{sh}}/\mathfrak m_B\cong\kappa(\bar
t)\subset\Omega$ give the field map of $\bar v$). The uniqueness in
[lem-weil-pbc-map-into-henselian-colimit] for the single etale $A$-algebra $D$ and the henselian
$B^{\mathrm{sh}}$ gives $f_1=f_2$, so $\varphi_1=\varphi_2$.
-/
theorem strictHenselizationFunctoriality
    {S T : Scheme.{v}} (g : T ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barT : Spec (.of Ω) ⟶ T) (barS : Spec (.of Ω) ⟶ S)
    (hbar : barS = barT ≫ g)
    [Algebra (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω]
    [Algebra (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω]
    (hΩS : algebraMap (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barS)).hom)
    (hΩT : algebraMap (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo barT)).hom)
    [IsLocalRing (Scheme.strictHenselization barS)]
    [IsLocalRing (Scheme.strictHenselization barT)]
    (σS : IsLocalRing.ResidueField (Scheme.strictHenselization barS) ≃+*
      separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)
    (σT : IsLocalRing.ResidueField (Scheme.strictHenselization barT) ≃+*
      separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)
    (hσS : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σS.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barS)))) ≫
          (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj j).2.left)
    (hσT : ∀ j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT),
      Spec.map (CommRingCat.ofHom
          (((IntermediateField.val
            (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
              σT.toRingHom).comp
            (IsLocalRing.residue (Scheme.strictHenselization barT)))) ≫
          (Scheme.strictHenselizationAffineCone barT).π.app (Opposite.op (Opposite.op j)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).1.left)).isoSpec.inv =
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj j).2.left) :
    (∀ x : Ω,
      x ∈ separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω →
      x ∈ separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω) ∧
    ∃ h : Scheme.strictHenselization barS ⟶ Scheme.strictHenselization barT,
      IsLocalHom h.hom ∧
      Spec.map h ≫ Scheme.strictLocalizationToBase barS =
        Scheme.strictLocalizationToBase barT ≫ g ∧
      (((IntermediateField.val
          (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σS.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barS))) =
        ((((IntermediateField.val
          (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σT.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barT)))).comp h.hom ∧
      (∀ h' : Scheme.strictHenselization barS ⟶ Scheme.strictHenselization barT,
        IsLocalHom h'.hom →
        Spec.map h' ≫ Scheme.strictLocalizationToBase barS =
          Scheme.strictLocalizationToBase barT ≫ g →
        (((IntermediateField.val
          (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σS.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barS))) =
          ((((IntermediateField.val
          (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
            σT.toRingHom).comp
          (IsLocalRing.residue (Scheme.strictHenselization barT)))).comp h'.hom →
        h' = h) ∧
      (∀ (a : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS)) (b : SmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barT))
         (w : ((Scheme.AffineEtale.Spec T).obj ((equivSmallModel.{v}
           (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1).left ⟶
           ((Scheme.AffineEtale.Spec S).obj ((equivSmallModel.{v}
             (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1).left),
        w ≫ ((Scheme.AffineEtale.Spec S).obj ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1).hom =
          ((Scheme.AffineEtale.Spec T).obj ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1).hom ≫ g →
        ((equivSmallModel.{v}
          (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).2.left ≫ w =
          ((equivSmallModel.{v}
            (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).2.left →
        ((Scheme.strictHenselizationAffineCone barT).π.app (Opposite.op (Opposite.op b)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1.left)).isoSpec.inv)
            ≫ w =
          Spec.map h ≫
            (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op a)) ≫
            (Spec (Opposite.unop ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1.left)).isoSpec.inv)
    := by
  obtain ⟨h, hhlocal, hhbase, hhres⟩ :=
    strictHenselizationMapExists g barT barS hbar hΩS hΩT σS σT hσS hσT
  let ψS := (((IntermediateField.val
    (separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σS.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barS)))
  let ψT := (((IntermediateField.val
    (separableClosure (T.residueField (barT (IsLocalRing.closedPoint Ω))) Ω)).toRingHom.comp
      σT.toRingHom).comp (IsLocalRing.residue (Scheme.strictHenselization barT)))
  have hres : ψS = ψT.comp h.hom := hhres
  have hspec : Spec.map (CommRingCat.ofHom ψT) ≫ Spec.map h =
      Spec.map (CommRingCat.ofHom ψS) := by
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hres.symm
  let cS := fun a : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS) ↦
    (Scheme.strictHenselizationAffineCone barS).π.app (Opposite.op (Opposite.op a)) ≫
      (Spec (Opposite.unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1.left)).isoSpec.inv
  let cT := fun b : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT) ↦
    (Scheme.strictHenselizationAffineCone barT).π.app (Opposite.op (Opposite.op b)) ≫
      (Spec (Opposite.unop ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1.left)).isoSpec.inv
  let pS := fun a : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barS) ↦
    ((Scheme.AffineEtale.Spec S).obj ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).1).hom
  let pT := fun b : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods barT) ↦
    ((Scheme.AffineEtale.Spec T).obj ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).1).hom
  have hcS : ∀ a, cS a ≫ pS a = Scheme.strictLocalizationToBase barS := by
    intro a
    simpa only [cS, pS, Scheme.isoSpec_Spec_inv] using!
      Scheme.strictHenselizationStructuralMap_eq barS a
  have hcT : ∀ b, cT b ≫ pT b = Scheme.strictLocalizationToBase barT := by
    intro b
    simpa only [cT, pT, Scheme.isoSpec_Spec_inv] using!
      Scheme.strictHenselizationStructuralMap_eq barT b
  have hψS : ∀ a, Spec.map (CommRingCat.ofHom ψS) ≫ cS a =
      ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).2.left := hσS
  have hψT : ∀ b, Spec.map (CommRingCat.ofHom ψT) ≫ cT b =
      ((equivSmallModel.{v}
        (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).2.left := hσT
  have hlocalψT : IsLocalHom ψT := inferInstance
  let := hlocalψT
  refine ⟨?_, h, hhlocal, hhbase, hhres, ?_, ?_⟩
  · intro x hx
    let z : separableClosure (S.residueField (barS (IsLocalRing.closedPoint Ω))) Ω := ⟨x, hx⟩
    obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective
      (R := Scheme.strictHenselization barS) (σS.symm z)
    have heq : ψS r = x := by
      change (σS (IsLocalRing.residue _ r)).val = x
      rw [hr]
      exact congrArg Subtype.val (σS.apply_symm_apply z)
    have heqT : ψT (h.hom r) = x :=
      (congrArg (fun q ↦ q r) hres).symm.trans heq
    exact heqT ▸ (σT (IsLocalRing.residue _ (h.hom r))).property
  · intro h' _ hh'base hh'res
    have hspec' : Spec.map (CommRingCat.ofHom ψT) ≫ Spec.map h' =
        Spec.map (CommRingCat.ofHom ψS) := by
      rw [← Spec.map_comp]
      congr 1
      exact CommRingCat.hom_ext hh'res.symm
    apply Spec.map_injective
    obtain ⟨hl⟩ := (Scheme.strictHenselizationAffineProperties barS).2.2
    apply hl.hom_ext
    intro j
    apply (cancel_mono (Spec (Opposite.unop ((equivSmallModel.{v}
      (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj
        j.unop.unop).1.left)).isoSpec.inv).1
    change Spec.map h' ≫ cS j.unop.unop = Spec.map h ≫ cS j.unop.unop
    apply etalePointedMapRigidity ψT (pS j.unop.unop)
    · simpa only [Category.assoc, hcS] using hh'base.trans hhbase.symm
    · simpa only [Category.assoc] using!
        (congrArg (fun q ↦ q ≫ cS j.unop.unop) hspec').trans
          (congrArg (fun q ↦ q ≫ cS j.unop.unop) hspec).symm
  · intro a b w hw hp
    change cT b ≫ w = Spec.map h ≫ cS a
    apply etalePointedMapRigidity ψT (pS a)
    · calc
        (cT b ≫ w) ≫ pS a = (cT b ≫ pT b) ≫ g := by
          simpa only [Category.assoc] using congrArg (fun q ↦ cT b ≫ q) hw
        _ = Scheme.strictLocalizationToBase barT ≫ g := by rw [hcT]
        _ = Spec.map h ≫ Scheme.strictLocalizationToBase barS := hhbase.symm
        _ = (Spec.map h ≫ cS a) ≫ pS a := by rw [Category.assoc, hcS]
    · calc
        Spec.map (CommRingCat.ofHom ψT) ≫ cT b ≫ w =
            ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barT)).inverse.obj b).2.left ≫ w := by
          rw [← Category.assoc, hψT]
        _ = ((equivSmallModel.{v}
              (Scheme.strictHenselizationNeighbourhoods barS)).inverse.obj a).2.left := hp
        _ = Spec.map (CommRingCat.ofHom ψS) ≫ cS a := (hψS a).symm
        _ = Spec.map (CommRingCat.ofHom ψT) ≫ Spec.map h ≫ cS a := by
          simpa only [Category.assoc] using!
            (congrArg (fun q ↦ q ≫ cS a) hspec).symm

end AlgebraicGeometry
