/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Etale locality of the ordinary ambient adjoint

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md
(blueprint: lemma-affine-space-etale-localization--4).

Sheaf-level exactness is the existing `preservesFiniteLimits_etaleLowerShriek`, together
with preservation of colimits by its existing left-adjoint structure. The first declaration
below descends the existing sheaf adjunction, without any boundedness restriction. The second
states locality for arbitrary right adjoints of the ordinary compact-support candidates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private noncomputable abbrev openLocalization {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] : U.Etale ⥤ X.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : Etale j)

private lemma openLocalization_terminal {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (V : X.Etaleᵒᵖ)
    (t : CostructuredArrow (openLocalization j).op V) [IsIso t.hom] :
    Nonempty (IsTerminal t) := by
  have : (openLocalization j).Full :=
    MorphismProperty.Over.full_map (P := @Etale) (Q := ⊤) (f := j) _
  have : (openLocalization j).Faithful :=
    MorphismProperty.Over.faithful_map (P := @Etale) (Q := ⊤) (f := j) _
  have hL : (openLocalization j).op.FullyFaithful :=
    (Functor.FullyFaithful.ofFullyFaithful (openLocalization j)).op
  refine ⟨IsTerminal.ofUniqueHom (fun s ↦ CostructuredArrow.homMk
    (hL.preimage (s.hom ≫ inv t.hom)) (by
      erw [hL.map_preimage]
      simp)) (fun s m ↦ ?_)⟩
  ext
  refine congrArg Quiver.Hom.unop (hL.map_injective ?_)
  erw [hL.map_preimage]
  simp [← CostructuredArrow.w m]

private lemma openLocalization_iso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (V : X.Etaleᵒᵖ)
    (s : CostructuredArrow (openLocalization j).op V) :
    ∃ t : CostructuredArrow (openLocalization j).op V, IsIso t.hom := by
  let W : U.Etale := s.left.unop
  let g : V.unop.left ⟶ W.left := s.hom.unop.left
  have hg : g ≫ W.hom ≫ j = V.unop.hom := by
    simpa [g] using MorphismProperty.Over.w s.hom.unop
  have : Etale ((g ≫ W.hom) ≫ j) := by
    rw [Category.assoc, hg]
    exact V.unop.prop
  have : Etale (g ≫ W.hom) := Etale.of_comp _ j
  let V' : U.Etale := MorphismProperty.Over.mk ⊤ (g ≫ W.hom) inferInstance
  let e : (openLocalization j).obj V' ≅ V.unop :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simpa [V'] using hg.symm)
  exact ⟨CostructuredArrow.mk (Y := Opposite.op V') e.inv.op, inferInstanceAs (IsIso e.inv.op)⟩

private lemma mono_open_lan (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {P : U.Etaleᵒᵖ ⥤ A} {Q : X.Etaleᵒᵖ ⥤ A}
    (ψ : (openLocalization j).op.lan.obj P ⟶ Q)
    (hψ : Mono ((openLocalization j).op.lanUnit.app P ≫
      Functor.whiskerLeft (openLocalization j).op ψ)) : Mono ψ := by
  have (V : X.Etaleᵒᵖ) : Mono (ψ.app V) := by
    by_cases h : Nonempty (CostructuredArrow (openLocalization j).op V)
    · obtain ⟨s⟩ := h
      obtain ⟨t, ht⟩ := openLocalization_iso j V s
      obtain ⟨hT⟩ := openLocalization_terminal j V t
      have h₂ := ((openLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
        P V).isIso_ι_app_of_isTerminal t hT
      change IsIso (((openLocalization j).op.lanUnit.app P).app t.left ≫
        ((openLocalization j).op.lan.obj P).map t.hom) at h₂
      have key : (((openLocalization j).op.lanUnit.app P).app t.left ≫
          ((openLocalization j).op.lan.obj P).map t.hom) ≫ ψ.app V =
          ((openLocalization j).op.lanUnit.app P ≫
            Functor.whiskerLeft (openLocalization j).op ψ).app t.left ≫
            Q.map t.hom := by
        rw [Category.assoc, ψ.naturality]
        simp
      have hm : Mono ((((openLocalization j).op.lanUnit.app P).app t.left ≫
          ((openLocalization j).op.lan.obj P).map t.hom) ≫ ψ.app V) := by
        rw [key]
        infer_instance
      rw [← IsIso.inv_hom_id_assoc (((openLocalization j).op.lanUnit.app P).app t.left ≫
        ((openLocalization j).op.lan.obj P).map t.hom) (ψ.app V)]
      infer_instance
    · have : IsEmpty (CostructuredArrow (openLocalization j).op V) :=
        not_nonempty_iff.mp h
      have hP := (isColimitEquivIsInitialOfIsEmpty A _).1
        ((openLocalization j).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit P V)
      exact (hP.isZero).mono _
  exact NatTrans.mono_of_mono_app ψ

private lemma open_unit_presheaf (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology A) :
    (sheafToPresheaf _ A).map
        ((openImmersionLowerShriekAdjunction A j).unit.app F) =
      (openLocalization j).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (openLocalization j).op
          (toSheafify _ ((openLocalization j).op.lan.obj F.obj)) := by
  dsimp only [openImmersionLowerShriekAdjunction, localizationLowerShriekAdjunction,
    Functor.sheafPullbackConstruction.sheafAdjunctionContinuous]
  erw [Adjunction.map_restrictFullyFaithful_unit_app]
  simp [Functor.lanAdjunction_unit]

private lemma mono_open_of_mono_transpose (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {F : Sheaf U.smallEtaleTopology A}
    {N : Sheaf X.smallEtaleTopology A}
    (φ : (openImmersionLowerShriek A j).obj F ⟶ N)
    (hφ : Mono ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
      (openImmersionRestriction A j).map φ)) : Mono φ := by
  let adj := sheafificationAdjunction X.smallEtaleTopology A
  let ψ := adj.homEquiv _ _ φ
  have hψ : Mono ψ := by
    refine mono_open_lan A j ψ ?_
    have e : (openLocalization j).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (openLocalization j).op ψ =
        (sheafToPresheaf _ A).map
          ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
            (openImmersionRestriction A j).map φ) := by
      rw [Functor.map_comp, open_unit_presheaf, Category.assoc]
      congr 1
    have h := (sheafToPresheaf _ A).map_mono
      ((openImmersionLowerShriekAdjunction A j).unit.app F ≫
        (openImmersionRestriction A j).map φ)
    rw [← e] at h
    exact h
  have : φ = (presheafToSheaf _ A).map ψ ≫ adj.counit.app N := by
    exact ((adj.homEquiv _ _).symm_apply_apply φ).symm.trans (adj.homEquiv_counit (g := ψ))
  rw [this]
  have : Mono ((presheafToSheaf X.smallEtaleTopology A).map ψ) :=
    (presheafToSheaf X.smallEtaleTopology A).map_mono ψ
  exact mono_comp _ _

private lemma mono_open_to_star (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf U.smallEtaleTopology A) :
    Mono ((openImmersionLowerShriekToLowerStar A j).app F) := by
  refine mono_open_of_mono_transpose A j _ ?_
  rw [openImmersionLowerShriekToLowerStar_app, Functor.map_comp, ← Category.assoc]
  erw [(openImmersionLowerShriekAdjunction A j).unit_naturality,
    Category.assoc,
    (openImmersionLowerShriekAdjunction A j).right_triangle_components,
    Category.comp_id]
  infer_instance

private lemma mono_compactification_to_star_aux
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (F : Sheaf U.smallEtaleTopology A) :
    Mono ((lowerStar A c.g).map ((openImmersionLowerShriekToLowerStar A c.i).app F) ≫
      (lowerStarComp A c.i c.g f c.comm).hom.app F) := by
  have := mono_open_to_star A c.i F
  infer_instance

private lemma mono_compactification_to_star (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} {f : U ⟶ X} (c : Compactification f)
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Mono ((compactificationSheafToDirectImage A c).app F) :=
  mono_compactification_to_star_aux (ModuleCat.{u + 1} A) c F

private lemma normalization_comparison_eq
    (A : Type (u + 1)) [CommRing A]
    (N N' : EtaleCompactSupportNormalization A)
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsNoetherian U] [IsNoetherian X] (c : Compactification f) :
    N.comparison f c = N'.comparison f c := by
  have hs : N.sheafComparison f c = N'.sheafComparison f c := by
    apply NatTrans.ext
    funext F
    have := mono_compactification_to_star A c F
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app F)).1
    rw [N.sheaf_normalization, N'.sheaf_normalization]
  apply Iso.ext_inv
  apply (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Qh |>.map_injective
  apply NatTrans.ext
  funext K
  change (N.comparison f c).inv.app (DerivedCategory.Qh.obj K) =
    (N'.comparison f c).inv.app (DerivedCategory.Qh.obj K)
  rw [N.derived_normalization, N'.derived_normalization, hs]

/-- The termwise derived sum-extension/restriction adjunction on whole unbounded categories.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md,
first assertion (blueprint: lemma-affine-space-etale-localization--4).
Both sheaf functors are exact; the degreewise unit and counit descend through localization,
and their triangle identities descend as well. The construction uses the existing sheaf
adjunction and the general exact-functor derived-adjunction construction. -/
noncomputable def etaleAmbientLeftComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  Functor.isoWhiskerRight (N.comparison u (d.ofComp c).restrict).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A c (d.ofComp c) ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (c.comp (d.ofComp c)) d

/-- For finite commutative coefficients the ordinary ambient right adjoint localizes along
separated etale maps of finite type. The isomorphism is natural in every unbounded input K.
Here `F` and `G`, with the supplied adjunctions, denote the right adjoints f^× and (fu)^×;
quantifying over them avoids imposing a choice of Brown right adjoint. Compactifications
are arbitrary. Their sources are Noetherian as finite-type schemes over the Noetherian base.
The canonical isomorphism is obtained from the Hom bijections in the proof below, by sending
the identity to its image; its inverse is obtained from the inverse bijections. In particular
its adjoint transpose is the inverse compact-support composition comparison followed by
the sum-extension counit and then the compact-support counit. The displayed equation records
this normalization in Lean. It holds for every graph-normalized comparison family `N` from
lemma-affine-space-etale-localization--5, which has a recorded existence theorem. Thus `N`
is not an additional hypothesis or an unconstrained choice of comparison.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md,
second assertion (blueprint: lemma-affine-space-etale-localization--4).

Proof:
1. Identify $U_{\mathrm{et}}$ with the localized site $X_{\mathrm{et}}/U$: an object on either
side is an etale $V\to X$ with a lift $V\to U$, and the morphisms and covering families are the
same. Composition and etale base change are supplied by
[lemma-affine-space-etale-localization--5]. For the converse, the graph of a lift $V\to U$
is a section of the etale projection, separated by [lemma-affine-space-etale-localization--5],
$V\times_XU\to V$, so is an open immersion by [lemma-affine-space-etale-localization--5]. Its
composite with the etale projection $V\times_XU\to U$ is etale. Thus the sites have exactly the
same objects, arrows and jointly surjective covers. Apply
[lemma-affine-space-etale-localization--5] to the constant sheaf of rings $A_X$. Its
restriction is $A_U$, its extension is precisely the direct-sum sheafification of
[lemma-acyclicity-pulled-back-injectives], and its restriction is $u^*$: the sectionwise
identification of inverse image with restriction is [lemma-affine-space-etale-localization--5], For
each $a\in A$, multiplication by $a$ is an endomorphism of the underlying abelian sheaf; naturality
of that node's isomorphism $\rho_G$ for this endomorphism gives $\rho_G\circ
u^{-1}(a)=a\circ\rho_G$. A section of the constant ring sheaf is locally represented by an element
of $A$; the preceding equality on such a cover and the sheaf axiom therefore show that $\rho_G$ is
$A_X$-linear, and the identification holds for constant-ring module sheaves. Consequently $u_!$ and
$u^*$ are exact and $u_!\dashv u^*$ on module sheaves.
2. The preceding exact functors induce termwise functors on unbounded derived categories by
[situation-conventions]. The sheaf adjunction gives a complex
adjunction: its transpose commutes with differentials by naturality, and the units and counits are
chain maps. Descend these natural transformations using
[lemma-affine-space-etale-localization--5]. The two triangle identities hold after
precomposition with localization, since they hold degreewise; clause (3) of that node makes them
hold on the derived categories. Hence the descended functors are adjoint, without any boundedness
condition.
3. For the compact-support comparison work between the Noetherian schemes in the second assertion.
On affine charts the etale ring-map result [lemma-affine-space-etale-localization--5] says that
$u$ is quasi-finite; this is local on the affine charts in the definition. Since $u$ is separated
and finite type and $X$ is quasi-compact by the Noetherian hypothesis and quasi-separated by
[lemma-affine-space-etale-localization--5], [lemma-affine-space-etale-localization--5] supplies
$u=pj$ with $j:U\hookrightarrow T$ open and $p:T\to X$ finite. The finite map is proper by
[lemma-affine-space-etale-localization--5], so this really is a compactification. Its finite-type
source $T$ is Noetherian by [lemma-affine-space-etale-localization--5]. Construct the comparison on
the defining presheaf. For a lift $a:V\to U$ over $X$, its graph in $U\times_XV$ is open by
[lemma-affine-space-etale-localization--5]; since $U\times_XV$ is open in $T\times_XV$ by
[lemma-affine-space-etale-localization--5], the graph is open there too. Both projections to $V$
are separated by [lemma-affine-space-etale-localization--5]. The graph is a section of the separated
$T\times_XV\to V$, so is closed there by [lemma-affine-space-etale-localization--5]. Extend
a section of $F(V,a)$ by zero on this open-and-closed graph. For a test morphism $b:V'\to V$, the
inverse image of the graph of $a$ is exactly the graph of $ab$: on this component the section
restricts to $s|_{V'}$, and on its open complement zero restricts to zero. These two restrictions
cover $T\times_XV'$, so the sheaf axiom proves equality with the section constructed from $ab$.
This also commutes with a morphism $F\to F'$, component by component. Summing gives a natural
presheaf map into $(p_*j_!F)(V)$, hence a sheaf map $u_!F\to p_*j_!F$. By
[lemma-affine-space-etale-localization--5], [lemma-weil-pbc-finite-stalk-formula], and
[lemma-affine-space-etale-localization--5], the stalk map sends a generator represented by $(V,\bar
v,a,s)$ to the tuple with germ $[s]$ at $a\bar v$ and zero at every other point of $T_{\bar x}$.
Indeed the graph has exactly the point $a\bar v$ in that fibre, and its complement carries the
zero section. Thus this map is the identity on the finite sum $\bigoplus_{\bar z\in U_{\bar
x}}F_{\bar z}$; the boundary summands are zero. The finite-stalk formula is $A$-linear since the
maps are evaluations of sections. Forgetting $A$ reflects isomorphisms, so
[lemma-weil-pbc-geometric-stalk-conservative] proves $u_!\cong p_*j_!$.
4. Finite direct image is exact by [lemma-weil-pbc-finite-direct-image-exact]; forgetting the
constant $A$-action detects exactness. Thus [lemma-affine-space-etale-localization--5]
identifies its unbounded total derived functor with termwise descent. Descend step 3's natural
sheaf isomorphism by [lemma-affine-space-etale-localization--5]. We obtain $Du_!\cong
Rp_*Dj_!$, the fixed-compactification candidate of
[proposition-construction-independence-rf-shriek]. This step makes no use of compactification
independence or composition on unbounded objects.
5. Construct the comparison maps before asserting their invertibility. For every scheme map $h$,
exact module inverse image is left adjoint to module direct image by
[situation-conventions]. Direct image carries K-injectives to K-injectives:
for an acyclic complex $C$, the complex adjunction identifies maps $C\to h_*I$ up to homotopy with
maps $h^*C\to I$, which vanish since $h^*C$ is acyclic. The bijection of
[lemma-affine-space-etale-localization--5], applied after K-injective resolution as in
[proposition-construction-independence-rf-shriek], therefore gives $h^*\dashv Rh_*$ on unbounded
categories. Open restriction $a^*$ also preserves K-injectives: its exact left adjoint $Da_!$ is
step 2 for the open immersion $a$. In an open Cartesian square with proper $p:T\to B$, open $a:V\to
B$, pullback open $b:T_V\to T$, and $p_V:T_V\to V$, the sheaf identity $a^*p_*=p_{V*}b^*$ follows
directly by evaluating on an etale test object of $V$ [lemma-affine-space-etale-localization--5].
Applying it to a K-injective complex gives an unbounded natural isomorphism $a^*Rp_*\cong
Rp_{V*}b^*$: $b^*I$ is K-injective by the preceding argument. Consequently define, for every
unbounded $N$, the proper/open map
$$\beta_N:Da_!Rp_{V*}N\longrightarrow Rp_*Db_!N$$
as the $Da_!\dashv a^*$ transpose of the inverse open-restriction isomorphism $Rp_{V*}N\cong
a^*Rp_*Db_!N$; here $b^*Db_!N=N$, since extension by zero restricts back to its original sheaf,
degreewise [lemma-affine-space-etale-localization--5]. For a proper refinement $q:T_1\to T_2$ of
open immersions $j_i:Z\hookrightarrow T_i$, the same open restriction identifies $j_2^*Rq_*Dj_{1!}M$
with $M$. Indeed $Z$ is an open-and-closed section of $T_1\times_{T_2}Z\to Z$ by
[proposition-construction-independence-rf-shriek--7], so pushforward of its extension by zero is the
identity on this component and zero on its complementary component. The clopen decomposition
[lemma-affine-space-etale-localization--5] identifies the module category with the product of its
two module categories (the actions and morphisms are componentwise). Extension on the section is
both adjoints to restriction, so carries K-injectives to K-injectives by the complex Hom argument
already given. Pushforward then computes the identity on this component and zero on the other,
also on unbounded derived categories. Define $\alpha_M:Dj_{2!}M\to Rq_*Dj_{1!}M$ as the transpose
of this identification. These formulas are natural transformations on the unbounded categories,
not arbitrary extensions of transformations from $D^+$. For composable scheme maps $h$ and $g$,
take a K-injective representative $I$. The preceding preservation result means $h_*I$ is
K-injective, so $Rg_*Rh_*QI=Q(g_*h_*I)=Q((gh)_*I)=R(gh)_*QI$. The middle equality is the canonical
identification of iterated fibre products in the sectionwise direct-image definition. Maps are
represented by homotopy classes between K-injectives, and both composites send such a class to the
same $g_*h_*$ class. This proves naturality and associativity of ordinary unbounded direct-image
composition, for any coefficient ring and without an invertible-prime assumption.
6. The unbounded comparison maps in step 5 are defined by the same units, counits and
open-restriction identities as the bounded-below maps. Their coherence does not require detecting
equality by telescopes. For two successive refinements $q,r$, restrict the composite
$Rr_*\alpha_q\circ\alpha_r$ along the final open immersion. Open restriction turns each $\alpha$
into the identity of $M$, so the restricted composite is the identity as well. The $Dj_!\dashv
j^*$ bijection now implies that this composite equals $\alpha_{rq}$ after the associative ordinary
direct-image identification proved in step 5. This is equality of adjoint transposes; restriction
need not be faithful on arbitrary morphisms. For composable compactifiable maps, construct nested
compactifications explicitly. For $Z\xrightarrow{h}Y\xrightarrow{g}S$, compactify $g$ as
$Y\xrightarrow{v}\overline Y\to S$ and compactify $vh$ as $Z\xrightarrow{a}\overline
Z\xrightarrow{p}\overline Y$ by [theorem-nagata-s-compactification-theorem--1]. Every open piece of
a Noetherian scheme is Noetherian by [lemma-affine-space-etale-localization--5]; applying this to
intersections with affine opens shows that $v$ is quasi-compact. Thus $v$ is finite type by
[lemma-affine-space-etale-localization--5]. The composite $vh$ is finite type: on affine charts
finite lists of algebra generators concatenate, and finite covers of the preimages concatenate
[lemma-affine-space-etale-localization--5]. It is separated: the diagonal factors through $Z\times_Y
Z$ as the closed diagonal of $h$, followed by the closed base change of the diagonal of $v$; for an
open immersion the diagonal is an isomorphism [lemma-affine-space-etale-localization--5,
lemma-affine-space-etale-localization--5]. Hence $vh$ has the hypotheses for Nagata; $\overline Y$
is quasi-compact and quasi-separated. Thus the cited existence assertion applies. The resulting
proper source $\overline Z$ is Noetherian by [lemma-affine-space-etale-localization--5]. Put
$V=\overline Z\times_{\overline Y}Y$ with open $b:V\to\overline Z$ and proper $p_Y:V\to Y$. Then
$Z\hookrightarrow V\to Y$ compactifies $h$, and the composite compactification of $gh$ is
$Z\xrightarrow{a}\overline Z\to S$. Apply $\beta$ to the extension by zero from $Z$ to $V$, and
then apply the proper direct image from $\overline Y$ to $S$. The proper/open map $\beta$ of step
5, open-extension composition [proposition-composition-base-change-rf-shriek--1], and ordinary
direct-image composition proved in step 5, give a natural map $c:Rf_!Du_!\to R(fu)_!$ for the nested
compactifications after step 4. Invertibility will be proved in step 7. For three factors, the two
proper/open composites are transposes under the composite open-extension adjunction of the same
open-restriction identity: on a test object inside the smallest open both are evaluation on the
same iterated fibre product. The counit of the composite adjunction is $\varepsilon^a\circ
Da_!(\varepsilon^b)$; substituting it makes the two transposes equal by naturality of
$\varepsilon^a$ and the triangle identities. Associativity of proper direct image and open
extension then gives associativity of composition. After invertibility is established in step 7,
comparing with different nested compactifications through a common proper refinement
[lemma-affine-space-etale-localization--5] is independent of the refinement by the preceding
identity for $\alpha$. These equations establish coherence of the constructed maps; after step 7
establishes invertibility they give coherent unbounded composition.
7. For the second assertion $A$ is now a finite commutative ring. Only now use
[proposition-construction-independence-rf-shriek--7], and only on bounded-below input over this
finite ring: its proper-refinement and usual-composition assertions give invertibility in that
range. The maps here have the prescribed identity transpose over the source, and the proper/open
transpose defining usual composition, so these are the comparisons named in that statement. Extend
invertibility, not existence, by an explicit telescope. All the functors on the two sides are exact:
termwise open extension is triangulated by [situation-conventions] and total direct image is
triangulated by [lemma-affine-space-etale-localization--5]. They preserve coproducts: open
extension is a left adjoint by step 2, and proper direct image preserves them as follows. For each
proper map $r:V\to T$ in the construction, $T$ is Noetherian and hence quasi-compact. Apply
[lemma-affine-space-etale-localization--5] to choose $d\geq0$ bounding its ordinary fibre
dimensions. Every $A$-module sheaf is killed by a positive integer: the order of the additive
element $1\in A$ kills the unit and hence every section (for the zero ring use the integer 1). Its
underlying abelian sheaf is therefore torsion. [lemma-affine-space-etale-localization--5] gives
abelian higher-direct-image vanishing above $2d$. The isomorphism $b_r$ and the
cohomology/forgetting assertion in [lemma-affine-space-etale-localization--5], applied to a sheaf in
degree zero (choose identity maps to complete a Cartesian square), transfer that bound to module
higher direct images. Forgetting is conservative, so vanishing of their underlying abelian sheaves
is vanishing in modules. Properness implies quasi-compactness and separatedness, hence
quasi-separatedness by [lemma-affine-space-etale-localization--5]. Thus all hypotheses, including
the finite-ring hypothesis and a bound valid for EVERY module sheaf, of
[corollary-proper-direct-image-finite-coefficients-localizing] hold. It gives unbounded coproduct
preservation for $Rr_*$. No arbitrary-ring version of proper-coproducts is used. Proper base change
and finite-type-over-Noetherian give proper maps between Noetherian schemes in each diagram
[lemma-affine-space-etale-localization--5, lemma-affine-space-etale-localization--5]; all open
pieces are Noetherian by [lemma-affine-space-etale-localization--5]. For a representing complex $L$,
put $L_n=\sigma_{\ge -n}L$ using [proposition-open-direct-image-preserves-finite]. These are bounded
below, their inclusions are chain maps, and their degreewise colimit is exactly $L$: in degree $i$
the system is eventually constant at $L^i$ with identity transitions. By
[proposition-open-direct-image-preserves-finite], $QL$ is the homotopy colimit of $QL_n$. By
[lemma-affine-space-etale-localization--5], both sides of $\alpha$ and $c$ preserve this telescope.
The units and counits used in step 5 commute with shifts because they are the classes of degreewise
maps on the K-injective models, with the same signs on both sides. Hence the resulting comparisons
commute with shifts. Naturality and [lemma-affine-space-etale-localization--5] supply a morphism
between their telescope triangles. On each of the two coproduct vertices it is the coproduct of the
isomorphisms on $QL_n$, hence an isomorphism. In the long exact cohomology ladder
[lemma-affine-space-etale-localization--5], the four maps surrounding $H^i$ of the third vertex are
isomorphisms. Evaluate the ladder at any geometric stalk; stalks are exact by
[lemma-affine-space-etale-localization--5] after forgetting the module action, and isomorphisms of
the cohomology sheaves are detected by [lemma-weil-pbc-geometric-stalk-conservative]. In this ladder
of modules, write the five terms as $P\to Q\to H\to R\to S$. For surjectivity, given $h$ in the
lower $H$, lift its image in the lower $R$ uniquely to $r$ in the upper $R$. Its image in the upper
$S$ is zero, since the fifth vertical map is injective and the lower sequence is exact. Thus $r$ is
the image of an upper $h_0$ by exactness. The difference between $h$ and the image of $h_0$ has zero
connecting image, so comes from the lower $Q$. Lift that element along the second vertical
isomorphism and add its image to $h_0$. For injectivity, an element killed in the lower third vertex
has zero connecting image by injectivity of the fourth map, hence comes from the upper second
vertex; its lower lift comes from the lower first vertex, which lifts along the first map, and
injectivity of the second map then forces the element to be zero. Hence the already constructed
comparison at $QL$ induces an isomorphism on every $H^i$, and is an isomorphism in the derived
category. Thus the fixed-compactification refinement and composition maps are invertible for all
unbounded complexes of modules over the finite ring $A$. In particular step 4's finite candidate
identifies with $Ru_!$. This argument uses stupid tails of a representing complex, not $\tau_{\le
n}L$ (which need not be bounded below), and does not claim that stupid truncation itself descends to
the derived category.
8. Continue with the finite ring $A$ of the second assertion. For $M\in D(U_{\mathrm{et}},A)$, the
derived adjunction of step 2 and the ambient adjunctions of
[theorem-existence-exceptional-inverse-image--1] give natural bijections
$$\operatorname{Hom}_U(M,u^*f^\times K)\cong\operatorname{Hom}_X(Du_!M,f^\times
K)\cong\operatorname{Hom}_S(Rf_!Du_!M,K)
\cong\operatorname{Hom}_S(R(fu)_!M,K)\cong\operatorname{Hom}_U(M,(fu)^\times
K).$$
The middle comparison is the unbounded composition constructed in steps 4–7. Define the map
$u^*f^\times K\to(fu)^\times K$ as the image of the identity under these bijections and define its
inverse using the inverse bijections on the other identity. Naturality in $M$ says each composite
is the corresponding identity; naturality in $K$ gives the natural isomorphism. Write
$L=u^*f^\times K$ and $c_M:Rf_!Du_!M\xrightarrow{\sim}R(fu)_!M$ for step 7. The transpose of this
isomorphism is explicitly
$$R(fu)_!L\xrightarrow{c_L^{-1}}Rf_!Du_!L\xrightarrow{Rf_!(\varepsilon^u_{f^\times
K})}Rf_!f^\times K\xrightarrow{\varepsilon^f_K}K.$$
This specifies the counit normalization; the unit is its adjoint transpose and the triangle
identities follow from those of the two adjunctions. For a further separated finite-type etale
$v:W\to U$ with $fuv$ compactifiable, the composite sum-extension adjunction has counit
$\varepsilon^u\circ Du_!(\varepsilon^v)$. Here $Du_!Dv_!$ and $D(uv)_!$ are canonically identified
as left adjoints to $v^*u^*=(uv)^*$: send the unit of either adjunction through the other Hom
bijection to define the comparison, and do the same in reverse; the triangle identities make their
composites identities. This identification has the stated composite counit. The coherence proved
by adjoint transposes in step 6 identifies $c_{f,uv}$ with $c_{fu,v}\circ(c_{f,u}Dv_!)$ after the
canonical association of the composite functors. Hence the direct and the iterated Hom bijections
both send a map to its composite with these same two counits and $\varepsilon^f$. They agree on
every $M$, so their identity constructions give the same localization isomorphism.
-/
theorem existsUnique_etaleAmbientAdjointLocalityIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f))
    (F : DerivedCategoryModule A S ⥤ DerivedCategoryModule A X)
    (G : DerivedCategoryModule A S ⥤ DerivedCategoryModule A U)
    (adjF : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ F)
    (adjG : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ G) :
    ∃! e : F ⋙ (upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory ≅ G,
      ∀ (N : EtaleCompactSupportNormalization A) (K : DerivedCategoryModule A S),
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).map
            (e.hom.app K) ≫ adjG.counit.app K =
          (etaleAmbientLeftComparison A N u f c d).inv.app
              ((upperStar (ModuleCat.{u + 1} A) u).mapDerivedCategory.obj (F.obj K)) ≫
            (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
              ((derivedEtaleLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} A) u inferInstance).counit.app (F.obj K)) ≫
            adjF.counit.app K := by
  obtain ⟨N₀⟩ := nonempty_etaleCompactSupportNormalization A
  let adjU := derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) u inferInstance
  let adj := (adjU.comp adjF).ofNatIsoLeft (etaleAmbientLeftComparison A N₀ u f c d)
  refine ⟨adj.rightAdjointUniq adjG, ?_, ?_⟩
  · intro N K
    have hN : etaleAmbientLeftComparison A N₀ u f c d =
        etaleAmbientLeftComparison A N u f c d := by
      unfold etaleAmbientLeftComparison
      rw [normalization_comparison_eq A N₀ N u (d.ofComp c).restrict]
    rw [← hN]
    simpa [adj, Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app,
      Category.assoc] using Adjunction.rightAdjointUniq_hom_app_counit adj adjG K
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply (adjG.homEquiv _ _).symm.injective
    rw [Adjunction.homEquiv_counit, he N₀ K,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
    simp [adj, Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app,
      adjU]

end AlgebraicGeometry.Etale
