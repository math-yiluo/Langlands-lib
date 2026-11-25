/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictionMap
public import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedEquivFields
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedEquiv
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedPinnedMaps
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenRestrictedQCoh

/-! # Compatible open restriction of representing Hom data

The compatibility at identity morphisms determines compatibility at every testing morphism.
Source: Stacks Project, Tags 079W, 08FE and 09RE.
(blueprint: lem-pc-perfect-hom-open-restricted-data).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
noncomputable section

private theorem restriction_map_natural
    {S Y T : Scheme.{u}} (s : Y ⟶ S) (B : Y.Opens) (r : T ⟶ S)
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    {M N Q : schemeDerivedCategory Y} (g : M ⟶ N)
    (f : (derivedPullback (pullback.fst s r)).obj N ⟶
      (derivedPullback (pullback.fst s r)).obj Q) :
    perfectHomOpenRestrictionMap s B r a
        ((derivedPullback (pullback.fst s r)).map g ≫ f) =
      (derivedPullback (pullback.fst (B.ι ≫ s) r)).map
          ((schemeMVDerivedRestriction Y B).map g) ≫
        perfectHomOpenRestrictionMap s B r a f := by
  unfold perfectHomOpenRestrictionMap
  rw [Functor.map_comp]
  have hn := (perfectHomOpenPullbackComparison s B r a).inv.naturality g
  dsimp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc]

/-- Compatibility at a stage identity implies compatibility at every testing morphism.
Source: Stacks Tags 079W and 09RE.
Proof: express each natural Hom equivalence at f by its value on the identity of
F_j. Apply restriction-map naturality to the original expression and use the
supplied identity equation. Independent representing data without that equation
need not agree; this hypothesis repairs the earlier false universal assertion.
(blueprint: new-perfect-hom-open-restricted-stage-pinned). -/
theorem perfect_hom_open_restricted_stage_pinned
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d)
    (he : ∀ j : Set.Ici i,
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj (F.obj j)) (𝟙 _) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j (F.obj j) (𝟙 _))) :
    ∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f) := by
  intro j M f
  have hb := e.stageNatural j _ _ ((schemeMVDerivedRestriction Y B).map f) (𝟙 _)
  have hh := h.stageNatural j M (F.obj j) f (𝟙 _)
  simp only [Category.comp_id] at hb hh
  rw [hb, he j, hh, restriction_map_natural]

/-- Compatibility at the apex identity implies compatibility at every testing morphism.
Source: Stacks Tags 079W and 09RE.
Proof: use testing-object naturality at f and the identity of d.pt on each side,
then restriction-map naturality and the supplied apex identity equation.
This statement makes no assertion about independently chosen unpinned data.
(blueprint: new-perfect-hom-open-restricted-limit-pinned). -/
theorem perfect_hom_open_restricted_limit_pinned
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d)
    (he : e.limitEquiv ((schemeMVDerivedRestriction Y B).obj d.pt) (𝟙 _) =
      perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
        (h.limitEquiv d.pt (𝟙 _))) :
    ∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
      e.limitEquiv ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (h.limitEquiv M f) := by
  intro M f
  have hb := e.limitNatural _ _ ((schemeMVDerivedRestriction Y B).map f) (𝟙 _)
  have hh := h.limitNatural M d.pt f (𝟙 _)
  simp only [Category.comp_id] at hb hh
  rw [hb, he, hh, restriction_map_natural]

/-- Combine the identity-normalized stage and apex equations.
Source: Stacks Tags 079W and 09RE.
Proof: apply the two naturality lemmas to the supplied identity equations.
(blueprint: lem-pc-perfect-hom-open-restricted-data-pinned). -/
theorem perfect_hom_open_restricted_data_pinned
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens) (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y) (F : Set.Ici i ⥤ schemeDerivedCategory Y)
    (d : Cocone F) (h : PerfectHomPushPullData R c s Q F d)
    (e : PerfectHomOpenRestrictedEquivFields R c s B Q F d)
    (hs : ∀ j : Set.Ici i,
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj (F.obj j)) (𝟙 _) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j (F.obj j) (𝟙 _)))
    (hl : e.limitEquiv ((schemeMVDerivedRestriction Y B).obj d.pt) (𝟙 _) =
      perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
        (h.limitEquiv d.pt (𝟙 _))) :
    (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
      e.stageEquiv j ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B
          (Spec.map (R.map (homOfLE j.property))) a (h.stageEquiv j M f)) ∧
    (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
      e.limitEquiv ((schemeMVDerivedRestriction Y B).obj M)
          ((schemeMVDerivedRestriction Y B).map f) =
        perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a
          (h.limitEquiv M f)) := by
  exact ⟨perfect_hom_open_restricted_stage_pinned R c s B a Q F d h e hs,
    perfect_hom_open_restricted_limit_pinned R c s B a Q F d h e hl⟩

/-- Exact open restriction carries a representing pullback Hom cocone to a representing
cocone for the restricted base scheme. There is no shift or outer open direct image
in this conclusion. The two additional equations tie its Hom equivalences on restricted
testing objects to the concrete perfectHomOpenRestrictionMap. These equations specify
which restriction of the original representing equivalences is used.

Source: Stacks Project, Cohomology, Tags 079W and 08FE; perfect.tex, Tag 09RE.
(blueprint: lem-pc-perfect-hom-open-restricted-data).

Proof: For the supplied adjunction a, set sigma =
(conjugateIsoEquiv a (schemeMVAdjunction Y B)).symm (Iso.refl _).
Thus sigma : L -> LB.ι* is the mate of the identity on the common right adjoint.
For any r : T -> Spec(R_i), let b_r be perfectHomOpenBaseChangeMap s B r,
p = pullback.fst s r and p' = pullback.fst (B.ι followed by s) r. Its fst equation
is b_r followed by p = p' followed by B.ι. The concrete comparison kappa_r is
perfectHomComposition b_r p, followed by eqToIso of that fst equation, followed
by (perfectHomComposition p' B.ι).symm, followed by sigma.symm whiskered by Lp'*.
The restriction of a Hom f is kappa_r(M).inv followed by Lb_r*(f), followed by
kappa_r(Q).hom: this is exactly perfectHomOpenRestrictionMap s B r a f.

Write L for restriction to B, pi_j for the original projection, A_j for
Lpi_j*, and J_j = Rpi_j* A_j Q. Choose the derived adjunction a_j of Tag 079W
compatible with the fixed pullback counit and direct-image unit. Its equivalence is
eta_j(M) : Hom(A_j M,A_j Q) -> Hom(M,J_j). Define
rho_j = eta_j(F_j)(h.stageEquiv j F_j (id)). Its inverse is
(h.stageEquiv j J_j).symm (eta_j(J_j).symm (id)). Naturality in M of eta_j and
h.stageEquiv proves eta_j(M)(h.stageEquiv j M f) = f followed by rho_j.
Applying this identity to rho_j and its proposed inverse proves both inverse laws.
Do the same at the apex, using h.limitEquiv and h.limitNatural.

Put U_j = pi_j inverse-image B and v_j = pi_j restricted to B. Restriction gives
L rho_j : L F_j -> L J_j. Compose it with the component of the explicitly
constructed schemeMVOpenRestrictionComparison pi_j B at A_j Q. This identifies
L J_j with Rv_j* (restriction to U_j of A_j Q). The cartesian square identifies
U_j.toScheme with the pullback of B.ι followed by s along the same ring map:
the forward map is pullback.lift of v_j and the restricted second projection;
the inverse is pullback.lift of the open inclusion and second projection, factored
through U_j. The two inverse laws follow by pullback.hom_ext and the open inclusion
monomorphism. Denote this isomorphism by k_j. The counit-pinned pullback composition
isomorphisms on the square give
restriction to U_j of A_j Q = Lk_j* (Lpi'_j* (L Q)), up to natural isomorphism.
Here restriction along an open inclusion is its exact derived pullback, by the
underived restriction/tensor-pullback adjunction and its derived universal property.
The inverse-image comparison is the composite of these two composition
isomorphisms and the equality of the square's morphisms, not an arbitrary iso.
Transport direct image across k_j using the right-derived composition comparison
and the identity comparison; k_j is an isomorphism, so its adjunction counit is
invertible. We obtain a representing isomorphism sigma_j : L F_j ->
Rpi'_j* (Lpi'_j* (L Q)). Repeat this construction at the apex to obtain sigma_inf.

For every M on B, define the new stage equivalence by postcomposition with sigma_j,
followed by the inverse Hom equivalence of the restricted projection adjunction.
Define its apex equivalence in the same way with sigma_inf. Adjunction naturality
and associativity prove the two testing-object naturality equations. Restriction
is exact and preserves quasi-coherent sheaves, hence stageQCoh and limitQCoh.

For j <= k, define the original representing transition J_j -> J_k by applying
eta_k(J_j) to perfectStageMap R s j.property hjk (eta_j(J_j).symm (id)).
The h.stageMap identity at id says F.map(j,k) followed by rho_k equals rho_j
followed by this transition. At the apex, the analogous formula using
perfectLimitMap gives the corresponding equation for the cocone leg.
Apply L to these equations. Naturality of the sectionwise restriction comparison,
and its determining right-derived unit equation, identify the resulting
transitions with the representing transitions for the restricted projections.
The pullback composition associativity equation identifies the square's two
pasted inverse-image comparisons; after applying the Hom adjunction, adjacent
comparison and inverse components cancel. The remaining composites are exactly
perfectStageMap R (B.ι followed by s) and perfectLimitMap R c (B.ι followed by s).
Thus postcomposition by L(F.map(j,k)) and L(d.ι.app j) satisfies the required
stageMap and limitMap fields for every M. For the additional two equations, the
original representing identity eta(M)(h.stageEquiv M f) = f followed by rho
is restricted to B. The mate identities for sigma and the restriction comparison
identify this restricted adjunction formula with kappa(M).inv followed by Lb*(f)
followed by kappa(Q).hom. This is the displayed equation with the specified
perfectHomOpenRestrictionMap, at a stage and at the apex. Package these fields
and equations. Since L has fully faithful right adjoint, its counit is invertible,
so every testing object on B is isomorphic to L of its open direct image; testing
object naturality extends these pinned equations to all objects on B.
The argument uses neither compactness nor perfectness. For the empty open every
Hom set is a singleton; for the full open the same comparison formulas apply.
For Q = 0, representability makes every representing object zero, so the
construction still works. No arbitrary existence witness is used in a definition. -/
theorem perfect_hom_open_restricted_data
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    {i : I} {Y : Scheme.{u}} (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (B : Y.Opens)
    (a : derivedPullback B.ι ⊣ schemeDerivedDirectImage B.ι)
    (Q : schemeDerivedCategory Y)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d) :
    let L := schemeMVDerivedRestriction Y B
    ∃ hB : PerfectHomPushPullData R c (B.ι ≫ s) (L.obj Q) (F ⋙ L) (L.mapCocone d),
      (∀ (j : Set.Ici i) (M : schemeDerivedCategory Y) (f : M ⟶ F.obj j),
        hB.stageEquiv j (L.obj M) (L.map f) =
          perfectHomOpenRestrictionMap s B (Spec.map (R.map (homOfLE j.property))) a
            (h.stageEquiv j M f)) ∧
      (∀ (M : schemeDerivedCategory Y) (f : M ⟶ d.pt),
        hB.limitEquiv (L.obj M) (L.map f) =
          perfectHomOpenRestrictionMap s B (Spec.map (c.ι.app i)) a (h.limitEquiv M f)) := by
  obtain ⟨e, hs, hl⟩ := perfect_hom_open_restricted_pinned_equiv R c s B a Q F d h
  obtain ⟨hs', hl'⟩ := perfect_hom_open_restricted_data_pinned R c s B a Q F d h e hs hl
  obtain ⟨hm, hc⟩ := perfect_hom_open_restricted_pinned_maps R c s B a Q F d h e hs' hl'
  obtain ⟨hq, hq'⟩ := perfect_hom_open_restricted_qcoh R c s B Q F d h
  exact ⟨{
    stageQCoh := hq
    limitQCoh := hq'
    stageEquiv := e.stageEquiv
    limitEquiv := e.limitEquiv
    stageNatural := e.stageNatural
    limitNatural := e.limitNatural
    stageMap := hm
    limitMap := hc }, hs', hl'⟩

end
end AlgebraicGeometry
