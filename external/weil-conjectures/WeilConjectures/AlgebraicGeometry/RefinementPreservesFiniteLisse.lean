/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ConstructibleSheaf.Refinement

import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison

/-! # Finite local constancy under refinement

Source: Stacks Project, Tags 095A, 03Q1 (3), and 03SI.
(blueprint: lem-weil-pbc-refinement-preserves-finite-lisse).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

open CategoryTheory.Limits Opposite in
/-- Constant sheaves pull back to constant sheaves, with unrestricted coefficient universe. -/
private theorem constant_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    [F.IsConstant X.smallEtaleTopology] :
    ((etaleSetPullback g).obj F).IsConstant Y.smallEtaleTopology := by
  have h := Sheaf.isConstant_sheafPullback g.Etale (K := Y.smallEtaleTopology) terminalIsTerminal
    (terminalIsTerminal.isTerminalObj g.Etale) F
  exact Sheaf.isConstant_congr _
    ((Functor.sheafPullbackConstruction.sheafPullbackIso g.Etale (Type (u + 1))
      X.smallEtaleTopology Y.smallEtaleTopology).app F)

open CategoryTheory.Limits Opposite in
/-- Localized restriction and inverse image along an etale map have the same constancy. -/
private theorem constant_over_iff {X : Scheme.{u}} (U : X.Etale)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    (F.over U).IsConstant (X.smallEtaleTopology.over U) ↔
      ((etaleSetPullback U.hom).obj F).IsConstant U.left.smallEtaleTopology := by
  let e : (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U) ≅
      (etaleSetPullback U.hom).obj F :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (X := (Etale.overSheafEquiv U (Type (u + 1))).functor.obj (F.over U))
      (Y := (Etale.localizationRestriction (Type (u + 1)) U.hom U.prop).obj F)
      (Functor.isoWhiskerRight (NatIso.op (Etale.etaleToOverCompForgetIso U).symm) F.obj) ≪≫
        ((Classical.choose (etaleSetInverseImageRestriction U.hom)).app F).symm
  rw [← Sheaf.isConstant_sheafCongr_functor_iff
    (J := X.smallEtaleTopology.over U) (K := U.left.smallEtaleTopology)
    (Etale.overEquiv U) Over.mkIdTerminal (F.over U)]
  constructor
  · intro h
    have : ((Etale.overSheafEquiv U (Type (u + 1))).functor.obj
        (F.over U)).IsConstant U.left.smallEtaleTopology := h
    exact Sheaf.isConstant_congr _ e
  · intro h
    have := h
    exact Sheaf.isConstant_congr _ e.symm

open CategoryTheory.Limits Opposite in
/-- Inverse image along any scheme morphism preserves local constancy of sheaves of sets.
Source: Stacks Project, Tag 095A (Lemma 59.64.2), using Modules on Sites, Tag 093R.
(blueprint: lem-weil-pbc-refinement-preserves-finite-lisse).

Proof: choose an etale cover of X trivializing F and base change it along g. Its members
are etale over Y and jointly surjective, so they form an etale cover of Y. Restriction
of inverse image to a member is inverse image of the original restriction along the
projection to the corresponding member of the original cover. This follows by the
composition comparison and the equality of the two maps from the fibre product to X;
restriction is inverse image along the etale structure map, after transporting through
the equivalence with the localized site. The original restriction is a constant sheaf
with some coefficient set in Type (u + 1). Inverse image preserves this constant sheaf,
by the constant-sheaf adjunction (Tag 093R), for coefficient sets in this full universe.
Thus every restriction to the base-changed cover is constant. This witnesses local
constancy of the inverse image. The empty cover on an empty scheme is permitted, and
neither the set of coefficients nor its cardinality is restricted. -/
private theorem etaleSetLocallyConstant_pullback {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : IsLocallyConstantEtaleSheafOfSets F) :
    IsLocallyConstantEtaleSheafOfSets ((etaleSetPullback g).obj F) := by
  classical
  obtain ⟨𝒰, h𝒰⟩ := hF
  obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  refine ⟨𝒰.pullback₂ g, fun j => ?_⟩
  apply (constant_over_iff (Cover.etalePrecoverageToEtale (𝒰.pullback₂ g) j)
    ((etaleSetPullback g).obj F)).mpr
  change ((etaleSetPullback (pullback.snd (𝒰.f j) g)).obj
    ((etaleSetPullback g).obj F)).IsConstant (pullback (𝒰.f j) g).smallEtaleTopology
  have h₁ : ((etaleSetPullback (𝒰.f j)).obj F).IsConstant
      (𝒰.X j).smallEtaleTopology := (constant_over_iff (𝒰.etalePrecoverageToEtale j) F).mp (h𝒰 j)
  have h₂ : ((etaleSetPullback (pullback.fst (𝒰.f j) g)).obj
      ((etaleSetPullback (𝒰.f j)).obj F)).IsConstant
      (pullback (𝒰.f j) g).smallEtaleTopology := constant_pullback (pullback.fst (𝒰.f j) g)
    ((etaleSetPullback (𝒰.f j)).obj F)
  let e : (etaleSetPullback (pullback.fst (𝒰.f j) g)).obj
      ((etaleSetPullback (𝒰.f j)).obj F) ≅
      (etaleSetPullback (pullback.snd (𝒰.f j) g)).obj ((etaleSetPullback g).obj F) :=
    (c X (𝒰.X j) (pullback (𝒰.f j) g) (𝒰.f j) (pullback.fst (𝒰.f j) g)).app F ≪≫
      eqToIso (congrArg (fun m => (etaleSetPullback m).obj F) pullback.condition) ≪≫
      ((c X Y (pullback (𝒰.f j) g) g (pullback.snd (𝒰.f j) g)).app F).symm
  exact Sheaf.isConstant_congr _ e

open CategoryTheory.Limits Opposite in
/-- Fully faithful inverse image along a universal homeomorphism reflects constancy. -/
private theorem constant_descend {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsUniversalHomeomorphism p] (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : ((etaleSetPullback p).obj F).IsConstant Y.smallEtaleTopology) :
    F.IsConstant X.smallEtaleTopology := by
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    p.Etale (Type (u + 1)) X.smallEtaleTopology Y.smallEtaleTopology
  let e : etaleSetPullback p ≅ (Etale.sheafEquivalence (Type (u + 1)) p).inverse :=
    adj.leftAdjointUniq (Etale.sheafEquivalence (Type (u + 1)) p).symm.toAdjunction
  have : (etaleSetPullback p).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  let ci : constantSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ etaleSetPullback p ≅
      constantSheaf Y.smallEtaleTopology (Type (u + 1)) :=
    (Functor.isoWhiskerLeft _
      (Functor.sheafPullbackConstruction.sheafPullbackIso p.Etale (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology)).symm ≪≫
      p.Etale.constantSheafsheafPullbackIso (Type (u + 1))
        X.smallEtaleTopology Y.smallEtaleTopology terminalIsTerminal
        (terminalIsTerminal.isTerminalObj p.Etale)
  let := hF
  obtain ⟨a, ⟨i⟩⟩ := ((etaleSetPullback p).obj F).mem_essImage_of_isConstant
  exact Sheaf.isConstant_of_iso _
    ((etaleSetPullback p).preimageIso (i.symm ≪≫ (ci.app a).symm))

open CategoryTheory.Limits Opposite in
/-- Local constancy descends along a universal homeomorphism.
Source: Stacks Project, Tags 03SI and 04DZ; compare the cover construction in
`WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`.
(blueprint: lem-weil-pbc-refinement-preserves-finite-lisse).

Proof: take a trivializing etale cover of the inverse image of F on Y. Base change along
p is an equivalence of etale categories (04DZ); choose for each member an etale X-scheme
whose base change is isomorphic to that member. These X-schemes cover X: lift a point
of X through the surjective map p, cover the lift by an original member, and project its
image under the chosen isomorphism to the corresponding X-scheme. Base change of p to
each chosen X-scheme is again a universal homeomorphism. Its inverse image is fully
faithful on sheaves, since it is part of the topos equivalence (03SI). Restrictions of F
to these X-schemes pull back to the original constant restrictions, using the composition
comparison and restriction/localized-site comparison. Constancy descends under this
fully faithful inverse image: the inverse image of the constant sheaf on the same
coefficient set is constant (093R), and full faithfulness lifts the trivialization and
its inverse, including their inverse identities. Hence the descended cover trivializes
F. No finiteness of stalks or of the coefficient set is required, and the argument also
allows the empty scheme and the empty trivializing cover. -/
private theorem etaleSetLocallyConstant_descend {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsUniversalHomeomorphism p] (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (hF : IsLocallyConstantEtaleSheafOfSets ((etaleSetPullback p).obj F)) :
    IsLocallyConstantEtaleSheafOfSets F := by
  classical
  have : p.Etale.IsEquivalence := Hom.isEquivalence_etale p
  obtain ⟨𝒰, h𝒰⟩ := hF
  obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  let V (i : 𝒰.I₀) : X.Etale := p.Etale.objPreimage (𝒰.etalePrecoverageToEtale i)
  let e (i : 𝒰.I₀) : p.Etale.obj (V i) ≅ 𝒰.etalePrecoverageToEtale i :=
    p.Etale.objObjPreimageIso _
  have hinv (i : 𝒰.I₀) : (e i).inv.left ≫ pullback.snd (V i).hom p = 𝒰.f i :=
    MorphismProperty.Over.w (e i).inv
  let 𝒱 : Cover.{u} etalePrecoverage X :=
    { I₀ := 𝒰.I₀
      X i := (V i).left
      f i := (V i).hom
      mem₀ := by
        refine (presieve₀_mem_precoverage_iff _).mpr ⟨fun x => ?_, fun i => (V i).prop⟩
        obtain ⟨y, rfl⟩ := p.surjective x
        obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
        refine ⟨i, (pullback.fst (V i).hom p) ((e i).inv.left y'), ?_⟩
        change ((e i).inv.left ≫ pullback.fst (V i).hom p ≫ (V i).hom) y' =
          (𝒰.f i ≫ p) y'
        rw [pullback.condition, ← Category.assoc, hinv]
        rfl }
  refine ⟨𝒱, fun i => ?_⟩
  apply (constant_over_iff (𝒱.etalePrecoverageToEtale i) F).mpr
  change ((etaleSetPullback (V i).hom).obj F).IsConstant (V i).left.smallEtaleTopology
  have h₁ : ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F)).IsConstant
      (𝒰.X i).smallEtaleTopology :=
    (constant_over_iff (𝒰.etalePrecoverageToEtale i) _).mp (h𝒰 i)
  change ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F)).IsConstant
    (𝒰.etalePrecoverageToEtale i).left.smallEtaleTopology at h₁
  let := h₁
  have h₂ : ((etaleSetPullback (e i).hom.left).obj
      ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F))).IsConstant
      (pullback (V i).hom p).smallEtaleTopology := constant_pullback (e i).hom.left _
  change ((etaleSetPullback (e i).hom.left).obj
    ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F))).IsConstant
    (p.Etale.obj (V i)).left.smallEtaleTopology at h₂
  let := h₂
  have hsnd : pullback.snd (V i).hom p = (e i).hom.left ≫ 𝒰.f i :=
    (MorphismProperty.Over.w (e i).hom).symm
  let e' : (etaleSetPullback (pullback.fst (V i).hom p)).obj
      ((etaleSetPullback (V i).hom).obj F) ≅
      (etaleSetPullback (e i).hom.left).obj
        ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F)) :=
    (c X (V i).left (pullback (V i).hom p) (V i).hom
      (pullback.fst (V i).hom p)).app F ≪≫
      eqToIso (congrArg (fun m => (etaleSetPullback m).obj F) pullback.condition) ≪≫
      ((c X Y (pullback (V i).hom p) p (pullback.snd (V i).hom p)).app F).symm ≪≫
      eqToIso (congrArg (fun m => (etaleSetPullback m).obj
        ((etaleSetPullback p).obj F)) hsnd) ≪≫
      ((c Y (𝒰.X i) (pullback (V i).hom p) (𝒰.f i) (e i).hom.left).app
        ((etaleSetPullback p).obj F)).symm
  have : ((etaleSetPullback (e i).hom.left).obj
      ((etaleSetPullback (𝒰.f i)).obj ((etaleSetPullback p).obj F))).IsConstant
      (pullback (V i).hom p).smallEtaleTopology := by
    change _ at h₂
    exact h₂
  exact constant_descend (pullback.fst (V i).hom p)
    ((etaleSetPullback (V i).hom).obj F) (Sheaf.isConstant_congr _ e'.symm)

open CategoryTheory.Limits Opposite in
/-- Transport a trivializing cover along an isomorphism of sheaves. -/
private theorem locallyConstant_of_iso {Z : Scheme.{u}}
    {F G : Sheaf Z.smallEtaleTopology (Type (u + 1))} (e : F ≅ G)
    (hF : IsLocallyConstantEtaleSheafOfSets F) :
    IsLocallyConstantEtaleSheafOfSets G := by
  obtain ⟨𝒰, h𝒰⟩ := hF
  refine ⟨𝒰, fun i => ?_⟩
  have := h𝒰 i
  exact Sheaf.isConstant_congr _
    ((Z.smallEtaleTopology.overPullback (Type (u + 1))
      (𝒰.etalePrecoverageToEtale i)).mapIso e)

/-- Finite local constancy on a stratification passes to every refinement.
Source: Stacks Project, Tags 095A, 03Q1 (3), and 03SI; compare the abelian-coefficient
argument in `WeilConjectures.ConstructibleSheaf.Refinement`.

Proof: fix i and choose k with T.stratum i contained in S.stratum k. Write
Z = T.domain i, W = S.domain k, a = T.immersion i, and b = S.immersion k.
Form P = Z times_X W with projections p to Z and q to W. The image containment makes
p surjective. It is an immersion by base change of b, hence a surjective closed
immersion and a universal homeomorphism. This avoids assuming that a factors through b,
which need not follow from containment of their underlying images.
Pull back the finite locally constant sheaf b^*F along q. A pulled-back trivializing
etale cover is still a cover and inverse image preserves constant sheaves (095A);
the stalk at each geometric point is the original stalk at its image (03Q1 (3)),
so it remains finite. Composition of inverse images and p followed by a = q followed
by b identify this sheaf with p^*(a^*F). The small etale sites of P and Z are equivalent
under p (03SI). Descend a trivializing cover and its constant-sheaf isomorphisms through
this equivalence; coverings and constant objects correspond, so a^*F is locally constant.
Every geometric point of Z lifts uniquely to P because p is a surjective closed immersion
and fields kill its defining ideal. The stalk comparison therefore also shows that all
geometric stalks of a^*F are finite. This proves the assertion for each i.
(blueprint: lem-weil-pbc-refinement-preserves-finite-lisse)
-/
theorem refinement_preserves_finite_lisse
    (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (T S : Stratification X) (hTS : T.Refines S)
    (hS : ∀ k : Fin S.n,
      IsFiniteLocallyConstantSheafOfTypes
        ((etaleSetPullback (S.immersion k)).obj F)) :
    ∀ i : Fin T.n,
      IsFiniteLocallyConstantSheafOfTypes
        ((etaleSetPullback (T.immersion i)).obj F) := by
  intro i
  obtain ⟨k, hk⟩ := hTS i
  let a := T.immersion i
  let b := S.immersion k
  have hrange : Set.range a ⊆ Set.range b := by
    simpa only [a, b, T.range_immersion, S.range_immersion] using hk
  have hp : Surjective (Limits.pullback.fst a b) :=
    surjective_pullback_fst_of_range_subset a b hrange
  have hclosed : IsClosedImmersion (Limits.pullback.fst a b) :=
    IsClosedImmersion.of_isImmersion_of_surjective (Limits.pullback.fst a b)
  have hq := etaleSetLocallyConstant_pullback (Limits.pullback.snd a b)
    ((etaleSetPullback b).obj F) (hS k).1
  obtain ⟨c, _⟩ := etaleSetInverseImageCompositionUnits.2.2
  let e : (etaleSetPullback (Limits.pullback.snd a b)).obj ((etaleSetPullback b).obj F) ≅
      (etaleSetPullback (Limits.pullback.fst a b)).obj ((etaleSetPullback a).obj F) :=
    (c X (S.domain k) (Limits.pullback a b) b (Limits.pullback.snd a b)).app F ≪≫
      eqToIso (congrArg (fun f => (etaleSetPullback f).obj F)
        (Limits.pullback.condition (f := a) (g := b)).symm) ≪≫
      ((c X (T.domain i) (Limits.pullback a b) a (Limits.pullback.fst a b)).app F).symm
  refine ⟨etaleSetLocallyConstant_descend (Limits.pullback.fst a b)
    ((etaleSetPullback a).obj F) (locallyConstant_of_iso e hq), ?_⟩
  refine isFiniteSheaf_of_finite_algClosed_stalks _ fun Ω _ _ s ↦ ?_
  obtain ⟨t, ht⟩ := exists_comp_eq_of_surjective (Limits.pullback.fst a b) s
  obtain ⟨cq, hcq, _⟩ := etaleSetInverseImageStalkGerm (S.domain k) (Limits.pullback a b)
    (Limits.pullback.snd a b) ((etaleSetPullback b).obj F) Ω t
  have hfinite := (hS k).finite_sheafFiber Ω (t ≫ Limits.pullback.snd a b)
  have hqfinite : Finite ((pointSmallEtale t).sheafFiber.obj
      ((etaleSetPullback (Limits.pullback.snd a b)).obj ((etaleSetPullback b).obj F))) :=
    Finite.of_injective cq hcq.1
  let es := (pointSmallEtale t).sheafFiber.mapIso e
  have hpfinite : Finite ((pointSmallEtale t).sheafFiber.obj
      ((etaleSetPullback (Limits.pullback.fst a b)).obj ((etaleSetPullback a).obj F))) :=
    Finite.of_injective es.inv (ConcreteCategory.bijective_of_isIso es.inv).1
  obtain ⟨cp, hcp, _⟩ := etaleSetInverseImageStalkGerm (T.domain i) (Limits.pullback a b)
    (Limits.pullback.fst a b) ((etaleSetPullback a).obj F) Ω t
  have hfinite' : Finite ((pointSmallEtale (t ≫ Limits.pullback.fst a b)).sheafFiber.obj
      ((etaleSetPullback a).obj F)) := Finite.of_surjective cp hcp.2
  simpa only [ht] using hfinite'

end AlgebraicGeometry.Scheme
