import Langlands.Geometry.Building.IntegerCentralizer
import Langlands.Geometry.Building.DerivedCentralizer

/-! # Integer-valued full centralizer compatibility under cover pullback -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits
namespace Langlands.Geometry.Building.IntegerValuation

variable {F : Type u} [Field F]
  (v : Valuation F (WithZero (Multiplicative ℤ)))
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {C G : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  (q : C ⟶ G) (t : S ⟶ T)
  (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))
  (CS : CentralizerDatum i) (CT : CentralizerDatum j)

/-- Character-normalized translations are natural in any commuting torus-centralizer square. -/
theorem cocharacterMapReal_centralizerTranslation
    {ZS ZT : GroupScheme (Spec (CommRingCat.of F))}
    (s : S.toGrp ⟶ ZS) (r : ZS ⟶ ZT) (s' : T.toGrp ⟶ ZT)
    (hs : s ≫ r = CommGroupScheme.groupHom t ≫ s')
    (hS : Function.Bijective (Cartan.restrictionEvaluation s))
    (hT : Function.Bijective (Cartan.restrictionEvaluation s'))
    (z : rationalPoints ZS) :
    cocharacterMapReal t (centralizerTranslation v s hS z).toAdd =
      (centralizerTranslation v s' hT (rationalPoints.map r z)).toAdd := by
  apply hT.injective
  apply AddMonoidHom.ext
  intro χ
  change eval T (Cartan.characterRestriction s' χ)
      (cocharacterMapReal t (centralizerTranslation v s hS z).toAdd) = _
  rw [eval_cocharacterMapReal]
  have hχ : t ≫ Cartan.characterRestriction s' χ =
      Cartan.characterRestriction s (characterRestrict r χ) := by
    change (CommGroupScheme.groupHom t ≫ s') ≫ _ = (s ≫ r) ≫ _
    rw [hs]
  rw [hχ, eval_centralizerTranslation, Cartan.restrictionEvaluation_apply,
    eval_centralizerTranslation, rationalCharacterEval_characterRestrict]

/-- Full translation-vector naturality for the constructed actual centralizer map. -/
theorem centralIsogenyCentralizerMap_translation (z : rationalPoints CS.Z) :
    cocharacterMapReal t (centralizerTranslation v CS.s CS.bijective z).toAdd =
      (centralizerTranslation v CT.s CT.bijective (rationalPoints.map
        (centralIsogenyCentralizerMap q t h ht CS CT) z)).toAdd :=
  cocharacterMapReal_centralizerTranslation v t CS.s _ CT.s
    (centralIsogenyCentralizerMap_torus q t h ht CS CT) CS.bijective CT.bijective z

section FullV6

variable [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)

omit [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom] in
private theorem centralizer_conj_mem_rootGroupPoints (a : characterLattice S)
    (z g : rationalPoints C) (hz : z ∈ centralizerPoints i)
    (hg : g ∈ rootGroupPoints i a) :
    z⁻¹ * g * z ∈ rootGroupPoints i a := by
  have hc := RelativeRoot.comp_mem_subgroup i a (C.innerIso z⁻¹).hom hg
  rw [(mem_centralizerPoints i).mp ((centralizerPoints i).inv_mem hz)] at hc
  simpa only [rootGroupPoints, comp_innerIso_hom, GroupScheme.constantPoint_self,
    inv_inv] using hc

/-- The full actual-centralizer axiom V6 pulls back through the actual centralizer map. -/
theorem IsCentralizerCompatible.centralIsogenyPullback
    {φ : RootFunctionFamily T G} (hφ : IsCentralizerCompatible v j CT.j CT.s CT.bijective φ) :
    IsCentralizerCompatible v i CS.j CS.s CS.bijective
      (RootFunctionFamily.centralIsogenyPullback q hq hS hT t h ht φ) := by
  intro a ha z g hg
  obtain ⟨a', he⟩ :=
    (centralIsogenyRootPullbackEquiv q hq hS hT t h ht).surjective ⟨a, ha⟩
  have he' : t ≫ a'.val = a := congrArg Subtype.val he
  subst a
  have hcg := centralizer_conj_mem_rootGroupPoints (t ≫ a'.val)
    (rationalPoints.map CS.j z) g
    (map_mem_centralizerPoints CS.isRepresentedBy z) hg
  have hz : rationalPoints.map q (rationalPoints.map CS.j z) =
      rationalPoints.map CT.j
        (rationalPoints.map (centralIsogenyCentralizerMap q t h ht CS CT) z) := by
    simpa only [rationalPoints.map_apply, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun m : CS.Z ⟶ G => z ≫ m.hom.hom)
        (centralIsogenyCentralizerMap_comp q t h ht CS CT).symm
  have heval : eval S (t ≫ a'.val) (centralizerTranslation v CS.s CS.bijective z).toAdd =
      eval T a'.val (centralizerTranslation v CT.s CT.bijective
        (rationalPoints.map (centralIsogenyCentralizerMap q t h ht CS CT) z)).toAdd := by
    rw [← centralIsogenyCentralizerMap_translation v q t h ht CS CT z,
      eval_cocharacterMapReal]
  rw [RootFunctionFamily.centralIsogenyPullback_apply_root q hq hS hT t h ht φ a' _ hcg,
    RootFunctionFamily.centralIsogenyPullback_apply_root q hq hS hT t h ht φ a' g hg,
    map_mul, map_mul, map_inv, hz, heval]
  exact hφ a'.val a'.property _ _
    (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a' ⟨g, hg⟩).property

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

/-- Full omega-compatibility of the whole actual apartment class pulls back. -/
theorem IsOmegaCompatible.centralIsogenyPullback
    {D : KPApartmentData j (order v)} (hD : IsOmegaCompatible v D CT) :
    IsOmegaCompatible v (D.centralIsogenyPullback q hq hS hT t h ht) CS := by
  rintro ψ ⟨φ, hφ, rfl⟩
  exact (hD φ hφ).centralIsogenyPullback v q t h ht CS CT hq hS hT

end FullV6

end Langlands.Geometry.Building.IntegerValuation

namespace Langlands.Geometry.Building.IntegerValuation

variable {F : Type u} [Field F]
    (v : Valuation F (WithZero (Multiplicative ℤ)))
    {T A S : CommGroupScheme (Spec (CommRingCat.of F))}
    {D G : GroupScheme (Spec (CommRingCat.of F))}
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))


variable (CS : CentralizerDatum j) (CT : CentralizerDatum i)

/-- The original character-normalized translation vectors commute with
the constructed algebraic centralizer map. -/
theorem derivedCentralizerMap_translation (z : rationalPoints CS.Z) :
    cocharacterMapReal e (centralizerTranslation v CS.s CS.bijective z).toAdd =
      (centralizerTranslation v CT.s CT.bijective (rationalPoints.map
        (derivedCentralizerMap e c j i d h hT hA hc CS CT) z)).toAdd :=
  cocharacterMapReal_centralizerTranslation v e CS.s _ CT.s
    (derivedCentralizerMap_torus e c j i d h hT hA hc CS CT) CS.bijective CT.bijective z

section FullV6

variable [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hd : IsDerivedSubgroup d) (hS : IsSplitTorus S.toGrp)

omit [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
private theorem derived_centralizer_conj_mem_rootGroupPoints (a : characterLattice T)
    (z g : rationalPoints D) (hz : z ∈ centralizerPoints j)
    (hg : g ∈ rootGroupPoints j a) :
    z⁻¹ * g * z ∈ rootGroupPoints j a := by
  have hcg := RelativeRoot.comp_mem_subgroup j a (D.innerIso z⁻¹).hom hg
  rw [(mem_centralizerPoints j).mp ((centralizerPoints j).inv_mem hz)] at hcg
  simpa only [rootGroupPoints, comp_innerIso_hom, GroupScheme.constantPoint_self,
    inv_inv] using hcg

/-- Full V6 on the actual ambient centralizer pulls back to full V6 on the
actual source centralizer, with its character-normalized translations. -/
theorem IsCentralizerCompatible.derivedPullback
    {φ : RootFunctionFamily S G} (hφ : IsCentralizerCompatible v i CT.j CT.s CT.bijective φ) :
    IsCentralizerCompatible v j CS.j CS.s CS.bijective
      (RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc φ) := by
  intro a ha z g hg
  obtain ⟨a', he⟩ :=
    (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).surjective ⟨a, ha⟩
  have he' : e ≫ a'.val = a := congrArg Subtype.val he
  subst a
  have hcg := derived_centralizer_conj_mem_rootGroupPoints j (e ≫ a'.val)
    (rationalPoints.map CS.j z) g (map_mem_centralizerPoints CS.isRepresentedBy z) hg
  have hz : rationalPoints.map d (rationalPoints.map CS.j z) =
      rationalPoints.map CT.j
        (rationalPoints.map (derivedCentralizerMap e c j i d h hT hA hc CS CT) z) := by
    simpa only [rationalPoints.map_apply, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun m : CS.Z ⟶ G => z ≫ m.hom.hom)
        (derivedCentralizerMap_comp e c j i d h hT hA hc CS CT).symm
  have heval : eval T (e ≫ a'.val) (centralizerTranslation v CS.s CS.bijective z).toAdd =
      eval S a'.val (centralizerTranslation v CT.s CT.bijective
        (rationalPoints.map (derivedCentralizerMap e c j i d h hT hA hc CS CT) z)).toAdd := by
    rw [← derivedCentralizerMap_translation v e c j i d h hT hA hc CS CT z,
      eval_cocharacterMapReal]
  rw [RootFunctionFamily.derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a' _ hcg,
    RootFunctionFamily.derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a' g hg,
    map_mul, map_mul, map_inv, hz, heval]
  exact hφ a'.val a'.property _ _
    (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a' ⟨g, hg⟩).property

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left] (hi : IsMaximalSplitTorus i)

/-- The whole actual derived apartment class inherits full
omega-compatibility on the supplied actual source centralizer. -/
theorem IsOmegaCompatible.derivedPullback
    {P : KPApartmentData i (order v)} (hP : IsOmegaCompatible v P CT) :
    IsOmegaCompatible v (P.derivedPullback e c j i d hd h hT hS hA hc hi) CS := by
  rintro ψ ⟨φ, hφ, rfl⟩
  exact (hP φ hφ).derivedPullback v e c j i d h hT hA hc CS CT hd hS

end FullV6

end Langlands.Geometry.Building.IntegerValuation
