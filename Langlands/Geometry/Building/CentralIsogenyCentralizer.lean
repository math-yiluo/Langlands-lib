import Langlands.Geometry.Building.CentralIsogenyApartment
import Langlands.Geometry.Building.KPCentralizerCompatibility
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Actual centralizer maps and full V6 under central-isogeny pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits Langlands.Plancherel

namespace Langlands.GroupScheme.TorusCoverTransport

variable {B : Scheme.{u}} {C G : GroupScheme B} {S T : CommGroupScheme B}
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  (q : C ⟶ G) (t : S ⟶ T)
  [Flat (CommGroupScheme.groupHom t).hom.hom.left]
  [Surjective (CommGroupScheme.groupHom t).hom.hom.left]
  (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)

private abbrev flatSurjectiveProperty : MorphismProperty Scheme.{u} :=
  @Flat ⊓ @Surjective

set_option backward.isDefEq.respectTransparency false in
private theorem epi_whiskerLeft (U : Over B) :
    Epi (U ◁ (CommGroupScheme.groupHom t).hom.hom) := by
  have hp : flatSurjectiveProperty (U ◁ (CommGroupScheme.groupHom t).hom.hom).left := by
    exact MorphismProperty.pullbackMap (P := flatSurjectiveProperty)
      (by change flatSurjectiveProperty (𝟙 U.left); exact ⟨inferInstance, inferInstance⟩)
      ⟨inferInstance, inferInstance⟩
      (by simp) (Over.w (CommGroupScheme.groupHom t).hom.hom).symm
  obtain ⟨hf, hs⟩ := hp
  let : Flat (U ◁ (CommGroupScheme.groupHom t).hom.hom).left := hf
  let : Surjective (U ◁ (CommGroupScheme.groupHom t).hom.hom).left := hs
  have : Epi (U ◁ (CommGroupScheme.groupHom t).hom.hom).left :=
    Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

include h in
/-- A faithfully flat change of acting group preserves centralization of all test points. -/
theorem map_mem_torusCentralizer {U : Over B} {g : U ⟶ C.X}
    (hg : g ∈ (torusCentralizer i).carrier U) :
    g ≫ q.hom.hom ∈ (torusCentralizer j).carrier U := by
  rw [mem_torusCentralizer_iff_universal]
  have : Epi (U ◁ (CommGroupScheme.groupHom t).hom.hom) := epi_whiskerLeft t U
  change (fst U T.X ≫ g ≫ q.hom.hom) * (snd U T.X ≫ j.hom.hom) =
    (snd U T.X ≫ j.hom.hom) * (fst U T.X ≫ g ≫ q.hom.hom)
  apply (cancel_epi (U ◁ (CommGroupScheme.groupHom t).hom.hom)).mp
  have hc := congrArg (fun f : U ⊗ S.X ⟶ C.X => f ≫ q.hom.hom)
    (hg (U ⊗ S.X) (fst U S.X) (snd U S.X)).eq
  have hs := congrArg (fun f : S.toGrp ⟶ G => f.hom.hom) h
  simp only [Grp.comp_hom_hom] at hs
  simpa only [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_fst_assoc,
    whiskerLeft_snd_assoc, Grp.comp_hom_hom, Category.assoc, hs] using hc

end Langlands.GroupScheme.TorusCoverTransport

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {C G : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ C} {j : T.toGrp ⟶ G}
  (q : C ⟶ G) (t : S ⟶ T)
  (h : i ≫ q = CommGroupScheme.groupHom t ≫ j)
  (ht : IsIsogeny (CommGroupScheme.groupHom t))
  (CS : CentralizerDatum i) (CT : CentralizerDatum j)

include h ht in
/-- The range of the actual source centralizer maps into the actual target centralizer. -/
theorem range_centralizer_comp_le :
    SubgroupFunctor.range (CS.j ≫ q) ≤ torusCentralizer j := by
  let : Flat (CommGroupScheme.groupHom t).hom.hom.left := ht.2.1
  let : Surjective (CommGroupScheme.groupHom t).hom.hom.left := ht.2.2
  rintro U _ ⟨z, rfl⟩
  change (z ≫ CS.j.hom.hom) ≫ q.hom.hom ∈ (torusCentralizer j).carrier U
  exact TorusCoverTransport.map_mem_torusCentralizer q t h (by
    rw [← CS.isRepresentedBy.2]
    exact ⟨z, rfl⟩)

/-- The unique actual algebraic centralizer map induced by the supplied torus square. -/
def centralIsogenyCentralizerMap : CS.Z ⟶ CT.Z :=
  CT.isRepresentedBy.factorHom (CS.j ≫ q) (range_centralizer_comp_le q t h ht CS)

/-- The constructed centralizer map commutes with the actual ambient embeddings. -/
theorem centralIsogenyCentralizerMap_comp :
    centralIsogenyCentralizerMap q t h ht CS CT ≫ CT.j = CS.j ≫ q :=
  CT.isRepresentedBy.factorHom_comp _ _

/-- The constructed centralizer map extends the actual acting-torus map. -/
theorem centralIsogenyCentralizerMap_torus :
    CS.s ≫ centralIsogenyCentralizerMap q t h ht CS CT =
      CommGroupScheme.groupHom t ≫ CT.s := by
  apply CT.isRepresentedBy.hom_ext
  rw [Category.assoc, centralIsogenyCentralizerMap_comp, ← Category.assoc,
    CS.comp_eq, Category.assoc, CT.comp_eq, h]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Character-normalized translations are natural in any commuting torus-centralizer square. -/
theorem cocharacterMapReal_centralizerTranslation
    {ZS ZT : GroupScheme (Spec (CommRingCat.of F))}
    (s : S.toGrp ⟶ ZS) (r : ZS ⟶ ZT) (s' : T.toGrp ⟶ ZT)
    (hs : s ≫ r = CommGroupScheme.groupHom t ≫ s')
    (hS : Function.Bijective (Cartan.restrictionEvaluation s))
    (hT : Function.Bijective (Cartan.restrictionEvaluation s'))
    (z : rationalPoints ZS) :
    cocharacterMapReal t (centralizerTranslation s hS z).toAdd =
      (centralizerTranslation s' hT (rationalPoints.map r z)).toAdd := by
  apply hT.injective
  apply AddMonoidHom.ext
  intro χ
  change eval T (Cartan.characterRestriction s' χ)
      (cocharacterMapReal t (centralizerTranslation s hS z).toAdd) = _
  rw [eval_cocharacterMapReal]
  have hχ : t ≫ Cartan.characterRestriction s' χ =
      Cartan.characterRestriction s (characterRestrict r χ) := by
    change (CommGroupScheme.groupHom t ≫ s') ≫ _ = (s ≫ r) ≫ _
    rw [hs]
  rw [hχ, eval_centralizerTranslation, Cartan.restrictionEvaluation_apply,
    eval_centralizerTranslation, rationalCharacterValuation_characterRestrict]

/-- Full translation-vector naturality for the constructed actual centralizer map. -/
theorem centralIsogenyCentralizerMap_translation (z : rationalPoints CS.Z) :
    cocharacterMapReal t (CS.translation z).toAdd =
      (CT.translation (rationalPoints.map
        (centralIsogenyCentralizerMap q t h ht CS CT) z)).toAdd :=
  cocharacterMapReal_centralizerTranslation t CS.s _ CT.s
    (centralIsogenyCentralizerMap_torus q t h ht CS CT) CS.bijective CT.bijective z

section FullV6

variable [IsAffineHom C.X.hom] [IsAffineHom G.X.hom]
  [LocallyOfFiniteType C.X.hom] [LocallyOfFiniteType G.X.hom]
  (hq : IsCentralIsogeny q)
  (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom C.X.hom] [LocallyOfFiniteType C.X.hom] in
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
    {φ : RootFunctionFamily T G} (hφ : IsCentralizerCompatible j CT.j CT.s CT.bijective φ) :
    IsCentralizerCompatible i CS.j CS.s CS.bijective
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
  have heval : eval S (t ≫ a'.val) (CS.translation z).toAdd =
      eval T a'.val (CT.translation
        (rationalPoints.map (centralIsogenyCentralizerMap q t h ht CS CT) z)).toAdd := by
    rw [← centralIsogenyCentralizerMap_translation q t h ht CS CT z,
      eval_cocharacterMapReal]
  rw [RootFunctionFamily.centralIsogenyPullback_apply_root q hq hS hT t h ht φ a' _ hcg,
    RootFunctionFamily.centralIsogenyPullback_apply_root q hq hS hT t h ht φ a' g hg,
    map_mul, map_mul, map_inv, hz, heval]
  exact hφ a'.val a'.property _ _
    (centralIsogenyRootGroupPointsEquiv q hq hS t h ht a' ⟨g, hg⟩).property

namespace KPApartmentData

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

/-- Full omega-compatibility of the whole actual apartment class pulls back. -/
theorem IsOmegaCompatible.centralIsogenyPullback
    {D : KPApartmentData j (localFieldOrder F)} (hD : D.IsOmegaCompatible CT) :
    (D.centralIsogenyPullback q hq hS hT t h ht).IsOmegaCompatible CS := by
  rintro ψ ⟨φ, hφ, rfl⟩
  exact (hD φ hφ).centralIsogenyPullback q t h ht CS CT hq hS hT

end KPApartmentData

end FullV6

end Langlands.Geometry.Building
