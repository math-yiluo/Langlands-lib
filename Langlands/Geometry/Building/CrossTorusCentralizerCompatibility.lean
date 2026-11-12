import Langlands.Geometry.Building.ValuationBuildingIsoTransport
import Langlands.Geometry.Building.CrossTorusBuildingComparison

/-! # Full centralizer compatibility under based group isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace CentralizerDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
    (C : CentralizerDatum i) (E : CentralizerDatum j)
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

/-- The canonical comparison of the actual centralizer representatives
through a simultaneous torus and ambient isomorphism. -/
def basedComparisonIso : C.Z ≅ E.Z :=
  (C.isRepresentedBy.torusCentralizer_of_iso_square
    { hom := CommGroupScheme.groupHom e.hom
      inv := CommGroupScheme.groupHom e.inv
      hom_inv_id := congrArg CommGroupScheme.groupHom e.hom_inv_id
      inv_hom_id := congrArg CommGroupScheme.groupHom e.inv_hom_id } f h).isoOfIsRepresentedBy
    E.isRepresentedBy

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The comparison uses the given actual ambient isomorphism. -/
theorem basedComparisonIso_hom_comp :
    (C.basedComparisonIso E e f h).hom ≫ E.j = C.j ≫ f.hom :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ E.isRepresentedBy

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The same comparison commutes with the given torus isomorphism. -/
theorem basedComparisonIso_torus :
    C.s ≫ (C.basedComparisonIso E e f h).hom =
      CommGroupScheme.groupHom e.hom ≫ E.s := by
  apply E.isRepresentedBy.hom_ext
  rw [Category.assoc, basedComparisonIso_hom_comp, ← Category.assoc, C.comp_eq,
    Category.assoc, E.comp_eq, h]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Character restriction commutes with the actual centralizer and torus
comparisons, including their contravariant character directions. -/
theorem basedComparisonIso_characterRestriction (chi : rationalCharacters E.Z) :
    characterLattice.congr e
      (BruhatTits.Cartan.characterRestriction C.s
        (characterRestrict (C.basedComparisonIso E e f h).hom chi)) =
      BruhatTits.Cartan.characterRestriction E.s chi := by
  change CommGroupScheme.groupHom e.inv ≫
      (C.s ≫ (C.basedComparisonIso E e f h).hom) ≫ chi.toMul = E.s ≫ chi.toMul
  rw [basedComparisonIso_torus]
  change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ E.s ≫ chi.toMul = _
  rw [Iso.inv_hom_id]
  rfl

/-- The character-normalized centralizer translation commutes with the
actual torus cocharacter map. -/
theorem basedComparisonIso_translation (z : rationalPoints C.Z) :
    cocharacterRealCongr e (C.translation z).toAdd =
      (E.translation (rationalPoints.map (C.basedComparisonIso E e f h).hom z)).toAdd := by
  apply E.bijective.injective
  apply AddMonoidHom.ext
  intro chi
  change eval S' (BruhatTits.Cartan.characterRestriction E.s chi)
      (cocharacterRealCongr e (C.translation z).toAdd) =
    eval S' (BruhatTits.Cartan.characterRestriction E.s chi)
      (E.translation (rationalPoints.map (C.basedComparisonIso E e f h).hom z)).toAdd
  conv_lhs =>
    rw [← C.basedComparisonIso_characterRestriction E e f h chi, eval_cocharacterRealCongr]
  rw [eval_centralizerTranslation, eval_centralizerTranslation,
    rationalCharacterValuation_characterRestrict]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The comparison's map on centralizer points is the original ambient
point map after the original inclusion. -/
theorem basedComparisonIso_map_comp (z : rationalPoints C.Z) :
    rationalPoints.map E.j
        (rationalPoints.map (C.basedComparisonIso E e f h).hom z) =
      rationalPoints.map f.hom (rationalPoints.map C.j z) := by
  simpa only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun a : C.Z ⟶ H => z ≫ a.hom.hom)
      (C.basedComparisonIso_hom_comp E e f h)

end CentralizerDatum

section Compatibility

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S S' : CommGroupScheme (Spec (CommRingCat.of F))}
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}
    (C : CentralizerDatum i) (E : CentralizerDatum j)
    (e : S ≅ S') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include h in
/-- Full V6 is preserved through the simultaneous isomorphism of the
torus and ambient group, for any actual target centralizer representative. -/
theorem IsCentralizerCompatible.transport_basedIso
    {phi : RootFunctionFamily S G}
    (hphi : IsCentralizerCompatible i C.j C.s C.bijective phi) :
    IsCentralizerCompatible j E.j E.s E.bijective
      (RootFunctionFamily.transportEquiv e f phi) := by
  intro a ha z v hv
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
  have ha' := (roots_mem_of_transport_iff e f h a).mp ha
  obtain ⟨z, rfl⟩ := (isoPointsEquiv (C.basedComparisonIso E e f h)
    (Over.mk (𝟙 _))).surjective z
  obtain ⟨v, rfl⟩ := (isoPointsEquiv f (Over.mk (𝟙 _))).surjective v
  have hv' : v ∈ rootGroupPoints i a := by
    apply (rootGroupPoints_transport_iff e f h a v).mp
    exact hv
  change RootFunctionFamily.transportEquiv e f phi (characterLattice.congr e a)
      ((rationalPoints.map E.j
        (rationalPoints.map (C.basedComparisonIso E e f h).hom z))⁻¹ *
        rationalPoints.map f.hom v *
        rationalPoints.map E.j
          (rationalPoints.map (C.basedComparisonIso E e f h).hom z)) =
    RootFunctionFamily.transportEquiv e f phi (characterLattice.congr e a)
      (rationalPoints.map f.hom v) +
    ((eval S' (characterLattice.congr e a)
      (E.translation (rationalPoints.map (C.basedComparisonIso E e f h).hom z)).toAdd : ℝ) :
        WithTop ℝ)
  rw [C.basedComparisonIso_map_comp E e f h z, ← map_inv, ← map_mul, ← map_mul,
    RootFunctionFamily.transportEquiv_apply_map, RootFunctionFamily.transportEquiv_apply_map]
  rw [← C.basedComparisonIso_translation E e f h z, eval_cocharacterRealCongr]
  exact hphi a ha' z v hv'

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

/-- The original transported apartment class satisfies full V6 with the
given target centralizer. -/
theorem KPApartmentData.IsOmegaCompatible.transport_basedIso
    {D : KPApartmentData i (localFieldOrder F)} (hD : D.IsOmegaCompatible C) :
    (D.transport e f h).IsOmegaCompatible E := by
  rintro _ ⟨phi, hphi, rfl⟩
  exact (hD phi hphi).transport_basedIso C E e f h

end Compatibility

end Langlands.Geometry.Building
