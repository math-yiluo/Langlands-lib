import Langlands.Geometry.Building.DerivedApartment
import Langlands.Geometry.Building.CentralIsogenyCentralizer

/-! # Actual centralizer transport and full V6 through a derived inclusion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.BruhatTits Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F]
    {T A S : CommGroupScheme (Spec (CommRingCat.of F))}
    {D G : GroupScheme (Spec (CommRingCat.of F))}
    (e : T ⟶ S) (c : A ⟶ S) (j : T.toGrp ⟶ D) (i : S.toGrp ⟶ G)
    (d : D ⟶ G)
    (h : j ≫ d = CommGroupScheme.groupHom e ≫ i)
    (hT : IsSplitTorus T.toGrp) (hA : IsSplitTorus A.toGrp)
    [hpflat : Flat (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    [hpsurj : Surjective (RelativeRoot.centralComplementProduct e c).hom.hom.left]
    (hc : IsCentral (CommGroupScheme.groupHom c ≫ i))

private abbrev productTorus : CommGroupScheme (Spec (CommRingCat.of F)) where
  toGrp := T.toGrp ⊗ A.toGrp
  comm := (hT.tensor hA).isCommMonObj

include hpflat hpsurj h hT hA hc in
/-- Centralizing the retained torus implies centralizing the full ambient
torus after the original point map, on every test scheme. -/
theorem derived_map_mem_torusCentralizer {U : Over (Spec (CommRingCat.of F))}
    {g : U ⟶ D.X} (hg : g ∈ (torusCentralizer j).carrier U) :
    g ≫ d.hom.hom ∈ (torusCentralizer i).carrier U := by
  let P := productTorus hT hA
  let p : P ⟶ S := Additive.ofMul (RelativeRoot.centralComplementProduct e c)
  have : Flat (CommGroupScheme.groupHom p).hom.hom.left := hpflat
  have : Surjective (CommGroupScheme.groupHom p).hom.hom.left := hpsurj
  have hmem : g ≫ d.hom.hom ∈
      (torusCentralizer (CommGroupScheme.groupHom p ≫ i)).carrier U := by
    intro V b x
    let xT := x ≫ (fst T.toGrp A.toGrp).hom.hom
    let xA := x ≫ (snd T.toGrp A.toGrp).hom.hom
    have hret : Commute (b ≫ g ≫ d.hom.hom)
        (xT ≫ (CommGroupScheme.groupHom e ≫ i).hom.hom) := by
      have hh := congrArg (fun f => f ≫ d.hom.hom) (hg V b xT).eq
      have hs := congrArg (fun f : T.toGrp ⟶ G => f.hom.hom) h
      simp only [Grp.comp_hom_hom] at hs
      exact (commute_iff_eq _ _).mpr (by
        simpa only [MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc, hs] using hh)
    have hcen : Commute (b ≫ g ≫ d.hom.hom)
        (xA ≫ (CommGroupScheme.groupHom c ≫ i).hom.hom) :=
      (commute_of_mem_center (hc V xA) (b ≫ g ≫ d.hom.hom)).symm
    have hprod : x ≫ (CommGroupScheme.groupHom p ≫ i).hom.hom =
        (xT ≫ (CommGroupScheme.groupHom e ≫ i).hom.hom) *
          (xA ≫ (CommGroupScheme.groupHom c ≫ i).hom.hom) := by
      change (x ≫ (RelativeRoot.centralComplementProduct e c).hom.hom) ≫ i.hom.hom = _
      simp only [RelativeRoot.centralComplementProduct, comp_prodHom,
        MonObj.mul_comp, Grp.comp_hom_hom, Category.assoc, xT, xA,
        productPointsEquiv_fst, productPointsEquiv_snd, Grp.fst_hom_hom, Grp.snd_hom_hom]
    rw [hprod]
    exact hret.mul_right hcen
  have hm := TorusCoverTransport.map_mem_torusCentralizer (j := i) (𝟙 G) p (by simp) hmem
  simpa using hm

variable (CS : CentralizerDatum j) (CT : CentralizerDatum i)

include h hT hA hc hpflat hpsurj in
/-- The actual source centralizer maps into the actual ambient centralizer. -/
theorem range_derived_centralizer_comp_le :
    SubgroupFunctor.range (CS.j ≫ d) ≤ torusCentralizer i := by
  rintro U _ ⟨z, rfl⟩
  change (z ≫ CS.j.hom.hom) ≫ d.hom.hom ∈ (torusCentralizer i).carrier U
  exact derived_map_mem_torusCentralizer e c j i d h hT hA hc (by
    rw [← CS.isRepresentedBy.2]
    exact ⟨z, rfl⟩)

/-- The unique original algebraic centralizer map induced by the retained
and central torus product. -/
def derivedCentralizerMap : CS.Z ⟶ CT.Z :=
  CT.isRepresentedBy.factorHom (CS.j ≫ d)
    (range_derived_centralizer_comp_le e c j i d h hT hA hc CS)

/-- The actual centralizer map commutes with the original ambient maps. -/
theorem derivedCentralizerMap_comp :
    derivedCentralizerMap e c j i d h hT hA hc CS CT ≫ CT.j = CS.j ≫ d :=
  CT.isRepresentedBy.factorHom_comp _ _

/-- The constructed centralizer map extends the original retained-torus
homomorphism. -/
theorem derivedCentralizerMap_torus :
    CS.s ≫ derivedCentralizerMap e c j i d h hT hA hc CS CT =
      CommGroupScheme.groupHom e ≫ CT.s := by
  apply CT.isRepresentedBy.hom_ext
  rw [Category.assoc, derivedCentralizerMap_comp, ← Category.assoc,
    CS.comp_eq, Category.assoc, CT.comp_eq, h]

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The original character-normalized translation vectors commute with
the constructed algebraic centralizer map. -/
theorem derivedCentralizerMap_translation (z : rationalPoints CS.Z) :
    cocharacterMapReal e (CS.translation z).toAdd =
      (CT.translation (rationalPoints.map
        (derivedCentralizerMap e c j i d h hT hA hc CS CT) z)).toAdd :=
  cocharacterMapReal_centralizerTranslation e CS.s _ CT.s
    (derivedCentralizerMap_torus e c j i d h hT hA hc CS CT) CS.bijective CT.bijective z

section FullV6

variable [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom]
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (hd : IsDerivedSubgroup d) (hS : IsSplitTorus S.toGrp)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom D.X.hom] [LocallyOfFiniteType D.X.hom] in
private theorem centralizer_conj_mem_rootGroupPoints (a : characterLattice T)
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
    {φ : RootFunctionFamily S G} (hφ : IsCentralizerCompatible i CT.j CT.s CT.bijective φ) :
    IsCentralizerCompatible j CS.j CS.s CS.bijective
      (RootFunctionFamily.derivedPullback e c j i d hd h hT hS hA hc φ) := by
  intro a ha z g hg
  obtain ⟨a', he⟩ :=
    (RelativeRoot.derivedRelativeRootEquiv e c j i d hd h hT hS hA hc).surjective ⟨a, ha⟩
  have he' : e ≫ a'.val = a := congrArg Subtype.val he
  subst a
  have hcg := centralizer_conj_mem_rootGroupPoints j (e ≫ a'.val)
    (rationalPoints.map CS.j z) g (map_mem_centralizerPoints CS.isRepresentedBy z) hg
  have hz : rationalPoints.map d (rationalPoints.map CS.j z) =
      rationalPoints.map CT.j
        (rationalPoints.map (derivedCentralizerMap e c j i d h hT hA hc CS CT) z) := by
    simpa only [rationalPoints.map_apply, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun m : CS.Z ⟶ G => z ≫ m.hom.hom)
        (derivedCentralizerMap_comp e c j i d h hT hA hc CS CT).symm
  have heval : eval T (e ≫ a'.val) (CS.translation z).toAdd =
      eval S a'.val (CT.translation
        (rationalPoints.map (derivedCentralizerMap e c j i d h hT hA hc CS CT) z)).toAdd := by
    rw [← derivedCentralizerMap_translation e c j i d h hT hA hc CS CT z,
      eval_cocharacterMapReal]
  rw [RootFunctionFamily.derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a' _ hcg,
    RootFunctionFamily.derivedPullback_apply_root e c j i d hd h hT hS hA hc φ a' g hg,
    map_mul, map_mul, map_inv, hz, heval]
  exact hφ a'.val a'.property _ _
    (derivedRootGroupPointsEquiv e c j i d hd h hT hS hA hc a' ⟨g, hg⟩).property

namespace KPApartmentData

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left] (hi : IsMaximalSplitTorus i)

/-- The whole actual derived apartment class inherits full
omega-compatibility on the supplied actual source centralizer. -/
theorem IsOmegaCompatible.derivedPullback
    {P : KPApartmentData i (localFieldOrder F)} (hP : P.IsOmegaCompatible CT) :
    (P.derivedPullback e c j i d hd h hT hS hA hc hi).IsOmegaCompatible CS := by
  rintro ψ ⟨φ, hφ, rfl⟩
  exact (hP φ hφ).derivedPullback e c j i d h hT hA hc CS CT hd hS

end KPApartmentData

end FullV6

end Langlands.Geometry.Building
