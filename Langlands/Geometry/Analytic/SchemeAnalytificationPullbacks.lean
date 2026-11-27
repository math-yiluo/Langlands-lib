import Langlands.Geometry.Analytic.SchemeAnalytificationLocalizedFunctor
import Langlands.Geometry.Analytic.LocalizedOpenDomainPullbacks
import Langlands.Geometry.Analytic.AffineAnalytificationFibreProductProof
import Langlands.Geometry.Analytic.SpaceAnalytificationAffinePullbacks

/-! # Pullback preservation for the separated-scheme analytification -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Set
open SaturatedAtlasPresentation AffineAnalytification AffineSchemeAnalytification
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.AlgebraicSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Localized

variable {W X Y Z : Scheme.{u}}
  {sW : W ⟶ Spec (CommRingCat.of K)} {sX : X ⟶ Spec (CommRingCat.of K)}
  {sY : Y ⟶ Spec (CommRingCat.of K)} {sZ : Z ⟶ Spec (CommRingCat.of K)}
  [LocallyOfFiniteType sW] [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
  [IsSeparated sW] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ]
  {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

private theorem center_map_eq (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    (x : localizedSpaceFunctor.obj (object K sX)) :
    center K sZ (localizedSpaceFunctor.map (map K sX sZ f hf) x) = f (center K sX x) := by
  change center K sZ ((localizedSpaceFunctor.map (map K sX sZ f hf)).hom x) = _
  rw [underlying_map]
  exact ((MorphismCompatibility.compatibility K sX sZ f hf _
    (MorphismExistence.isAnalytificationMap_analytification K sX sZ f hf)).1 x)

omit [IsSeparated sX] in
private theorem chartDomain_open (U : X.affineOpens) : IsOpen (chartDomain K sX U).carrier := by
  rw [chartDomain_carrier]
  exact (U : X.Opens).isOpen.preimage (center K sX).continuous

private def domainMap (f : X ⟶ Z) (hf : f ≫ sZ = sX) {U : X.affineOpens} {V : Z.affineOpens}
    (h : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Z.Opens)) :
    domainObj (object K sX) (chartDomain K sX U) ⟶
      domainObj (object K sZ) (chartDomain K sZ V) :=
  (chartIso K sX U).inv ≫ affineMap K sX sZ f hf h ≫ (chartIso K sZ V).hom

omit [IsSeparated sX] [IsSeparated sZ] in
private theorem chartIso_domainMap (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    {U : X.affineOpens} {V : Z.affineOpens} (h : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Z.Opens)) :
    (chartIso K sX U).hom ≫ domainMap K f hf h =
      affineMap K sX sZ f hf h ≫ (chartIso K sZ V).hom :=
  Iso.hom_inv_id_assoc _ _

private theorem domainMap_fac (f : X ⟶ Z) (hf : f ≫ sZ = sX)
    {U : X.affineOpens} {V : Z.affineOpens} (h : (U : X.Opens) ≤ f ⁻¹ᵁ (V : Z.Opens)) :
    domainMap K f hf h ≫ domainι (object K sZ) (chartDomain K sZ V) =
      domainι (object K sX) (chartDomain K sX U) ≫ map K sX sZ f hf := by
  apply (cancel_epi (chartIso K sX U).hom).mp
  calc
    _ = ((chartIso K sX U).hom ≫ domainMap K f hf h) ≫
        domainι (object K sZ) (chartDomain K sZ V) := (Category.assoc _ _ _).symm
    _ = (affineMap K sX sZ f hf h ≫ (chartIso K sZ V).hom) ≫
        domainι (object K sZ) (chartDomain K sZ V) :=
          congrArg (· ≫ _) (chartIso_domainMap K f hf h)
    _ = affineMap K sX sZ f hf h ≫ chartInclusion K sZ V := Category.assoc _ _ _
    _ = chartInclusion K sX U ≫ map K sX sZ f hf := (chartInclusion_map K sX sZ f hf h).symm
    _ = _ := Category.assoc _ _ _

private structure AffinePullbackCharts (f : X ⟶ Z) (g : Y ⟶ Z) where
  left : X.affineOpens
  right : Y.affineOpens
  target : Z.affineOpens
  left_le : (left : X.Opens) ≤ f ⁻¹ᵁ (target : Z.Opens)
  right_le : (right : Y.Opens) ≤ g ⁻¹ᵁ (target : Z.Opens)

namespace AffinePullbackCharts

variable (c : AffinePullbackCharts f g) (h : IsPullback p q f g)

private def source : W.affineOpens := by
  let U : W.Opens := p ⁻¹ᵁ (c.left : X.Opens) ⊓ q ⁻¹ᵁ (c.right : Y.Opens)
  have : IsAffine ((c.left : X.Opens) : Scheme) := c.left.property
  have : IsAffine ((c.right : Y.Opens) : Scheme) := c.right.property
  have : IsAffine ((c.target : Z.Opens) : Scheme) := c.target.property
  exact ⟨U, IsAffine.of_isIso (Scheme.Hom.isPullback_resLE h c.right_le c.left_le rfl).isoPullback.hom⟩

omit [IsSeparated sW] [IsSeparated sX] [IsSeparated sY] [IsSeparated sZ] in
private theorem affine_isPullback (hp : p ≫ sX = sW) (hq : q ≫ sY = sW)
    (hf : f ≫ sZ = sX) (hg : g ≫ sZ = sY) :
    IsPullback (affineMap K sW sX p hp (U := c.source h) (V := c.left) inf_le_left)
      (affineMap K sW sY q hq (U := c.source h) (V := c.right) inf_le_right)
      (affineMap K sX sZ f hf c.left_le) (affineMap K sY sZ g hg c.right_le) := by
  apply SpaceAnalytification.affineTestPullbackPreservation_of_tensor
    affineAnalytificationFibreProduct affineAnalytificationLocalizedFunctoriality
  apply IsPullback.map
  apply IsPullback.of_map_of_faithful (F := Over.forget (Spec (CommRingCat.of K)))
  let U := c.source h
  let : IsAffine ((p ⁻¹ᵁ (c.left : X.Opens) ⊓ q ⁻¹ᵁ (c.right : Y.Opens) : W.Opens) : Scheme) :=
    U.property
  change IsPullback
    (Spec.map (p.resLE (c.left : X.Opens) (U : W.Opens) inf_le_left).appTop)
    (Spec.map (q.resLE (c.right : Y.Opens) (U : W.Opens) inf_le_right).appTop)
    (Spec.map (f.resLE (c.target : Z.Opens) (c.left : X.Opens) c.left_le).appTop)
    (Spec.map (g.resLE (c.target : Z.Opens) (c.right : Y.Opens) c.right_le).appTop)
  exact (Scheme.Hom.isPullback_resLE h c.right_le c.left_le rfl).of_iso
    (coordinateIso (structureMap sW U)) (coordinateIso (structureMap sX c.left))
    (coordinateIso (structureMap sY c.right)) (coordinateIso (structureMap sZ c.target))
    (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
    (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm

private def analytic (hp : p ≫ sX = sW) (hq : q ≫ sY = sW)
    (hf : f ≫ sZ = sX) (hg : g ≫ sZ = sY) :
    OpenPullbackChart (map K sW sX p hp) (map K sW sY q hq) (map K sX sZ f hf) (map K sY sZ g hg) where
  source := chartDomain K sW (c.source h)
  left := chartDomain K sX c.left
  right := chartDomain K sY c.right
  target := chartDomain K sZ c.target
  left_open := chartDomain_open K _
  right_open := chartDomain_open K _
  source_carrier := by
    rw [chartDomain_carrier, chartDomain_carrier, chartDomain_carrier]
    ext z
    change (p (center K sW z) ∈ (c.left : X.Opens) ∧ q (center K sW z) ∈ (c.right : Y.Opens)) ↔
      (center K sX (localizedSpaceFunctor.map (map K sW sX p hp) z) ∈ (c.left : X.Opens) ∧
        center K sY (localizedSpaceFunctor.map (map K sW sY q hq) z) ∈ (c.right : Y.Opens))
    have hpz := center_map_eq K p hp z
    have hqz := center_map_eq K q hq z
    exact ⟨fun hz => ⟨hpz.symm ▸ hz.1, hqz.symm ▸ hz.2⟩,
      fun hz => ⟨hpz ▸ hz.1, hqz ▸ hz.2⟩⟩
  fst := domainMap K p hp (U := c.source h) (V := c.left) inf_le_left
  snd := domainMap K q hq (U := c.source h) (V := c.right) inf_le_right
  leftMap := domainMap K f hf c.left_le
  rightMap := domainMap K g hg c.right_le
  fst_fac := domainMap_fac K p hp inf_le_left
  snd_fac := domainMap_fac K q hq inf_le_right
  left_fac := domainMap_fac K f hf c.left_le
  right_fac := domainMap_fac K g hg c.right_le
  isPullback := by
    refine (c.affine_isPullback K h hp hq hf hg).of_iso (chartIso K sW (c.source h))
      (chartIso K sX c.left) (chartIso K sY c.right) (chartIso K sZ c.target) ?_ ?_ ?_ ?_
    · exact (chartIso_domainMap K p hp inf_le_left).symm
    · exact (chartIso_domainMap K q hq inf_le_right).symm
    · exact (chartIso_domainMap K f hf c.left_le).symm
    · exact (chartIso_domainMap K g hg c.right_le).symm

end AffinePullbackCharts

/-- A pullback of separated schemes locally of finite type over the field analytifies
to a pullback of their actual glued analytic spaces. -/
private theorem map_isPullback (h : IsPullback p q f g) (hp : p ≫ sX = sW) (hq : q ≫ sY = sW)
    (hf : f ≫ sZ = sX) (hg : g ≫ sZ = sY)
    (hcomm : map K sW sX p hp ≫ map K sX sZ f hf = map K sW sY q hq ≫ map K sY sZ g hg) :
    IsPullback (map K sW sX p hp) (map K sW sY q hq) (map K sX sZ f hf) (map K sY sZ g hg) := by
  refine isPullback_of_openDomainCharts hcomm (fun c : AffinePullbackCharts f g =>
    c.analytic K h hp hq hf hg) ?_
  intro x y hxy
  have hz : f (center K sX x) = g (center K sY y) := by
    rw [← center_map_eq K f hf, ← center_map_eq K g hg, hxy]
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (center K sX x)) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (x := center K sX x) (U := f ⁻¹ᵁ V) hzV
  have hyV : center K sY y ∈ g ⁻¹ᵁ V := by
    change g (center K sY y) ∈ V
    rw [← hz]
    exact hzV
  obtain ⟨T, hT, hyT, hTV⟩ := exists_isAffineOpen_mem_and_subset
    (x := center K sY y) (U := g ⁻¹ᵁ V) hyV
  refine ⟨⟨⟨U, hU⟩, ⟨T, hT⟩, ⟨V, hV⟩, hUV, hTV⟩, ?_, ?_⟩
  · change x ∈ (chartDomain K sX ⟨U, hU⟩).carrier
    rwa [chartDomain_carrier]
  · change y ∈ (chartDomain K sY ⟨T, hT⟩).carrier
    rwa [chartDomain_carrier]

end Localized

/-- The functorial analytification sends any square which is a pullback on the underlying
schemes to a pullback in the localized analytic category. -/
theorem localizedAnalytification_map_isPullback
    {W X Y Z : (separatedLocallyFiniteTypeOver K).FullSubcategory}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    IsPullback ((localizedAnalytification K).map p) ((localizedAnalytification K).map q)
      ((localizedAnalytification K).map f) ((localizedAnalytification K).map g) := by
  let : LocallyOfFiniteType W.obj.hom := W.property.1
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : LocallyOfFiniteType Z.obj.hom := Z.property.1
  let : IsSeparated W.obj.hom := W.property.2
  let : IsSeparated X.obj.hom := X.property.2
  let : IsSeparated Y.obj.hom := Y.property.2
  let : IsSeparated Z.obj.hom := Z.property.2
  have hcomm : p ≫ f = q ≫ g := (separatedLocallyFiniteTypeOver K).ι.map_injective
    (Over.OverMorphism.ext h.w)
  have hcommAn : (localizedAnalytification K).map p ≫ (localizedAnalytification K).map f =
      (localizedAnalytification K).map q ≫ (localizedAnalytification K).map g := by
    simpa only [Functor.map_comp] using congrArg ((localizedAnalytification K).map) hcomm
  exact Localized.map_isPullback K h (Over.w p.hom) (Over.w q.hom) (Over.w f.hom) (Over.w g.hom) hcommAn

/-- The limit structure on the cone of analytified scheme projections. -/
def localizedAnalytificationPullbackIsLimit
    {W X Y Z : (separatedLocallyFiniteTypeOver K).FullSubcategory}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback p.hom.left q.hom.left f.hom.left g.hom.left) :
    IsLimit (localizedAnalytification_map_isPullback K h).cone :=
  (localizedAnalytification_map_isPullback K h).isLimit

end Langlands.Analytic.SchemeAnalytification
