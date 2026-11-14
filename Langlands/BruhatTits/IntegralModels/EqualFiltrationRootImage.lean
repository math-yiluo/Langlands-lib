import Langlands.BruhatTits.IntegralModels.RootModelPresentationIso
import Langlands.GroupScheme.HomImage

/-! # Actual special-fibre root images at equal filtration subgroups -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels.RootFiltrationModelData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω : Kˣ → ℝ}
  {C : KPApartmentData i ω} {x : C.Apartment} {a : relativeRoots i} {r s : ℝ}
  (U : RootFiltrationModelData R K C x a r)
  (V : RootFiltrationModelData R K C x a s)
  (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K))
  (h : C.filtration x a r = C.filtration x a s)
  {N N' : IntegralModel R K G}
  (φ : U.model.Hom N U.inclusion) (φ' : V.model.Hom N' V.inclusion)
  (ψ : N'.Hom N (𝟙 G))

/-- The actual root-model isomorphism at equal filtration subgroups commutes
with the ambient model map, by generic rigidity. -/
theorem modelIsoOfFiltrationEq_hom_comp :
    (U.modelIsoOfFiltrationEq V hext h).iso.hom ≫ φ'.hom ≫ ψ.hom = φ.hom := by
  let e := U.modelIsoOfFiltrationEq V hext h
  change e.iso.hom ≫ φ'.hom ≫ ψ.hom = φ.hom
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono N.genericIso.hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [ψ.generic_comm, Category.comp_id, φ'.generic_comm,
    ← Category.assoc, e.generic_comm, Category.assoc,
    U.genericIso_hom_comp V, φ.generic_comm]

variable [IsLocalRing R]

local instance model_specialFibre_affine
    {H : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K H) :
    IsAffineHom M.specialFibre.X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd M.group.X.hom (IntegralModel.residueBaseMap R))
  infer_instance

local instance model_specialFibre_isAffine
    {H : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K H) :
    IsAffine M.specialFibre.X.left :=
  isAffine_of_isAffineHom M.specialFibre.X.hom

/-- A factor of the target root model's whole special fibre through the
actual schematic image of the ambient special-fibre map. -/
def specialFibreImageFactorOfFiltrationEq :
    U.model.specialFibre ⟶ SchematicImage.image ψ.specialFibreMap :=
  (U.modelIsoOfFiltrationEq V hext h).specialFibreIso.hom ≫
    φ'.specialFibreMap ≫ SchematicImage.projection ψ.specialFibreMap

/-- The factor recovers the original target root-model map on every test
scheme, rather than only on residue-field points. -/
@[reassoc]
theorem specialFibreImageFactorOfFiltrationEq_comp :
    U.specialFibreImageFactorOfFiltrationEq V hext h φ' ψ ≫
        SchematicImage.inclusion ψ.specialFibreMap = φ.specialFibreMap := by
  unfold specialFibreImageFactorOfFiltrationEq
  rw [Category.assoc, Category.assoc, SchematicImage.projection_inclusion]
  change
    (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
        (U.modelIsoOfFiltrationEq V hext h).iso.hom ≫
      (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map φ'.hom ≫
        (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ψ.hom =
      (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map φ.hom
  rw [← Functor.map_comp, ← Functor.map_comp,
    U.modelIsoOfFiltrationEq_hom_comp V hext h φ φ' ψ]

include V hext h φ' in
/-- The all-test image of the target integral root model's special fibre
lies in the actual ambient schematic image. -/
theorem range_specialFibreMap_le_image_of_filtration_eq :
    SubgroupFunctor.range φ.specialFibreMap ≤
      SubgroupFunctor.range (SchematicImage.inclusion ψ.specialFibreMap) := by
  rw [← U.specialFibreImageFactorOfFiltrationEq_comp V hext h φ φ' ψ]
  intro T z hz
  rw [SubgroupFunctor.mem_range] at hz ⊢
  rcases hz with ⟨w, rfl⟩
  exact ⟨w ≫ (U.specialFibreImageFactorOfFiltrationEq V hext h φ' ψ).hom.hom,
    by rw [Grp.comp_hom_hom, Category.assoc]⟩

section Unramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₀ : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G₀.X.hom] {B : MaximalUnramified.BuildingData F G₀}
  {y : B.Apartment} {b : relativeRoots B.i} {t t' : ℝ}
  (P : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
    B.apartment y b t)
  (Q : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
    B.apartment y b t')
  (heq : B.apartment.filtration y b t = B.apartment.filtration y b t')
  {M M' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G₀}
  (α : P.model.Hom M P.inclusion) (α' : Q.model.Hom M' Q.inclusion)
  (β : M'.Hom M (𝟙 G₀))

/-- Over the actual maximal-unramified integers, the root-image factor uses
the proved smooth homomorphism extension theorem. -/
def unramifiedSpecialFibreImageFactorOfFiltrationEq :
    P.model.specialFibre ⟶ SchematicImage.image β.specialFibreMap :=
  P.specialFibreImageFactorOfFiltrationEq Q
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    heq α' β

@[reassoc]
theorem unramifiedSpecialFibreImageFactorOfFiltrationEq_comp :
    P.unramifiedSpecialFibreImageFactorOfFiltrationEq Q heq α' β ≫
        SchematicImage.inclusion β.specialFibreMap = α.specialFibreMap :=
  P.specialFibreImageFactorOfFiltrationEq_comp Q
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    heq α α' β

include Q heq α' in
theorem unramifiedRange_specialFibreMap_le_image_of_filtration_eq :
    SubgroupFunctor.range α.specialFibreMap ≤
      SubgroupFunctor.range (SchematicImage.inclusion β.specialFibreMap) :=
  P.range_specialFibreMap_le_image_of_filtration_eq Q
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    heq α α' β

end Unramified

end Langlands.BruhatTits.IntegralModels.RootFiltrationModelData
