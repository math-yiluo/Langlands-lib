import Langlands.BruhatTits.IntegralModels.RootFiltrationModel
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.IntegralModel.SemilinearExtension

/-! # Comparisons of supplied root-filtration models -/

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

/-- Canonical generic isomorphism between two representatives of the same
actual all-test root subgroup, at possibly different depths. -/
def genericIso : U.rootGroup ≅ V.rootGroup :=
  U.isRootSubgroup.isoOfIsRepresentedBy V.isRootSubgroup

theorem genericIso_hom_comp : (U.genericIso V).hom ≫ V.inclusion = U.inclusion :=
  U.isRootSubgroup.isoOfIsRepresentedBy_hom_comp V.isRootSubgroup

/-- A depth comparison preserves the exact integral-point images under any
generic map compatible with the actual root inclusions. -/
theorem map_mem_integralPoints_of_depth_le (hrs : r ≤ s)
    (f : V.rootGroup ⟶ U.rootGroup) (hf : f ≫ U.inclusion = V.inclusion)
    {g : rationalPoints V.rootGroup} (hg : g ∈ V.model.integralPoints) :
    rationalPoints.map f g ∈ U.model.integralPoints := by
  have hg' : rationalPoints.map V.inclusion g ∈ C.filtration x a s := by
    rw [← V.integralPoints_eq]
    exact ⟨g, hg, rfl⟩
  have hg'' := C.filtration_antitone x a hrs hg'
  rw [← U.integralPoints_eq] at hg''
  obtain ⟨h, hh, hinc⟩ := hg''
  have hm : Mono U.inclusion.hom.hom := U.isRootSubgroup.1
  have heq : h = rationalPoints.map f g := by
    apply hm.right_cancellation
    change rationalPoints.map U.inclusion h =
      rationalPoints.map U.inclusion (rationalPoints.map f g)
    rw [hinc]
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, hf]
  exact heq ▸ hh

/-- A model comparison from the deeper depth to the shallower depth,
conditional on the explicit homomorphism-extension criterion for the base. -/
def comparisonHom (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K))
    (hrs : r ≤ s) : V.model.Hom U.model (V.genericIso U).hom :=
  Classical.choice (hext V.rootGroup U.rootGroup (V.genericIso U).hom
    V.model U.model V.smooth
    (fun _ hg => U.map_mem_integralPoints_of_depth_le V hrs _
      (V.genericIso_hom_comp U) hg))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison commutes with any compatible maps into ambient models
whose comparison extends the generic identity. -/
theorem comparisonHom_comp
    (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K)) (hrs : r ≤ s)
    {N N' : IntegralModel R K G}
    (φ : U.model.Hom N U.inclusion) (φ' : V.model.Hom N' V.inclusion)
    (ψ : N'.Hom N (𝟙 G)) :
    (U.comparisonHom V hext hrs).hom ≫ φ.hom = φ'.hom ≫ ψ.hom := by
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono N.genericIso.hom).mp
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    φ.generic_comm, ψ.generic_comm, Category.comp_id]
  rw [← Category.assoc, (U.comparisonHom V hext hrs).generic_comm,
    Category.assoc, V.genericIso_hom_comp U, ← φ'.generic_comm]

end Langlands.BruhatTits.IntegralModels.RootFiltrationModelData
