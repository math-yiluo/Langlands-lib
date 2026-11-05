import Langlands.Geometry.Building.IwahoriWeyl

/-! # Parahorics without relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- With no relative roots the sharp fixer has no generators, for every subset. -/
theorem sharpFixer_eq_bot_of_relativeRoots_eq_empty
    (hΦ : relativeRoots i = ∅) (Ω : Set D.Apartment) :
    D.sharpFixer Ω = ⊥ := by
  haveI : IsEmpty (relativeRoots i) := Set.isEmpty_coe_sort.2 hΦ
  simp [sharpFixer]

end KPApartmentData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Without relative roots every full parahoric is the actual centralizer-zero image. -/
theorem parahoric_eq_centralizerZeroImage_of_relativeRoots_eq_empty
    (hΦ : relativeRoots P.i = ∅) (Ω : Set P.Apartment) :
    P.parahoric Ω = P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  change _ ⊔ P.apartment.sharpFixer Ω = _
  rw [P.apartment.sharpFixer_eq_bot_of_relativeRoots_eq_empty hΦ Ω, sup_bot_eq]

/-- The root-free parahoric and centralizer-zero image have the same ambient point. -/
def parahoricEquivCentralizerZeroImage_of_relativeRoots_eq_empty
    (hΦ : relativeRoots P.i = ∅) (Ω : Set P.Apartment) :
    P.parahoric Ω ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  MulEquiv.subgroupCongr
    (P.parahoric_eq_centralizerZeroImage_of_relativeRoots_eq_empty hΦ Ω)

@[simp]
theorem parahoricEquivCentralizerZeroImage_of_relativeRoots_eq_empty_apply_coe
    (hΦ : relativeRoots P.i = ∅) (Ω : Set P.Apartment) (g : P.parahoric Ω) :
    ((P.parahoricEquivCentralizerZeroImage_of_relativeRoots_eq_empty hΦ Ω g :
      P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = g :=
  rfl

/-- The restricted-normalizer intersection is already constant without relative roots. -/
theorem iInf_parahoric_normalizerZeroComponent_eq_of_relativeRoots_eq_empty
    (hΦ : relativeRoots P.i = ∅) (C : Set P.Apartment) :
    (⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  simp_rw [P.parahoric_eq_centralizerZeroImage_of_relativeRoots_eq_empty hΦ]
  exact iInf_const

/-- The root-free case of the chamber-conjugate intersection uses only the identity
normalizer. No chamber or apartment-axiom premise is needed. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_of_relativeRoots_eq_empty
    (hΦ : relativeRoots P.i = ∅) {C : Set P.Apartment} {g : rationalPoints G}
    (hg : ∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      g ∈ P.parahoric (n • C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  have hbase := hg 1 P.zeroSubgroup.one_mem
  simpa only [one_smul,
    P.parahoric_eq_centralizerZeroImage_of_relativeRoots_eq_empty hΦ] using hbase

/-- In particular every parahoric of an anisotropic group is its centralizer-zero image. -/
theorem parahoric_eq_centralizerZeroImage_of_isAnisotropic
    (hG : IsAnisotropic G) (Ω : Set P.Apartment) :
    P.parahoric Ω = P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.parahoric_eq_centralizerZeroImage_of_relativeRoots_eq_empty
    (hG.relativeRoots_eq_empty P.isMaximalSplitTorus.isSplitSubtorus) Ω

end ParahoricBuildingData

end Langlands.Geometry.Building
