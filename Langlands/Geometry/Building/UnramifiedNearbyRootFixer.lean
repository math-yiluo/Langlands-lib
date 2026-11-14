import Langlands.Geometry.Building.NearbyRootFixer
import Langlands.Geometry.Building.UnramifiedApartmentModelInput
import Langlands.Geometry.Building.UnramifiedRootTranslationPositivity

/-! # Nearby root fixers along actual descended translation lines -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter
open scoped CategoryTheory.MonObj Topology ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace KPApartmentData

section DescentTranslation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {jT : T.toGrp ⟶ G}

local notation "b" => algebraBaseMap k K
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT

private instance nearbyDescentExtendedAffine :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

/-- Push a lower torus vector to the actual translation quotient of the
upper apartment. -/
def descentTranslationMap (f : S ⟶ T) (hS : IsSplitTorus S.toGrp) :
    V S →ₗ[ℝ] TranslationSpace (S := (CommGroupScheme.baseChange b).obj T) j_K :=
  (rootAnnihilator (S := (CommGroupScheme.baseChange b).obj T) j_K).mkQ.comp
    (descentCocharacterMap k K f hS)

@[simp] theorem descentTranslationMap_apply (f : S ⟶ T)
    (hS : IsSplitTorus S.toGrp) (v : V S) :
    descentTranslationMap (K := K) (jT := jT) f hS v =
      Submodule.Quotient.mk (descentCocharacterMap k K f hS v) := rfl

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) jT).hom.hom.left] {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map jT) ω)
  (f : S ⟶ T) (hS : IsSplitTorus S.toGrp)

/-- The existing descended apartment point is exactly translation by the
quotient of the descended cocharacter vector. -/
theorem descentTranslate_eq_vadd (x : D.Apartment) (v : V S) :
    D.descentTranslate f hS x v =
      descentTranslationMap (K := K) (jT := jT) f hS v +ᵥ x := by
  apply Apartment.ext
  rfl

/-- Scaling a lower vector scales the actual upper translation vector. -/
theorem descentTranslate_smul_eq_vadd (x : D.Apartment) (t : ℝ) (v : V S) :
    D.descentTranslate f hS x (t • v) =
      t • descentTranslationMap (K := K) (jT := jT) f hS v +ᵥ x := by
  rw [D.descentTranslate_eq_vadd f hS, map_smul]

end DescentTranslation

section MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))
  (f : S ⟶ T) (hS : IsSplitTorus S.toGrp)
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

include hG hiT hDC

/-- The original upper point belongs to the closed facet of every
sufficiently nearby actual descended translate. -/
theorem eventually_mem_facetClosure_descentTranslate
    (x : D.Apartment) (v : V S) :
    ∀ᶠ t : ℝ in 𝓝 0,
      x ∈ AffineRootSystem.facetClosure D.affineRoots
        (D.descentTranslate f hS x (t • v)) := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  have hnear := B.eventually_mem_facetClosure_smul_vadd x
    (descentTranslationMap (K := inertiaFixedField F) (jT := iT) f hS v)
  dsimp only [IntegerValuationBuildingData.affineRoots, B,
    MaximalUnramified.buildingDataOfApartment] at hnear
  simpa only [D.descentTranslate_smul_eq_vadd f hS] using hnear

/-- On one parameter neighbourhood all two-point root fixers are those
of the translated singleton. -/
theorem eventually_rootFixer_pair_eq_singleton_descentTranslate
    (x : D.Apartment) (v : V S) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ a : relativeRoots
      (T := (CommGroupScheme.baseChange
        (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT),
      D.rootFixer a.1 {x, D.descentTranslate f hS x (t • v)} =
        D.rootFixer a.1 {D.descentTranslate f hS x (t • v)} := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  filter_upwards [D.eventually_mem_facetClosure_descentTranslate f hS hG hiT C hDC x v]
    with t ht a
  exact D.rootFixer_pair_eq_singleton_of_mem_facetClosure
    B.affineRoot_mem_or_two_smul_mem ht a.property

/-- The actual two-point and translated singleton sharp fixers agree
near the zero parameter on every descended line. -/
theorem eventually_sharpFixer_pair_eq_singleton_descentTranslate
    (x : D.Apartment) (v : V S) :
    ∀ᶠ t : ℝ in 𝓝 0,
      D.sharpFixer {x, D.descentTranslate f hS x (t • v)} =
        D.sharpFixer {D.descentTranslate f hS x (t • v)} := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  filter_upwards [D.eventually_mem_facetClosure_descentTranslate f hS hG hiT C hDC x v]
    with t ht
  exact D.sharpFixer_pair_eq_singleton_of_mem_facetClosure
    B.affineRoot_mem_or_two_smul_mem ht

end MaximalUnramified

end KPApartmentData

end Langlands.Geometry.Building
