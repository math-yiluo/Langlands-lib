import Langlands.Geometry.Building.ApartmentQuotientComparison
import Langlands.Geometry.Building.KPLieGradedAction

/-!
# Lie filtrations on the reduced building from compatible apartment lattices

This is a conditional construction for KP §13.3.1. An apartment family `L` gives a well-defined
family on the reduced building quotient if its nonnegative-depth lattices transform under the
normalizer and are stabilized by the subgroups `G(F)^♯_x` used in the quotient. No construction of
the integral models or verification of these two hypotheses is supplied here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} (L : P.LieFiltrationData)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem map_adjoint_one (M : Submodule 𝒪[F] (GenericLie 𝒪[F] G)) :
    M.map (GenericLie.adjoint 𝒪[F] (1 : rationalPoints G)) = M := by
  have h : GenericLie.adjoint 𝒪[F] (1 : rationalPoints G) = LinearMap.id :=
    LinearMap.ext (GenericLie.adjoint_one 𝒪[F])
  rw [h, Submodule.map_id]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem map_adjoint_mul (g h : rationalPoints G)
    (M : Submodule 𝒪[F] (GenericLie 𝒪[F] G)) :
    M.map (GenericLie.adjoint 𝒪[F] (g * h)) =
      (M.map (GenericLie.adjoint 𝒪[F] h)).map (GenericLie.adjoint 𝒪[F] g) := by
  rw [← Submodule.map_comp]
  congr 1
  exact LinearMap.ext (GenericLie.adjoint_mul 𝒪[F] g h)

local instance : MulAction (rationalPoints G) (Submodule 𝒪[F] (GenericLie 𝒪[F] G)) where
  smul g M := M.map (GenericLie.adjoint 𝒪[F] g)
  one_smul := map_adjoint_one
  mul_smul g h := map_adjoint_mul g h

/-- Compatibility of the nonnegative-depth apartment lattices with the two ingredients of the
reduced building quotient: normalizer transport and invariance under `G(F)^♯_x`. -/
structure IsAdjointCompatible : Prop where
  normalizer (n : normalizerPoints P.i) (x : P.Apartment) (r : NNReal) :
    (L.lieFiltration x r).map (GenericLie.adjoint 𝒪[F] (n : rationalPoints G)) =
      L.lieFiltration (n • x) r
  sharpFixer (x : P.Apartment) : P.sharpFixer {x} ≤ L.filtrationStabilizer x

variable {L}

private theorem adjoint_mem_lieFiltrationReal_of_map_le {x y : P.Apartment}
    {g : rationalPoints G} {r : ℝ}
    (h : (L.lieFiltration x (shiftedIndex r)).map (GenericLie.adjoint 𝒪[F] g) ≤
      L.lieFiltration y (shiftedIndex r)) {X : GenericLie 𝒪[F] G}
    (hX : X ∈ L.lieFiltrationReal x r) :
    GenericLie.adjoint 𝒪[F] g X ∈ L.lieFiltrationReal y r := by
  rw [mem_lieFiltrationReal] at hX ⊢
  intro a ha
  rw [← map_smul]
  exact h (Submodule.mem_map.2 ⟨_, hX a ha, rfl⟩)

/-- The normalizer transports the real-depth lattices, since the shift uses scalar multiples. -/
theorem IsAdjointCompatible.normalizer_real (hL : L.IsAdjointCompatible)
    (n : normalizerPoints P.i) (x : P.Apartment) (r : ℝ) :
    (L.lieFiltrationReal x r).map (GenericLie.adjoint 𝒪[F] (n : rationalPoints G)) =
      L.lieFiltrationReal (n • x) r := by
  have h := (hL.normalizer n x (shiftedIndex r)).le
  have h' := (hL.normalizer n⁻¹ (n • x) (shiftedIndex r)).le
  rw [inv_smul_smul] at h'
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact adjoint_mem_lieFiltrationReal_of_map_le h hX
  · intro Y hY
    refine ⟨_, adjoint_mem_lieFiltrationReal_of_map_le h' hY, ?_⟩
    change GenericLie.adjoint 𝒪[F] (n : rationalPoints G)
      (GenericLie.adjoint 𝒪[F] (n : rationalPoints G)⁻¹ Y) = Y
    rw [← GenericLie.adjoint_mul, mul_inv_cancel, GenericLie.adjoint_one]

private def lieFiltrationBuildingHom (hL : L.IsAdjointCompatible) (r : ℝ) :
    P.ReducedBuilding →[rationalPoints G] Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ApartmentQuotient.lift P.apartment.sharpFixerFamily
    { toFun := fun x => L.lieFiltrationReal x r
      map_smul' := fun n x => (hL.normalizer_real n x r).symm }
    (by
      intro x g hg
      have hx := hL.sharpFixer x hg
      apply MulAction.mem_stabilizer_iff.2
      change (L.lieFiltrationReal x r).map (GenericLie.adjoint 𝒪[F] g) = L.lieFiltrationReal x r
      apply le_antisymm
      · rintro _ ⟨X, hX, rfl⟩
        exact adjoint_mem_lieFiltrationReal hx hX
      · intro Y hY
        refine ⟨_, adjoint_mem_lieFiltrationReal (inv_mem hx) hY, ?_⟩
        rw [← GenericLie.adjoint_mul, mul_inv_cancel, GenericLie.adjoint_one])

/-- The real-depth Lie lattice at a point of the reduced building, obtained from the supplied
compatible family by `ApartmentQuotient.lift`. At `g · x` it is `Ad(g) 𝔤_{x,r}`. -/
def lieFiltrationOnBuilding (hL : L.IsAdjointCompatible) (y : P.ReducedBuilding) (r : ℝ) :
    Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  lieFiltrationBuildingHom hL r y

@[simp] theorem lieFiltrationOnBuilding_apartmentMap (hL : L.IsAdjointCompatible)
    (x : P.Apartment) (r : ℝ) :
    lieFiltrationOnBuilding hL (P.apartmentMap x) r = L.lieFiltrationReal x r :=
  ApartmentQuotient.lift_apartment _ _ _ _

/-- The equivariance of the descended lattice with respect to the actual adjoint action. -/
theorem map_adjoint_lieFiltrationOnBuilding (hL : L.IsAdjointCompatible) (g : rationalPoints G)
    (y : P.ReducedBuilding) (r : ℝ) :
    (lieFiltrationOnBuilding hL y r).map (GenericLie.adjoint 𝒪[F] g) =
      lieFiltrationOnBuilding hL (g • y) r :=
  ((lieFiltrationBuildingHom hL r).map_smul g y).symm

theorem lieFiltrationOnBuilding_smul_apartmentMap (hL : L.IsAdjointCompatible)
    (g : rationalPoints G) (x : P.Apartment) (r : ℝ) :
    lieFiltrationOnBuilding hL (g • P.apartmentMap x) r =
      (L.lieFiltrationReal x r).map (GenericLie.adjoint 𝒪[F] g) := by
  rw [← map_adjoint_lieFiltrationOnBuilding, lieFiltrationOnBuilding_apartmentMap]

/-- The strict-depth supremum at a reduced building point. For periodic `L` this is KP's union. -/
def lieFiltrationPlusOnBuilding (hL : L.IsAdjointCompatible) (y : P.ReducedBuilding) (r : ℝ) :
    Submodule 𝒪[F] (GenericLie 𝒪[F] G) :=
  ⨆ (s : ℝ) (_ : r < s), lieFiltrationOnBuilding hL y s

@[simp] theorem lieFiltrationPlusOnBuilding_apartmentMap (hL : L.IsAdjointCompatible)
    (x : P.Apartment) (r : ℝ) :
    lieFiltrationPlusOnBuilding hL (P.apartmentMap x) r = L.lieFiltrationPlusReal x r := by
  simp only [lieFiltrationPlusOnBuilding, lieFiltrationOnBuilding_apartmentMap, lieFiltrationPlusReal]

theorem map_adjoint_lieFiltrationPlusOnBuilding (hL : L.IsAdjointCompatible)
    (g : rationalPoints G) (y : P.ReducedBuilding) (r : ℝ) :
    (lieFiltrationPlusOnBuilding hL y r).map (GenericLie.adjoint 𝒪[F] g) =
      lieFiltrationPlusOnBuilding hL (g • y) r := by
  simp only [lieFiltrationPlusOnBuilding, Submodule.map_iSup, map_adjoint_lieFiltrationOnBuilding]

theorem lieFiltrationOnBuilding_antitone (hL : L.IsAdjointCompatible) (hper : L.IsPeriodic)
    (y : P.ReducedBuilding) : Antitone (lieFiltrationOnBuilding hL y) := by
  obtain ⟨g, x, rfl⟩ := P.exists_smul_apartmentMap y
  intro r s hrs
  simp only [lieFiltrationOnBuilding_smul_apartmentMap]
  exact Submodule.map_mono (L.lieFiltrationReal_antitone hper x hrs)

theorem mem_lieFiltrationPlusOnBuilding (hL : L.IsAdjointCompatible) (hper : L.IsPeriodic)
    {y : P.ReducedBuilding} {r : ℝ} {X : GenericLie 𝒪[F] G} :
    X ∈ lieFiltrationPlusOnBuilding hL y r ↔ ∃ s, r < s ∧ X ∈ lieFiltrationOnBuilding hL y s :=
  mem_biSup_lt_of_antitone (lieFiltrationOnBuilding_antitone hL hper y)

theorem lieFiltrationPlusOnBuilding_le (hL : L.IsAdjointCompatible) (hper : L.IsPeriodic)
    (y : P.ReducedBuilding) (r : ℝ) :
    lieFiltrationPlusOnBuilding hL y r ≤ lieFiltrationOnBuilding hL y r :=
  iSup₂_le fun _ hs => lieFiltrationOnBuilding_antitone hL hper y hs.le

end Langlands.Geometry.Building.ParahoricBuildingData.LieFiltrationData
