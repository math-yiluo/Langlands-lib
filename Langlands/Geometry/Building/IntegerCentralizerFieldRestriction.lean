import Langlands.Geometry.Building.IntegerCentralizer
import Langlands.Geometry.Building.RootApartmentFieldDescent

/-! # Actual centralizer valuation and full V6 under field restriction -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.IntegerValuation

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {Z : GroupScheme (Spec (CommRingCat.of k))}
  (hS : IsSplitTorus S.toGrp)
  (v : Valuation k (WithZero (Multiplicative ℤ)))
  (w : Valuation K (WithZero (Multiplicative ℤ)))
  (horder : ∀ t : kˣ,
    order w (Units.map (algebraMap k K).toMonoidHom t) = order v t)
  (s : S.toGrp ⟶ Z)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "Z_K" => baseChanged k K Z
local notation "s_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) s

include horder

/-- Exact restriction of the scalar order identifies the positive centralizer
valuation at every original point through actual cocharacter base change. -/
theorem centralizerValuation_fieldExtend
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K) s_K))
    (z : rationalPoints Z) :
    splitCocharacterBaseChange (K := K) S hS (centralizerValuation v s h z).toAdd =
      (centralizerValuation w (S := S_K) s_K hK (rationalExtend k K Z z)).toAdd := by
  let L := splitCocharacterBaseChange (K := K) S hS
  have heq : L.symm
      (centralizerValuation w (S := S_K) s_K hK (rationalExtend k K Z z)).toAdd =
      (centralizerValuation v s h z).toAdd := by
    apply h.1
    ext χ
    change eval S (Cartan.characterRestriction s χ) _ =
      eval S (Cartan.characterRestriction s χ) _
    rw [← eval_splitCocharacterBaseChange (K := K) S hS]
    change eval S_K (characterLattice.baseChange b S (Cartan.characterRestriction s χ))
      (L (L.symm _)) = _
    rw [LinearEquiv.apply_symm_apply]
    have hχ : characterLattice.baseChange b S (Cartan.characterRestriction s χ) =
        Cartan.characterRestriction (S := S_K) s_K (rationalCharacters.baseChange b χ) :=
      characterLattice.baseChange_torusCharacterRestrict b s χ
    rw [hχ, centralizerValuation_spec, rationalCharacterEval_extend,
      horder, centralizerValuation_spec]
  have hh := congrArg L heq
  rw [LinearEquiv.apply_symm_apply] at hh
  exact hh.symm

/-- KP uses the negative of the positive centralizer valuation; that sign is
preserved under actual field extension as well. -/
theorem centralizerTranslation_fieldExtend
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K) s_K))
    (z : rationalPoints Z) :
    splitCocharacterBaseChange (K := K) S hS (centralizerTranslation v s h z).toAdd =
      (centralizerTranslation w (S := S_K) s_K hK (rationalExtend k K Z z)).toAdd := by
  rw [centralizerTranslation_toAdd, centralizerTranslation_toAdd, map_neg,
    centralizerValuation_fieldExtend hS v w horder s h hK z]

section Compatibility

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (i : S.toGrp ⟶ G) (j : Z ⟶ G)

local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

include hS

/-- Full V6 descends on every original root and centralizer point through the
literal field-restricted root-function family. -/
theorem IsCentralizerCompatible.fieldRestrict
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K) s_K))
    {ψ : RootFunctionFamily S_K G_K}
    (hψ : IsCentralizerCompatible w (S := S_K) (i_K) (j_K) (s_K) hK ψ) :
    IsCentralizerCompatible v i j s h
      (RootFunctionFamily.fieldRestrict (k := k) ψ) := by
  intro a ha z u hu
  have hroot : (a_K a) ∈ relativeRoots (T := S_K) (i_K) :=
    (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  have hcompat := hψ (a_K a) hroot (rationalExtend k K Z z)
    (rationalExtend k K G u) (rationalExtend_mem_rootGroupPoints (K := K) i a hu)
  simp only [RootFunctionFamily.fieldRestrict_apply]
  rw [map_mul, map_mul, map_inv, rationalExtend_map k K j z]
  rw [← centralizerTranslation_fieldExtend hS v w horder s h hK z,
    eval_splitCocharacterBaseChange] at hcompat
  exact hcompat

end Compatibility

section Apartment

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]

local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

private instance apartmentExtendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance apartmentExtendedMono : Mono (i_K).hom.hom.left := by
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  change Mono ((Over.pullback b).map i.hom.hom).left
  infer_instance

/-- The literal image apartment with precisely the original integer valuation
order, using exact scalar-order restriction and original-unit nontriviality. -/
def fieldRestrictApartment (hE : RelativeRoot.HasOppositeFactorPairs i)
    (hν : ∃ t : kˣ, order v t ≠ 0)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (order w)) :
    KPApartmentData i (order v) := by
  let ω : Kˣ →* Multiplicative ℝ :=
    (Int.castAddHom ℝ).toMultiplicative.comp (orderUnits w)
  have hω : ∃ t : kˣ, (ω (Units.map (algebraMap k K).toMonoidHom t)).toAdd ≠ 0 := by
    obtain ⟨t, ht⟩ := hν
    exact ⟨t, by change order w _ ≠ 0; rw [horder]; exact ht⟩
  let D' := KPApartmentData.fieldRestrict i hS hE ω hω D
  refine { carrier := D'.carrier, exists_eq_orbit := ?_, smul_mem := D'.smul_mem }
  obtain ⟨ψ, hψ, hcompat, hcarrier⟩ := D'.exists_eq_orbit
  refine ⟨ψ, hψ, ?_, hcarrier⟩
  change IsSplitTorusCompatible i
    (fun t => order w (Units.map (algebraMap k K).toMonoidHom t)) ψ at hcompat
  simpa only [horder] using hcompat

@[simp] theorem fieldRestrictApartment_carrier
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    (hν : ∃ t : kˣ, order v t ≠ 0)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (order w)) :
    (fieldRestrictApartment hS v w horder i hE hν D).carrier =
      RootFunctionFamily.fieldRestrict (k := k) '' D.carrier := rfl

/-- The entire literal image apartment satisfies full V6 on the original
actual centralizer if the upstairs class does on its literal base change. -/
theorem fieldRestrictApartment_isOmegaCompatible
    (hE : RelativeRoot.HasOppositeFactorPairs i)
    (hν : ∃ t : kˣ, order v t ≠ 0)
    (D : KPApartmentData (S := S_K) (G := G_K) (i_K) (order w))
    (C : CentralizerDatum i)
    (hK : Function.Bijective (Cartan.restrictionEvaluation (S := S_K)
      ((GroupScheme.baseChange b).map C.s)))
    (hD : ∀ ψ ∈ D.carrier, IsCentralizerCompatible w (S := S_K) (i_K)
      ((GroupScheme.baseChange b).map C.j) ((GroupScheme.baseChange b).map C.s) hK ψ) :
    IsOmegaCompatible v (fieldRestrictApartment hS v w horder i hE hν D) C := by
  intro φ hφ
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  exact IsCentralizerCompatible.fieldRestrict hS v w horder C.s i C.j
    C.bijective hK (hD ψ hψ)

end Apartment

end Langlands.Geometry.Building.IntegerValuation
