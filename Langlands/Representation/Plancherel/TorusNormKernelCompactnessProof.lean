import Langlands.Representation.Plancherel.TorusNormKernelCompactnessStatement
import Langlands.Representation.Plancherel.TorusNormKernel.FieldNormCompact
import Langlands.Representation.Plancherel.TorusNormKernel.NormCharacter
import Langlands.Representation.Plancherel.TorusNormKernel.SplitCoordinates
import Langlands.Representation.Plancherel.RationalCharacterTopology
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.AlgebraicGeometry.PointTopology.AffineBoundedCompactness
import Langlands.Galois.Local.AbsoluteDefinitions

/-!
# Compactness of the rational norm kernel of a local-field torus
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.TorusNormKernel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Regular-function values at a rational point are extended by the field inclusion. -/
theorem rationalPointAlgebraHom_rationalExtend (E : Type u) [Field E] [Algebra F E]
    (T : GroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]
    [IsAffine (GaloisPointComparison.baseChanged F E T).X.left]
    (p : rationalPoints T) (f : AffineCoordinateRing F T.X) :
    rationalPointAlgebraHom E (GaloisPointComparison.baseChanged F E T).X
        (GaloisPointComparison.rationalExtend F E T p)
        ((Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap F E)).appTop.hom f) =
      algebraMap F E (rationalPointAlgebraHom F T.X p f) := by
  set s := GaloisPointComparison.rationalExtend F E T p
  have hE := affineSchemePointEquiv_apply_eq_evaluation (GaloisPointComparison.baseChanged F E T)
    (rationalPointEquiv E _ s)
    ((Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap F E)).appTop.hom f)
  have hF := affineSchemePointEquiv_apply_eq_evaluation T (rationalPointEquiv F T.X p) f
  change affineSchemePointEquiv E _ E (rationalPointEquiv E _ s) _ =
    algebraMap F E (affineSchemePointEquiv F T.X F (rationalPointEquiv F T.X p) f)
  rw [hE, hF]
  change ((rationalPointEquiv E _ s).left.appTop ≫ (Scheme.ΓSpecIso _).hom).hom
      ((Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap F E)).appTop.hom f) =
    algebraMap F E (((rationalPointEquiv F T.X p).left.appTop ≫ (Scheme.ΓSpecIso _).hom).hom f)
  rw [rationalPointEquiv_left, rationalPointEquiv_left]
  have h1 : (Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap F E)).appTop ≫
      s.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).hom =
        p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom ≫
          CommRingCat.ofHom (algebraMap F E) := by
    have h0 := GaloisPointComparison.rationalExtend_fst F E T p
    have h0' : (Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap F E)).appTop ≫
        s.left.appTop = p.left.appTop ≫ (GaloisPointComparison.baseMap F E).appTop := by
      have h2 := congrArg Scheme.Hom.appTop h0
      rw [Scheme.Hom.comp_appTop (GaloisPointComparison.baseMap F E) p.left] at h2
      exact (Scheme.Hom.comp_appTop s.left _).symm.trans h2
    calc _ = ((Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap F E)).appTop ≫
          s.left.appTop) ≫ (Scheme.ΓSpecIso (CommRingCat.of E)).hom := (Category.assoc _ _ _).symm
      _ = (p.left.appTop ≫ (GaloisPointComparison.baseMap F E).appTop) ≫
          (Scheme.ΓSpecIso (CommRingCat.of E)).hom := by rw [h0']
      _ = _ := by
        rw [Category.assoc, GaloisPointComparison.baseMap, Scheme.ΓSpecIso_naturality]
  exact congrArg (fun φ => φ.hom f) h1

variable (F)

/-- In the canonical norm, unit valuation means norm one. -/
theorem localNorm_eq_one_iff (x : F) :
    letI := Langlands.LocalGalois.localNormedField F
    ‖x‖ = 1 ↔ ValuativeRel.valuation F x = 1 := by
  let _ := Langlands.LocalGalois.localNormedField F
  have h1 := Langlands.LocalGalois.localNormedField_le F x 1
  have h2 := Langlands.LocalGalois.localNormedField_le F 1 x
  rw [norm_one, map_one] at h1 h2
  constructor
  · intro hx
    exact le_antisymm (h1.mp hx.le) (h2.mp hx.ge)
  · intro hx
    exact le_antisymm (h1.mpr hx.le) (h2.mpr hx.ge)

/-- Units of a finite extension whose field norm has unit valuation form a compact set. -/
theorem isCompact_units_valuation_norm_eq_one (E : Type u) [Field E] [Algebra F E]
    [FiniteDimensional F E] [TopologicalSpace E] [IsModuleTopology F E] :
    IsCompact {u : Eˣ | ValuativeRel.valuation F (Algebra.norm F (u : E)) = 1} := by
  let _ := Langlands.LocalGalois.localNormedField F
  have : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have h := isCompact_units_algebraNorm_eq_one (F := F) (E := E)
  have heq : {u : Eˣ | ValuativeRel.valuation F (Algebra.norm F (u : E)) = 1} =
      {u : Eˣ | ‖Algebra.norm F (u : E)‖ = 1} := by
    ext u
    exact (localNorm_eq_one_iff F _).symm
  rw [heq]
  exact h

/-- A compact subset of a local field is valuatively bounded. -/
theorem exists_vle_of_isCompact {S : Set F} (hS : IsCompact S) :
    ∃ b : F, b ≠ 0 ∧ ∀ x ∈ S, x ≤ᵥ b := by
  let _ := Langlands.LocalGalois.localNormedField F
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall 0
  obtain ⟨b, hb⟩ := NormedField.exists_lt_norm F (max R 0)
  refine ⟨b, fun h => ?_, fun x hx => ?_⟩
  · rw [h, norm_zero] at hb
    exact absurd hb (not_lt.mpr (le_max_right _ _))
  · have hx' : ‖x‖ ≤ ‖b‖ := by
      have := hR hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans ((le_max_left _ _).trans hb.le)
    exact ((ValuativeRel.valuation F).vle_iff_le).mpr
      ((Langlands.LocalGalois.localNormedField_le F x b).mp hx')

/-- The preimage of a compact set under the field inclusion is compact. -/
theorem isCompact_preimage_algebraMap (E : Type u) [Field E] [Algebra F E]
    [FiniteDimensional F E] [TopologicalSpace E] [IsModuleTopology F E] {C : Set E}
    (hC : IsCompact C) : IsCompact (algebraMap F E ⁻¹' C) := by
  let _ := Langlands.LocalGalois.localNormedField F
  have : CompleteSpace F := Langlands.LocalGalois.localNormedField_complete F
  have : T2Space E := t2Space_of_moduleTopology (F := F)
  have : IsTopologicalAddGroup E := IsModuleTopology.isTopologicalAddGroup F E
  have hker : LinearMap.ker (Algebra.linearMap F E) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (algebraMap F E).injective
  exact (LinearMap.isClosedEmbedding_of_injective hker).isCompact_preimage hC

variable {F}

/-- Characters have unit-valuation values on the common norm kernel. -/
theorem valuation_eval_of_mem {T : GroupScheme (Spec (CommRingCat.of F))}
    {p : rationalPoints T} (hp : p ∈ rationalCommonNormKernel T)
    (ψ : rationalCharacters T) :
    ValuativeRel.valuation F (rationalCharacterEval ψ p : F) = 1 := by
  have h := (mem_rationalCommonNormKernel T p).mp hp ψ
  have hk : rationalCharacterEval ψ p ∈ FML.unitGroup F := by
    rw [← fieldNormUnits_ker F]
    exact h
  simpa only [FML.unitGroup, Valuation.mem_unitGroup_iff] using hk

end Langlands.Plancherel.TorusNormKernel

namespace Langlands.Plancherel

open TorusNormKernel

/-- **Compactness of torus norm kernels.** For every torus over a nonarchimedean local field,
the common kernel of the normalized absolute values of its rational characters is compact. -/
theorem torusNormKernelCompactness : TorusNormKernelCompactnessStatement.{u} := by
  intro F _ _ _ _ T _ _ hT
  let _ : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  let _ := rationalPointTopology F T.X
  obtain ⟨E, _, _, _, -, hsplit⟩ := torusFiniteGaloisSplitting F T hT
  obtain ⟨I, _, ⟨e⟩⟩ := hsplit
  have := Fintype.ofFinite I
  let _ : TopologicalSpace E := moduleTopology F E
  have : IsModuleTopology F E := ⟨rfl⟩
  have : IsTopologicalRing E := IsModuleTopology.isTopologicalRing F E
  have : IsAffine (GaloisPointComparison.baseChanged F E T).X.left := by
    change IsAffine (Limits.pullback T.X.hom (GaloisPointComparison.baseMap F E))
    infer_instance
  refine (localFieldAffineBoundedCompactness_proof F T.X _
    (isClosed_rationalCommonNormKernel T)).mp ?_
  intro f
  obtain ⟨Φ, hΦ, hΦeq⟩ := exists_continuous_of_splitCharacters e
    ((Limits.pullback.fst T.X.hom (GaloisPointComparison.baseMap F E)).appTop.hom f)
  set KU := {u : Eˣ | ValuativeRel.valuation F (Algebra.norm F (u : E)) = 1}
  have hKU : IsCompact KU := isCompact_units_valuation_norm_eq_one F E
  have hC : IsCompact (Φ '' Set.pi Set.univ (fun _ : I => KU)) :=
    (isCompact_univ_pi fun _ => hKU).image hΦ
  obtain ⟨b, hb0, hb⟩ := exists_vle_of_isCompact F (isCompact_preimage_algebraMap F E hC)
  refine ⟨b, hb0, fun p hp => hb _ ?_⟩
  refine ⟨fun i => rationalCharacterEval (splitCharacter e i)
    (GaloisPointComparison.rationalExtend F E T p), fun i _ => ?_, ?_⟩
  · change ValuativeRel.valuation F (Algebra.norm F
      ((rationalCharacterEval (splitCharacter e i)
        (GaloisPointComparison.rationalExtend F E T p) : Eˣ) : E)) = 1
    rw [← normCharacter_eval]
    exact valuation_eval_of_mem hp _
  · rw [← hΦeq, rationalPointAlgebraHom_rationalExtend]
