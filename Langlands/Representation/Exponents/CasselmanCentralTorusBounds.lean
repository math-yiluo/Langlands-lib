import Langlands.Representation.Exponents.CasselmanCentralTorusLift
import Langlands.Representation.Exponents.CasselmanConeNormBounds

/-! # Strict bounds on central torus points of represented Levis -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

/-- The ambient maximal torus of a compatible presentation mapped into the
literal represented Levi point image. -/
def presentationTorusPointsMap :
    rationalPoints pres.data.T.toGrp →* pointImage (l ≫ p) :=
  (rationalPoints.map pres.data.i).codRestrict _ (by
    intro t
    have ht := range_le_standardLevi pres.data.i pres.data.ν pres.data.J
      (Over.mk (𝟙 _)) ⟨t, rfl⟩
    rw [← pres.isCompatible.levi_eq] at ht
    exact ht)

@[simp] theorem presentationTorusPointsMap_val (t : rationalPoints pres.data.T.toGrp) :
    (presentationTorusPointsMap pres t : rationalPoints G) =
      rationalPoints.map pres.data.i t := rfl

theorem presentationTorusPointsMap_comp_component (s : rationalPoints A.toGrp) :
    presentationTorusPointsMap pres
      (rationalPoints.map (CommGroupScheme.groupHom pres.data.f) s) =
        splitComponentPointsMap (l ≫ p) a s := by
  apply Subtype.ext
  change (s ≫ (CommGroupScheme.groupHom pres.data.f).hom.hom) ≫ pres.data.i.hom.hom =
    (s ≫ a.hom.hom) ≫ (l ≫ p).hom.hom
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun f => s ≫ f)
    (congrArg (fun f : A.toGrp ⟶ G => f.hom.hom) pres.isCompatible.factor_comp)

/-- Ambient torus points whose images lie in the full abstract Levi center. -/
def presentationCentralTorusPoints : Subgroup (rationalPoints pres.data.T.toGrp) :=
  (Subgroup.center (pointImage (l ≫ p))).comap (presentationTorusPointsMap pres)

/-- The actual map from those torus points to the full abstract Levi center. -/
def presentationCentralTorusToCenter :
    presentationCentralTorusPoints pres →* Subgroup.center (pointImage (l ≫ p)) :=
  ((presentationTorusPointsMap pres).comp
    (presentationCentralTorusPoints pres).subtype).codRestrict _ (fun t => t.property)

section Topology

variable [TopologicalSpace k] [IsAffine pres.data.T.X.left]

local instance boundsTorusTopology : TopologicalSpace (rationalPoints pres.data.T.toGrp) :=
  rationalPointTopology k pres.data.T.X
local instance boundsAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

theorem continuous_presentationTorusPointsMap :
    Continuous (presentationTorusPointsMap pres) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (continuous_rationalPointMap k pres.data.i.hom.hom).subtype_mk _

theorem continuous_presentationCentralTorusToCenter :
    Continuous (presentationCentralTorusToCenter pres) :=
  (((continuous_presentationTorusPointsMap pres).comp continuous_subtype_val).subtype_mk _)

variable [IsTopologicalGroup (rationalPoints G)] [T2Space (rationalPoints G)]

theorem isClosed_presentationCentralTorusPoints :
    IsClosed (presentationCentralTorusPoints pres : Set (rationalPoints pres.data.T.toGrp)) := by
  have hc : IsClosed
      (Subgroup.center (pointImage (l ≫ p)) : Set (pointImage (l ≫ p))) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set (pointImage (l ≫ p))))
  exact hc.preimage (continuous_presentationTorusPointsMap pres)

variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- A full-center character has the same norm at a central torus point and
a split-component representative of that point modulo the norm kernel. -/
theorem centralCharacter_norm_eq_of_component_mod_normKernel
    (χ : Subgroup.center (pointImage (l ≫ p)) →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set (Subgroup.center (pointImage (l ≫ p)))))
    (t : rationalPoints pres.data.T.toGrp)
    (z : Subgroup.center (pointImage (l ≫ p)))
    (hz : ((z : pointImage (l ≫ p)) : rationalPoints G) = rationalPoints.map pres.data.i t)
    (s : rationalPoints A.toGrp)
    (hts : t * (rationalPoints.map (CommGroupScheme.groupHom pres.data.f) s)⁻¹ ∈
      Plancherel.rationalCommonNormKernel pres.data.T.toGrp) :
    ‖(χ z : ℂ)‖ =
      ‖(χ (splitComponentCenterPointsMap p l pres.isCompatible.splitComponent s) : ℂ)‖ := by
  have ht : t ∈ presentationCentralTorusPoints pres := by
    change presentationTorusPointsMap pres t ∈ Subgroup.center (pointImage (l ≫ p))
    have heq : presentationTorusPointsMap pres t = z := Subtype.ext hz.symm
    rw [heq]
    exact z.property
  have hs : rationalPoints.map (CommGroupScheme.groupHom pres.data.f) s ∈
      presentationCentralTorusPoints pres := by
    change presentationTorusPointsMap pres _ ∈ Subgroup.center (pointImage (l ≫ p))
    rw [presentationTorusPointsMap_comp_component]
    exact splitComponentPointsMap_mem_center (l ≫ p) pres.isCompatible.splitComponent s
  have htz : presentationCentralTorusToCenter pres ⟨t, ht⟩ = z := by
    apply Subtype.ext
    exact Subtype.ext hz.symm
  have hsz : presentationCentralTorusToCenter pres
      ⟨rationalPoints.map (CommGroupScheme.groupHom pres.data.f) s, hs⟩ =
        splitComponentCenterPointsMap p l pres.isCompatible.splitComponent s := by
    apply Subtype.ext
    exact presentationTorusPointsMap_comp_component pres s
  have hnorm := Plancherel.SplitTorus.norm_eq_of_closedSubgroup_mul_inv_mem_commonNormKernel
    pres.isCompatible.maximalSplit.isSplitSubtorus.1
    (presentationCentralTorusPoints pres) (isClosed_presentationCentralTorusPoints pres)
    (χ.comp (presentationCentralTorusToCenter pres))
    (hχ.preimage (continuous_presentationCentralTorusToCenter pres))
    ⟨t, ht⟩ ⟨_, hs⟩ hts
  simpa only [MonoidHom.comp_apply, htz, hsz] using hnorm

end Topology

section Valuation

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- A component representative modulo the norm kernel has exactly the
original torus point's character orders, under the restricted-root pairing. -/
theorem pair_restrictedCharacter_valuation_eq_order
    (t : rationalPoints pres.data.T.toGrp) (s : rationalPoints A.toGrp)
    (hts : t * (rationalPoints.map (CommGroupScheme.groupHom pres.data.f) s)⁻¹ ∈
      Plancherel.rationalCommonNormKernel pres.data.T.toGrp)
    (α : characterLattice pres.data.T) :
    RealTorusSpace.pair A ((1 : ℝ) ⊗ₜ[ℤ] (pres.data.f ≫ α))
      (Plancherel.SplitTorus.valuation
        pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 s).toAdd =
      ((Plancherel.rationalCharacterValuation pres.data.T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice pres.data.T).symm α) : ℝ) := by
  let hA := pres.isCompatible.splitComponent.isCentralSplitTorus.1.1
  let hT := pres.isCompatible.maximalSplit.isSplitSubtorus.1
  have hv := Plancherel.SplitTorus.valuation_eq_of_mul_inv_mem hT hts
  change RealTorusSpace.pair A
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom pres.data.f)
      ((1 : ℝ) ⊗ₜ[ℤ] α)) (Plancherel.SplitTorus.valuation hA s).toAdd = _
  rw [← RealTorusSpace.pair_cocharacterMapReal,
    ← Plancherel.SplitTorus.valuation_map hA hT pres.data.f s, ← hv,
    ← RealTorusSpace.eval_eq_pair]
  have h := BruhatTits.Cartan.centralizerValuation_spec (𝟙 pres.data.T.toGrp)
    (BruhatTits.Cartan.restrictionEvaluation_id_bijective hT) t
    ((rationalCharacters.equivCharacterLattice pres.data.T).symm α)
  simpa only [BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
    characterRestrict_id, AddMonoidHom.id_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.apply_symm_apply] using h

end Valuation

section StrictBounds

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [T2Space k] [LocallyOfFiniteType G.X.hom]

local instance strictBoundsAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Positive-cone bounds for represented normalized exponents give strict
norm bounds on every central torus point whose selected-root orders vanish
and whose simple-root orders are nonnegative and not all zero. -/
theorem centralExponent_norm_lt_one_on_centralTorus_of_positiveCone
    (r : U ⟶ P) (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))
    (hcone : ∀ ψ : rationalPoints A.toGrp →* ℂˣ,
      IsNormalizedJacquetExponent p l r hp hl hr hmul
        pres.isCompatible.splitComponent π ψ →
      Plancherel.SplitTorus.normalizedRealPart
        pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 ψ ∈ pres.positiveCone)
    (χ : Subgroup.center (pointImage (l ≫ p)) →* ℂˣ)
    (hχ : IsCentralExponent ((jacquetFunctor p l r hp hr hl hmul).obj π).representation χ)
    (t : rationalPoints pres.data.T.toGrp)
    (z : Subgroup.center (pointImage (l ≫ p)))
    (hz : ((z : pointImage (l ≫ p)) : rationalPoints G) = rationalPoints.map pres.data.i t)
    (hzero : ∀ α ∈ pres.data.J,
      (Plancherel.rationalCharacterValuation pres.data.T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice pres.data.T).symm α) = 0)
    (hnonneg : ∀ α ∈ simpleRelativeRoots pres.data.i pres.data.ν,
      0 ≤ (Plancherel.rationalCharacterValuation pres.data.T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice pres.data.T).symm α))
    (hpos : ∃ α ∈ simpleRelativeRoots pres.data.i pres.data.ν,
      0 < (Plancherel.rationalCharacterValuation pres.data.T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice pres.data.T).symm α)) :
    ‖(χ z : ℂ)‖ < 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : T2Space (rationalPoints G) := rationalPoint_t2Space k G
  have := pres.isCompatible.maximalSplit.isSplitSubtorus.1.isAffineHom
  have : IsAffine pres.data.T.X.left := isAffine_of_isAffineHom pres.data.T.X.hom
  obtain ⟨b, hb⟩ := pres.exists_splitComponent_point_mod_normKernel t hzero
  let s := CocharacterUniformizer.latticeSection k A (.ofAdd b)
  rw [centralCharacter_norm_eq_of_component_mod_normKernel pres χ hχ.1 t z hz s hb]
  apply centralExponent_norm_lt_one_of_positiveCone p l r hp hl hr hmul
    pres.isCompatible.splitComponent pres π hcone χ hχ s
  · intro β hβ
    obtain ⟨α, hα, _, rfl⟩ := pres.mem_restrictedRoots.mp hβ
    rw [pair_restrictedCharacter_valuation_eq_order pres t s hb α]
    exact_mod_cast hnonneg α hα
  · obtain ⟨α, hα, hpα⟩ := hpos
    have hnot : α ∉ pres.data.J := by
      intro hαJ
      rw [hzero α hαJ] at hpα
      exact lt_irrefl _ hpα
    refine ⟨(1 : ℝ) ⊗ₜ[ℤ] (pres.data.f ≫ α),
      pres.mem_restrictedRoots.mpr ⟨α, hα, hnot, rfl⟩, ?_⟩
    rw [pair_restrictedCharacter_valuation_eq_order pres t s hb α]
    exact_mod_cast hpα

end StrictBounds

end Langlands.Aubert.General.RepresentedParabolic
