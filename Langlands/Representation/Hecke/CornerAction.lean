import Langlands.Representation.Hecke.ActionProjection
import Langlands.Representation.Hecke.Corner

/-! The actual compact-open Hecke corner acts on the existing fixed vectors. -/

noncomputable section

namespace Langlands.Hecke

open MeasureTheory MeasureTheory.Measure

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Restriction of the actual integrated operator to the existing fixed subspace. -/
def cornerActionLinear : HeckeAlgebra.Corner μ K hK →ₗ[ℂ]
    Module.End ℂ (fixedVectors ρ K.toSubgroup) where
  toFun f :=
    ((heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)).comp
      (fixedVectors ρ K.toSubgroup).subtype).codRestrict
      (fixedVectors ρ K.toSubgroup) (fun v =>
        integratedAction_mem_fixedVectors μ ρ hρ f.property v)
  map_add' f g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (f + g)) v = _
    simp only [map_add, LinearMap.add_apply]
    rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (c • f)) v = _
    simp only [map_smul, LinearMap.smul_apply]
    rfl

/-- The genuine unital corner representation on K-fixed vectors. -/
def cornerAction : HeckeAlgebra.Corner μ K hK →ₐ[ℂ]
    Module.End ℂ (fixedVectors ρ K.toSubgroup) :=
  AlgHom.ofLinearMap (cornerActionLinear μ ρ hρ K hK)
    (by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK 1) v = v
      rw [HeckeAlgebra.Corner.toHeckeAlgebra_one]
      exact heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK v.property)
    (by
      intro f g
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (f * g)) v =
        heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f)
          (heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK g) v)
      rw [map_mul, map_mul, Module.End.mul_apply])

@[simp]
theorem cornerAction_apply (f : HeckeAlgebra.Corner μ K hK)
    (v : fixedVectors ρ K.toSubgroup) :
    (cornerAction μ ρ hρ K hK f v : V) =
      heckeAction μ ρ hρ (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f) v := rfl

/-- The corner's unital module structure, with no new fixed-vector carrier. -/
@[instance_reducible]
def cornerModule : Module (HeckeAlgebra.Corner μ K hK) (fixedVectors ρ K.toSubgroup) where
  smul f v := cornerAction μ ρ hρ K hK f v
  one_smul v := by
    change cornerAction μ ρ hρ K hK 1 v = v
    rw [map_one]
    rfl
  mul_smul f g v := by
    change cornerAction μ ρ hρ K hK (f * g) v =
      cornerAction μ ρ hρ K hK f (cornerAction μ ρ hρ K hK g v)
    rw [map_mul, Module.End.mul_apply]
  smul_zero f := (cornerAction μ ρ hρ K hK f).map_zero
  smul_add f v w := (cornerAction μ ρ hρ K hK f).map_add v w
  add_smul f g v := by
    change cornerAction μ ρ hρ K hK (f + g) v = _
    rw [map_add, LinearMap.add_apply]
    rfl
  zero_smul v := by
    change cornerAction μ ρ hρ K hK 0 v = 0
    rw [map_zero, LinearMap.zero_apply]

@[simp]
theorem cornerModule_smul (f : HeckeAlgebra.Corner μ K hK)
    (v : fixedVectors ρ K.toSubgroup) :
    letI := cornerModule μ ρ hρ K hK
    f • v = cornerAction μ ρ hρ K hK f v := rfl

/-- The corner action agrees with the existing complex scalar multiplication. -/
theorem cornerModule_isScalarTower :
    letI := cornerModule μ ρ hρ K hK
    IsScalarTower ℂ (HeckeAlgebra.Corner μ K hK) (fixedVectors ρ K.toSubgroup) := by
  let _ := cornerModule μ ρ hρ K hK
  constructor
  intro c f v
  change cornerAction μ ρ hρ K hK (c • f) v = c • cornerAction μ ρ hρ K hK f v
  rw [map_smul, LinearMap.smul_apply]

/-- Representation intertwiners restrict to intertwining maps for the actual corner. -/
theorem cornerAction_intertwiner {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (T : ρ.IntertwiningMap σ) (f : HeckeAlgebra.Corner μ K hK)
    (v : fixedVectors ρ K.toSubgroup) :
    fixedVectorsMap T K.toSubgroup (cornerAction μ ρ hρ K hK f v) =
      cornerAction μ σ hσ K hK f (fixedVectorsMap T K.toSubgroup v) := by
  apply Subtype.ext
  exact integratedAction_intertwiner μ hρ hσ T
    (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK f) v

/-- The existing fixed-vector equivalence respects the actual corner action. -/
theorem cornerAction_equiv {σ : Representation ℂ G W} (hσ : IsSmooth σ)
    (e : ρ.Equiv σ) (f : HeckeAlgebra.Corner μ K hK)
    (v : fixedVectors ρ K.toSubgroup) :
    fixedVectorsEquiv e K.toSubgroup (cornerAction μ ρ hρ K hK f v) =
      cornerAction μ σ hσ K hK f (fixedVectorsEquiv e K.toSubgroup v) :=
  cornerAction_intertwiner μ ρ hρ K hK hσ e.toIntertwiningMap f v

/-- Corner refinement and fixed-vector inclusion commute with the actual action. -/
theorem cornerAction_refinement {L : OpenSubgroup G}
    (hL : IsCompact (L : Set G)) (hLK : L ≤ K)
    (f : HeckeAlgebra.Corner μ K hK) (v : fixedVectors ρ K.toSubgroup) :
    (cornerAction μ ρ hρ L hL (HeckeAlgebra.Corner.inclusion μ K hK hL hLK f)
      ⟨v, fun l => v.property ⟨l, hLK l.property⟩⟩ : V) =
      (cornerAction μ ρ hρ K hK f v : V) := rfl

/-- The corner projection acts by projecting the input and output of the full action. -/
theorem cornerAction_project (f : HeckeAlgebra μ) (v : fixedVectors ρ K.toSubgroup) :
    cornerAction μ ρ hρ K hK (HeckeAlgebra.Corner.project μ K hK f) v =
      fixedProjection μ ρ hρ K hK (heckeAction μ ρ hρ f v) := by
  apply Subtype.ext
  change heckeAction μ ρ hρ
      (HeckeAlgebra.Corner.toHeckeAlgebra μ K hK (HeckeAlgebra.Corner.project μ K hK f)) v =
    heckeAction μ ρ hρ (HeckeAlgebra.normalizedIndicator μ K hK) (heckeAction μ ρ hρ f v)
  rw [HeckeAlgebra.Corner.toHeckeAlgebra_project, map_mul, map_mul]
  simp only [Module.End.mul_apply,
    heckeAction_normalizedIndicator_of_fixed μ ρ hρ K hK v.property]

end Langlands.Hecke
