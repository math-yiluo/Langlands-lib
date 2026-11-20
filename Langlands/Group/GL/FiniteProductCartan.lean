import Langlands.Group.GL.UpperTriangularCartan
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.GroupTransport
import Langlands.LocalField.FiniteExtension
import Mathlib.Data.Finset.NoncommProd
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Cartan covering and contraction for finite products -/

noncomputable section

namespace Langlands.GeneralLinear

open Matrix HarishChandraSchwartz

universe u v w

variable {ι : Type u} {R : Type v} {S : ι → Type w}
  [CommRing R] [∀ i, CommRing (S i)] [TopologicalSpace R] [∀ i, TopologicalSpace (S i)]
  (n : ℕ) (e : R ≃+* ∀ i, S i) (he : Continuous e) (he' : Continuous e.symm)

/-- Taking matrix units commutes with a product of topological coefficient rings. -/
def generalLinearEquivPi : GeneralLinear n R ≃ₜ* ∀ i, GeneralLinear n (S i) :=
  let f : Matrix (Fin n) (Fin n) R ≃ₜ* ∀ i, Matrix (Fin n) (Fin n) (S i) :=
    { __ := (e.mapMatrix.trans Matrix.piRingEquiv).toMulEquiv
      continuous_toFun := continuous_pi fun k => continuous_matrix fun i j =>
        (continuous_apply k).comp (he.comp (continuous_apply_apply i j))
      continuous_invFun := continuous_matrix fun i j =>
        he'.comp (continuous_pi fun k => (continuous_apply_apply i j).comp (continuous_apply k)) }
  (Units.mapContinuousMulEquiv f).trans ContinuousMulEquiv.piUnits

theorem generalLinearEquivPi_apply (g : GeneralLinear n R) (k : ι) (i j : Fin n) :
    (generalLinearEquivPi n e he he' g k) i j = e (g i j) k := rfl

private theorem mem_upperTriangularSubgroup_iff_pi (g : GeneralLinear n R) :
    g ∈ upperTriangularSubgroup n R ↔
      ∀ k, generalLinearEquivPi n e he he' g k ∈ upperTriangularSubgroup n (S k) := by
  simp only [mem_upperTriangularSubgroup_iff, generalLinearEquivPi_apply]
  constructor
  · intro h k i j hji
    rw [h i j hji, map_zero]
    rfl
  · intro h i j hji
    apply e.injective
    rw [map_zero]
    exact funext fun k => h k i j hji

/-- The product isomorphism also restricts to upper triangular matrix units. -/
def upperTriangularEquivPi :
    upperTriangularSubgroup n R ≃ₜ* ∀ i, upperTriangularSubgroup n (S i) := by
  let f := generalLinearEquivPi n e he he'
  let h := mem_upperTriangularSubgroup_iff_pi n e he he'
  exact
    { toFun := fun g i => ⟨f g.val i, (h g.val).mp g.property i⟩
      invFun := fun g => ⟨f.symm (fun i => (g i).val), (h _).mpr (by
        rw [f.apply_symm_apply]
        exact fun i => (g i).property)⟩
      left_inv := fun g => Subtype.ext (f.symm_apply_apply g.val)
      right_inv := fun g => funext fun i => Subtype.ext
        (congrFun (f.apply_symm_apply fun k => (g k).val) i)
      map_mul' := fun g h => funext fun i => Subtype.ext
        (congrFun (map_mul f (g : GeneralLinear n R) (h : GeneralLinear n R)) i)
      continuous_toFun := continuous_pi fun i =>
        ((continuous_apply i).comp (f.continuous.comp continuous_subtype_val)).subtype_mk _
      continuous_invFun :=
        (f.symm.continuous.comp (continuous_pi fun _ =>
          continuous_subtype_val.comp (continuous_apply _))).subtype_mk _ }

private def piCompactOpenSubgroup [Finite ι] {G : ι → Type*}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (K : ∀ i, CompactOpenSubgroup (G i)) : CompactOpenSubgroup (∀ i, G i) :=
  ⟨⟨Subgroup.pi Set.univ (fun i => (K i).toSubgroup),
    isOpen_set_pi Set.finite_univ fun i _ => (K i).1.isOpen⟩,
    isCompact_univ_pi fun i => (K i).2⟩

include e he he' in
/-- Compact double-coset covering and uniform upper triangular contraction pass
to a finite product of topological rings and transport along a topological ring
isomorphism. -/
theorem hasUpperTriangularCartanContraction_of_pi [Finite ι]
    (hS : ∀ i, HasUpperTriangularCartanContraction n (S i)) :
    HasUpperTriangularCartanContraction n R := by
  classical
  let _ := Fintype.ofFinite ι
  choose K M hcover hcontract using hS
  let f := generalLinearEquivPi n e he he'
  let fP := upperTriangularEquivPi n e he he'
  let K' := (piCompactOpenSubgroup K).comap f
  let M' := f ⁻¹' Set.pi Set.univ M
  refine ⟨K', M', ?_, ?_⟩
  · intro g
    choose k m hm j hj using fun i => hcover i (f g i)
    let k' : K'.toSubgroup := ⟨f.symm (fun i => (k i).val), by
      change f (f.symm _) ∈ (piCompactOpenSubgroup K).toSubgroup
      rw [f.apply_symm_apply]
      exact fun i _ => (k i).property⟩
    let j' : K'.toSubgroup := ⟨f.symm (fun i => (j i).val), by
      change f (f.symm _) ∈ (piCompactOpenSubgroup K).toSubgroup
      rw [f.apply_symm_apply]
      exact fun i _ => (j i).property⟩
    refine ⟨k', f.symm m, ?_, j', ?_⟩
    · change f (f.symm m) ∈ Set.pi Set.univ M
      rw [f.apply_symm_apply]
      exact fun i _ => hm i
    · apply f.injective
      change f g = f (f.symm _ * f.symm m * f.symm _)
      simp only [map_mul, f.apply_symm_apply]
      funext i
      exact hj i
  · intro J
    let J' := J.comap f.symm.toMonoidHom f.symm.continuous
    let Ji (i : ι) := J'.comap (MonoidHom.mulSingle (fun i => GeneralLinear n (S i)) i)
      (continuous_mulSingle (A := fun i => GeneralLinear n (S i)) i)
    choose L hL using fun i => hcontract i (Ji i)
    refine ⟨(piCompactOpenSubgroup L).comap fP, ?_⟩
    intro m hm p
    let a := m⁻¹ * ((p : upperTriangularSubgroup n R) : GeneralLinear n R) * m
    have hp (i : ι) : fP p.val i ∈ (L i).toSubgroup := p.property i (Set.mem_univ i)
    have hx (i : ι) : Pi.mulSingle i (f a i) ∈ J' := by
      have h := hL i (f m i) (hm i (Set.mem_univ i)) ⟨fP p.val i, hp i⟩
      change f a i ∈ Ji i
      dsimp only [a]
      rw [map_mul, map_mul, map_inv]
      exact h
    have hprod : f a ∈ J' := by
      rw [← Finset.noncommProd_mulSingle (f a)]
      exact Subgroup.noncommProd_mem _ _ fun i _ => hx i
    change f.symm (f a) ∈ J at hprod
    rwa [f.symm_apply_apply] at hprod

/-- The upper triangular Cartan input for a reduced finite algebra with the
module topology over a nonarchimedean local field. -/
def FiniteAlgebraUpperTriangularCartanStatement.{uF, uE} : Prop :=
  ∀ (n : ℕ) (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type uE) [CommRing E] [Algebra F E]
    [Module.Finite F E] [IsReduced E] [TopologicalSpace E] [IsModuleTopology F E],
    HasUpperTriangularCartanContraction n E

/-- The Artinian decomposition is a topological product of local fields
when the factors have their spectral topologies. -/
theorem finiteAlgebraUpperTriangularCartan : FiniteAlgebraUpperTriangularCartanStatement.{u, v} := by
  intro n F _ _ _ _ E _ _ _ _ _ _
  let _ : IsArtinianRing E := IsArtinianRing.of_finite F E
  let S (i : MaximalSpectrum E) := E ⧸ i.asIdeal
  let _ (i : MaximalSpectrum E) : Field (S i) := IsArtinianRing.fieldOfSubtypeIsMaximal E i
  let _ (i : MaximalSpectrum E) : Algebra F (S i) :=
    inferInstanceAs (Algebra F (E ⧸ i.asIdeal))
  have (i : MaximalSpectrum E) : IsScalarTower F E (S i) :=
    inferInstanceAs (IsScalarTower F E (E ⧸ i.asIdeal))
  have (i : MaximalSpectrum E) : FiniteDimensional F (S i) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F i.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  let _ := LocalGalois.localNormedField F
  have := LocalGalois.localNormedField_complete F
  let normedS (i : MaximalSpectrum E) : NontriviallyNormedField (S i) :=
    LocalField.FiniteExtension.normedField F (S i)
  let _ (i : MaximalSpectrum E) : TopologicalSpace (S i) :=
    (normedS i).toNormedField.toUniformSpace.toTopologicalSpace
  let _ (i : MaximalSpectrum E) : NormedAlgebra F (S i) :=
    LocalField.FiniteExtension.normedAlgebra F (S i)
  let _ (i : MaximalSpectrum E) : ValuativeRel (S i) :=
    LocalField.FiniteExtension.valuativeRel F (S i)
  have (i : MaximalSpectrum E) : IsNonarchimedeanLocalField (S i) :=
    LocalField.FiniteExtension.isLocalField F (S i)
  have (i : MaximalSpectrum E) : IsModuleTopology F (S i) := isModuleTopologyOfFiniteDimensional
  have := IsModuleTopology.toContinuousAdd F E
  let e : E ≃ₐ[F] ∀ i, S i := (IsArtinianRing.equivPi E).restrictScalars F
  exact hasUpperTriangularCartanContraction_of_pi n e.toRingEquiv
    (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap)
    (fun i => hasUpperTriangularCartanContraction_localField n (S i))

end Langlands.GeneralLinear
