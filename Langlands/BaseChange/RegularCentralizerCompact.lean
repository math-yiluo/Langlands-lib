import Langlands.BaseChange.CompactCentralizerNormalization
import Langlands.BaseChange.NormCentralizer
import Langlands.BaseChange.RegularCyclicBasis
import Langlands.LocalField.FiniteExtension
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! The largest compact open subgroups of the regular centralizers used in base change. -/

noncomputable section

namespace Langlands.BaseChange

open Matrix _root_.Polynomial _root_.Topology
open Langlands.JacquetLanglands

universe u v

/-- The units of a finite reduced algebra with the module topology have a largest compact
open subgroup. -/
theorem HasLargestCompactOpenSubgroup.finiteAlgebraUnits
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (A : Type v) [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A]
    [TopologicalSpace A] [IsModuleTopology F A] :
    HasLargestCompactOpenSubgroup Aˣ := by
  let : IsArtinianRing A := IsArtinianRing.of_finite F A
  let : IsTopologicalRing A := IsModuleTopology.isTopologicalRing F A
  let K (I : MaximalSpectrum A) := A ⧸ I.asIdeal
  let _ (I : MaximalSpectrum A) : Field (K I) := Ideal.Quotient.field I.asIdeal
  let _ (I : MaximalSpectrum A) : Module.Finite F (K I) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom F A (K I)).toLinearMap
      Ideal.Quotient.mk_surjective
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let _ (I : MaximalSpectrum A) : NontriviallyNormedField (K I) :=
    LocalField.FiniteExtension.normedField F (K I)
  let _ (I : MaximalSpectrum A) : TopologicalSpace (K I) :=
    (LocalField.FiniteExtension.normedField F (K I)).toUniformSpace.toTopologicalSpace
  let _ (I : MaximalSpectrum A) : NormedAlgebra F (K I) :=
    LocalField.FiniteExtension.normedAlgebra F (K I)
  let _ (I : MaximalSpectrum A) : IsModuleTopology F (K I) :=
    isModuleTopologyOfFiniteDimensional
  let e : A ≃ₐ[F] (∀ I, K I) := (IsArtinianRing.equivPi A).restrictScalars F
  let eTop : A ≃ₜ* (∀ I, K I) :=
    { e.toRingEquiv.toMulEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearEquiv.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearEquiv.toLinearMap }
  let eUnits := (Units.mapContinuousMulEquiv eTop).trans ContinuousMulEquiv.piUnits
  apply HasLargestCompactOpenSubgroup.of_isClosedEmbedding _ eUnits.toMonoidHom
    eUnits.toHomeomorph.isClosedEmbedding
  apply HasLargestCompactOpenSubgroup.pi
  intro I
  let : ValuativeRel (K I) := LocalField.FiniteExtension.valuativeRel F (K I)
  let : IsNonarchimedeanLocalField (K I) := LocalField.FiniteExtension.isLocalField F (K I)
  exact HasLargestCompactOpenSubgroup.localFieldUnits (K I)

private theorem adjoinRoot_isReduced_of_squarefree {F : Type*} [Field F] (p : F[X])
    (hp : Squarefree p) : IsReduced (AdjoinRoot p) := by
  constructor
  intro a ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  obtain ⟨k, hk⟩ := ha
  have hpow : AdjoinRoot.mk p (q ^ (k + 1)) = 0 := by
    rw [map_pow, pow_succ, hk, zero_mul]
  exact AdjoinRoot.mk_eq_zero.mpr ((hp.dvd_pow_iff_dvd (Nat.succ_ne_zero k)).mp
    (AdjoinRoot.mk_eq_zero.mp hpow))

/-- An ordinary regular semisimple centralizer has a largest compact open subgroup. -/
def RegularCentralizerCompactStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (γ : GeneralLinear n F),
    IsRegularSemisimple γ → HasLargestCompactOpenSubgroup (glCentralizer γ)

set_option maxHeartbeats 600000 in
theorem regularCentralizer_hasLargestCompactOpenSubgroup : RegularCentralizerCompactStatement.{u} := by
  intro F _ _ _ _ n γ hγ
  let p := minpoly F γ.val
  let A := AdjoinRoot p
  let : Module.Finite F A := (minpoly.monic γ.val.isIntegral).finite_adjoinRoot
  let : IsReduced A := adjoinRoot_isReduced_of_squarefree p
    ((show γ.val.charpoly.Separable from hγ).squarefree.squarefree_of_dvd
      (Matrix.minpoly_dvd_charpoly γ.val))
  let : TopologicalSpace A := moduleTopology F A
  let : IsModuleTopology F A := ⟨rfl⟩
  let : IsTopologicalRing A := IsModuleTopology.isTopologicalRing F A
  let : T2Space A := (finiteAlgebraTopology F A).1
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let eval : A →ₐ[F] Matrix (Fin n) (Fin n) F :=
    Ideal.Quotient.liftₐ _ (aeval γ.val) fun q hq =>
      minpoly.dvd_iff.mp (Ideal.mem_span_singleton.mp hq)
  have heval (q : F[X]) : eval (AdjoinRoot.mk p q) = aeval γ.val q := rfl
  have hinj : Function.Injective eval := by
    apply (injective_iff_map_eq_zero eval).mpr
    intro a ha
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [heval] at ha
    exact AdjoinRoot.mk_eq_zero.mpr (minpoly.dvd F γ.val ha)
  have hemb : IsClosedEmbedding eval :=
    LinearMap.isClosedEmbedding_of_injective (f := eval.toLinearMap)
      (LinearMap.ker_eq_bot.mpr hinj)
  let f : Aˣ →* GeneralLinear n F := Units.map eval.toRingHom.toMonoidHom
  have hf : IsClosedEmbedding f := hemb.units_map
  have hmem (x : Aˣ) : f x ∈ glCentralizer γ := by
    rw [glCentralizer_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    obtain ⟨q, hq⟩ := AdjoinRoot.mk_surjective x.val
    change eval x.val * γ.val = γ.val * eval x.val
    rw [← hq, heval]
    simpa only [aeval_X] using ((Commute.all q X).map (aeval γ.val)).eq
  let fC := f.codRestrict (glCentralizer γ) hmem
  obtain ⟨v, hv⟩ := regularCyclicBasis F n γ.val hγ
  have preimage (c : glCentralizer γ) : ∃ a : A, eval a = c.val.val := by
    have hc : Commute c.val γ :=
      (Subgroup.mem_centralizer_singleton_iff.mp (glCentralizer_eq_centralizer γ ▸ c.property))
    obtain ⟨d, hd⟩ := exists_sum_pow_of_commute hv (hc.map (Units.coeHom _))
    change c.val.val = ∑ j : Fin n, d j • γ.val ^ (j : ℕ) at hd
    refine ⟨AdjoinRoot.mk p (∑ j : Fin n, monomial (j : ℕ) (d j)), ?_⟩
    rw [heval, hd]
    simp only [map_sum, aeval_monomial, Algebra.smul_def]
  have hsurj : Function.Surjective fC := by
    intro c
    obtain ⟨a, ha⟩ := preimage c
    obtain ⟨b, hb⟩ := preimage c⁻¹
    have hab : a * b = 1 := hinj (by
      rw [map_mul, map_one, ha, hb]
      exact c.val.val_inv)
    have hba : b * a = 1 := hinj (by
      rw [map_mul, map_one, ha, hb]
      exact c.val.inv_val)
    exact ⟨⟨a, b, hab, hba⟩, Subtype.ext (Units.ext ha)⟩
  have hfC : IsEmbedding fC := IsEmbedding.subtypeVal.of_comp_iff.mp hf.isEmbedding
  let e := MulEquiv.ofBijective fC ⟨hfC.injective, hsurj⟩
  let eTop : Aˣ ≃ₜ* glCentralizer γ :=
    { e with
      continuous_toFun := hfC.continuous
      continuous_invFun := (e.toEquiv.toHomeomorphOfIsInducing hfC.isInducing).continuous_invFun }
  exact HasLargestCompactOpenSubgroup.of_isClosedEmbedding
    (HasLargestCompactOpenSubgroup.finiteAlgebraUnits F A) eTop.symm.toMonoidHom
    eTop.symm.toHomeomorph.isClosedEmbedding

/-- A twisted centralizer at a regular norm has a largest compact open subgroup. -/
theorem sigmaCentralizer_hasLargestCompactOpenSubgroup
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l n : ℕ} (hσ : IsCyclicAlgebra σ l)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ)
    (hassoc : IsNormAssociated σ l δ γ) : HasLargestCompactOpenSubgroup (sigmaCentralizer σ n δ) := by
  obtain ⟨x, hx⟩ := hassoc
  let e := normCentralizerEquiv hσ hγ x hx
  exact HasLargestCompactOpenSubgroup.of_isClosedEmbedding
    (regularCentralizer_hasLargestCompactOpenSubgroup F n γ hγ) e.symm.toMonoidHom
    e.symm.toHomeomorph.isClosedEmbedding

end Langlands.BaseChange
