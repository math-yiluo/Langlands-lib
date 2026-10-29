import Langlands.Algebra.LocalAlgebraTowerConstruction
import Langlands.Algebra.LocalAlgebraApproximationExistenceProof
import Langlands.Algebra.LocalModuleApproximationReduction
import Langlands.Algebra.LocalModuleTowerApproximationExistenceStatement

/-! # Existence of simultaneous local tower approximations, proof -/

universe uI uA uB uC uR uS uT u v w z

namespace Langlands.Algebra

namespace LocalAlgebraTowerSystem

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} {T : Type uT} [CommRing R] [CommRing S] [CommRing T]
  [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S T)]
  (D : LocalAlgebraTowerSystem.{uI, uA, uB, uC} ι R S T)

/-- The restriction of a synchronized tower to the indices above `i₀`, with the same rings,
transitions and cocone maps. Its lower arrow is `D.rs.tail i₀`. -/
def tail (i₀ : ι) : LocalAlgebraTowerSystem.{uI, uA, uB, uC} {j : ι // i₀ ≤ j} R S T where
  rs := D.rs.tail i₀
  top j := D.top j.1
  upperAlgebra j := D.upperAlgebra j.1
  upper_local j := D.upper_local j.1
  topMap j k h := D.topMap j.1 k.1 h
  top_directed :=
    { map_self := by
        intro j x
        exact DirectedSystem.map_self' D.topMap x
      map_map := by
        intro k j i hij hjk x
        exact DirectedSystem.map_map' D.topMap hij hjk x }
  topMap_local j k h := D.topMap_local j.1 k.1 h
  topMap_comm j k h s := D.topMap_comm j.1 k.1 h s
  topι j := D.topι j.1
  topι_local j := D.topι_local j.1
  topι_compat j k h t := D.topι_compat j.1 k.1 h t
  topι_comm j s := D.topι_comm j.1 s

/-- Restriction to a tail preserves the simultaneous ring approximation conditions. -/
theorem tail_isApproximation (hD : D.IsApproximation) (i₀ : ι) :
    (D.tail i₀).IsApproximation :=
  ⟨D.rs.tail_isApproximation hD.1 i₀,
    ⟨ringDirectLimit_lift_tail_bijective D.rs.algMap D.rs.algι D.rs.algι_compat hD.2.1.1 i₀,
      ringDirectLimit_lift_tail_bijective D.topMap D.topι D.topι_compat hD.2.1.2 i₀⟩,
    fun j ↦ hD.2.2.1 j.1, fun j k h ↦ hD.2.2.2.1 j.1 k.1 h, fun j k h ↦ hD.2.2.2.2 j.1 k.1 h⟩

/-- The upper arrow of an approximating tower is a ring approximation system for `S → T`. -/
theorem st_isApproximation (hD : D.IsApproximation) : D.st.IsApproximation := by
  refine ⟨hD.2.1, fun i ↦ ?_, hD.2.2.1, hD.2.2.2.1⟩
  have := hD.1.2.1 i
  have := hD.1.2.2.1 i
  exact _root_.Algebra.EssFiniteType.comp ℤ (D.rs.base i) (D.rs.alg i)

end LocalAlgebraTowerSystem

open LocalAlgebraApproximationExistence LocalAlgebraTowerApproximation in
/-- The construction for Stacks 00R7 before its flatness argument: for local algebra maps
`R → S → T` with `S` and `T` essentially finitely presented over `R` and a finitely presented
`T`-module `M`, there are one directed index, one synchronized tower of local ring
approximations and one upper module system satisfying all simultaneous approximation
conditions. -/
theorem localModuleTowerApproximationExistence :
    LocalModuleTowerApproximationExistenceStatement.{u, v, w, z} := by
  intro R S T M _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS hT hM
  have : IsLocalHom (algebraMap R (ULift.{max w z} S)) := by
    refine ⟨fun r hr ↦ IsUnit.of_map (algebraMap R S) r ?_⟩
    have := hr.map (ULift.algEquiv : ULift.{max w z} S ≃ₐ[R] S)
    rwa [AlgEquiv.commutes] at this
  have hS' : EssFinitePresentation R (ULift.{max w z} S) := by
    obtain ⟨n, I, hI, P, ⟨e⟩⟩ := hS
    exact ⟨n, I, hI, P, ⟨e.trans ULift.algEquiv.symm⟩⟩
  -- The ring system for `R → S` (Stacks 00QV), with all carriers in the common universe.
  obtain ⟨ι, _, _, _, D₀, hD₀⟩ :=
    localAlgebraApproximationExistence.{u, max v w z} R (ULift.{max w z} S) hS'
  let D₁ := D₀.mapAlgEquiv (ULift.algEquiv : ULift.{max w z} S ≃ₐ[R] S)
  have hD₁ : D₁.IsApproximation := D₀.mapAlgEquiv_isApproximation _ hD₀
  -- The upper stages over a tail of that system.
  obtain ⟨P⟩ := nonempty_pres_upper_of_essFinitePresentation hS hT
  obtain ⟨i₀, ⟨L⟩⟩ := exists_relLift D₁ hD₁.1.2.2 P
  have hD₂ : L.tower.IsApproximation :=
    L.tower_isApproximation (D₁.tail_isApproximation hD₁ i₀)
  -- The module system (Stacks 00QX) over the upper arrow, on a further tail.
  have := hM
  obtain ⟨n, m, A, ⟨eA⟩⟩ := exists_matrix_presentation T M
  have hst := L.tower.st_isApproximation hD₂
  obtain ⟨i₁, a, ha⟩ := L.tower.st.exists_algι_eq_fun hst.1.2.2
    (fun p : Fin n × Fin m ↦ A p.1 p.2)
  have ha' : (Matrix.of fun r c ↦ a (r, c)).map (L.tower.st.algι i₁) = A := by
    ext r c
    exact ha (r, c)
  have hE := (L.tower.st.presentationSystem A i₁ _ ha').mapLinearEquiv_isApproximation eA
    (L.tower.st.presentationSystem_isApproximation hst A i₁ _ ha')
  exact ⟨_, inferInstance, inferInstance, inferInstance, L.tower.tail i₁,
    ⟨(L.tower.st.presentationSystem A i₁ _ ha').mapLinearEquiv eA⟩,
    L.tower.tail_isApproximation hD₂ i₁, hE.1.2, hE.2.2.2.1, hE.2.2.2.2.2⟩

end Langlands.Algebra
