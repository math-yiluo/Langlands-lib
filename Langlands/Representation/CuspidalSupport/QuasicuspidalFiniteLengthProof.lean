import Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement
import Langlands.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly
import Langlands.Representation.CompactCoefficient.SemisimplicityProof
import Langlands.Representation.Smooth.FixedVectors.FiniteTypes
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section

namespace Langlands.CuspidalSupport

open scoped MonoidAlgebra
open Topology

universe uG uV

namespace QuasicuspidalFiniteLength

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Finite group-algebra generators have group orbits spanning the vector space. -/
theorem orbit_span_eq_top (ρ : Representation ℂ G V) {m : ℕ} (v : Fin m → ρ.asModule)
    (hv : Submodule.span ℂ[G] (Set.range v) = ⊤) :
    Submodule.span ℂ (Set.range (fun t : G × Fin m => ρ t.1 (ρ.asModuleEquiv (v t.2)))) = ⊤ := by
  let P : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ
        (Set.range (fun t : G × Fin m => ρ t.1 (ρ.asModuleEquiv (v t.2))))
      apply_mem_toSubmodule := by
        intro g w hw
        apply (show Submodule.span ℂ (Set.range
            (fun t : G × Fin m => ρ t.1 (ρ.asModuleEquiv (v t.2)))) ≤
            (Submodule.span ℂ (Set.range
              (fun t : G × Fin m => ρ t.1 (ρ.asModuleEquiv (v t.2))))).comap (ρ g) from ?_) hw
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨h, i⟩, rfl⟩
        change ρ g (ρ h (ρ.asModuleEquiv (v i))) ∈
          Submodule.span ℂ (Set.range (fun t : G × Fin m => ρ t.1 (ρ.asModuleEquiv (v t.2))))
        rw [← Module.End.mul_apply, ← map_mul]
        exact Submodule.subset_span ⟨(g * h, i), rfl⟩ }
  have hle : Submodule.span ℂ[G] (Set.range v) ≤ P.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change ρ.asModuleEquiv (v i) ∈ P.toSubmodule
    exact Submodule.subset_span ⟨(1, i), by simp⟩
  rw [hv] at hle
  have hP : P = ⊤ := by
    apply (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).injective
    exact top_unique hle
  exact congrArg Subrepresentation.toSubmodule hP

section Topological

variable [TopologicalSpace G] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]

/-- Finite generation and finite index after adjoining the center provide a
single compact open level generating the restricted representation. -/
theorem exists_fixedVectors_generating (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (H : OpenSubgroup G) [(H.toSubgroup ⊔ Subgroup.center G).FiniteIndex]
    [Module.Finite ℂ[G] ρ.asModule] :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K.toSubgroup ≤ H.toSubgroup ∧
      ∀ S : Subrepresentation (ρ.comp H.toSubgroup.subtype),
        fixedVectors ρ K.toSubgroup ≤ S.toSubmodule → S = ⊤ := by
  classical
  obtain ⟨m, v, hv⟩ := Module.Finite.exists_fin (R := ℂ[G]) (M := ρ.asModule)
  let J := H.toSubgroup ⊔ Subgroup.center G
  let w : (G ⧸ J) × Fin m → V := fun t => ρ t.1.out⁻¹ (ρ.asModuleEquiv (v t.2))
  obtain ⟨K, hK, hKH, hw⟩ := exists_compactOpen_fixing_finite ρ hρ w
    (H : Set G) H.mem_nhds_one
  refine ⟨K, hK, hKH, ?_⟩
  intro S hS
  have horbit : ∀ t : G × Fin m, ρ t.1 (ρ.asModuleEquiv (v t.2)) ∈ S := by
    rintro ⟨g, i⟩
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul J g⁻¹
    obtain ⟨h, hh, z, hz, hhz⟩ := Subgroup.mem_sup_of_normal_right.mp j.property
    let q : G ⧸ J := QuotientGroup.mk g⁻¹
    have hg : g = h * z * q.out⁻¹ := by
      change g = h * z * (QuotientGroup.mk g⁻¹ : G ⧸ J).out⁻¹
      rw [hj, hhz]
      group
    have hzw : ρ z (w (q, i)) ∈ fixedVectors ρ K.toSubgroup := by
      intro k
      change ρ (k : G) (ρ z (w (q, i))) = ρ z (w (q, i))
      rw [← Module.End.mul_apply, ← map_mul,
        (Subgroup.mem_center_iff.mp hz (k : G)), map_mul, Module.End.mul_apply]
      exact congrArg (ρ z) (hw (q, i) k)
    have hmem := S.apply_mem_toSubmodule ⟨h, hh⟩ (hS hzw)
    change ρ h (ρ z (ρ q.out⁻¹ (ρ.asModuleEquiv (v i)))) ∈ S.toSubmodule at hmem
    change ρ g (ρ.asModuleEquiv (v i)) ∈ S.toSubmodule
    simpa only [hg, map_mul, Module.End.mul_apply] using hmem
  have hle := Submodule.span_le.mpr (Set.range_subset_iff.mpr horbit)
  rw [orbit_span_eq_top ρ v hv] at hle
  apply Subrepresentation.toSubmodule_injective
  exact top_unique hle

end Topological

/-- A finite-dimensional fixed-vector generating space supplies finitely many
group-algebra generators. -/
theorem finite_of_fixedVectors_generating (ρ : Representation ℂ G V) (H K : Subgroup G)
    [FiniteDimensional ℂ (fixedVectors ρ K)]
    (hgen : ∀ S : Subrepresentation (ρ.comp H.subtype),
      fixedVectors ρ K ≤ S.toSubmodule → S = ⊤) :
    Module.Finite ℂ[H] (Representation.asModule (ρ.comp H.subtype)) := by
  let σ : Representation ℂ H V := ρ.comp H.subtype
  let F := fixedVectors ρ K
  obtain ⟨m, w, hw⟩ := Module.Finite.exists_fin (R := ℂ) (M := F)
  let v : Fin m → σ.asModule := fun i => σ.asModuleEquiv.symm (w i : V)
  let P := Submodule.span ℂ[H] (Set.range v)
  let S := Subrepresentation.ofSubmodule' (ρ := σ) P
  have hS : S = ⊤ := by
    apply hgen
    have hle : Submodule.span ℂ (Set.range w) ≤ S.toSubmodule.comap F.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [hw] at hle
    intro x hx
    exact hle (show (⟨x, hx⟩ : F) ∈ (⊤ : Submodule ℂ F) from trivial)
  apply Module.Finite.of_fg_top
  apply Submodule.fg_def.mpr
  refine ⟨Set.range v, Set.finite_range v, ?_⟩
  change P = ⊤
  exact congrArg (fun T : Subrepresentation σ => T.asSubmodule) hS

/-- Restriction embeds the lattice of invariant subspaces, so finite length
over a subgroup implies finite length for the original group. -/
theorem finiteLength_of_restriction (ρ : Representation ℂ G V) (H : Subgroup G)
    (h : IsFiniteLength ℂ[H] (Representation.asModule (ρ.comp H.subtype))) :
    IsFiniteLength ℂ[G] ρ.asModule := by
  let eG := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let eH := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ.comp H.subtype)
  let i : Subrepresentation ρ ↪o Subrepresentation (ρ.comp H.subtype) :=
    { toFun := fun S => ⟨S.toSubmodule, fun h _ hv => S.apply_mem_toSubmodule h hv⟩
      inj' := fun S T h => Subrepresentation.toSubmodule_injective
        (congrArg (fun S : Subrepresentation (ρ.comp H.subtype) => S.toSubmodule) h)
      map_rel_iff' := Iff.rfl }
  let e := (eG.symm.toOrderEmbedding.comp i).comp eH.toOrderEmbedding
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  let : IsNoetherian ℂ[H] (Representation.asModule (ρ.comp H.subtype)) := hN
  let : IsArtinian ℂ[H] (Representation.asModule (ρ.comp H.subtype)) := hA
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_mk e.wellFoundedGT, e.wellFoundedLT⟩

end QuasicuspidalFiniteLength

/-- Finitely generated admissible quasicuspidal representations of every actual
standard product Levi have finite group-algebra length. -/
theorem leviQuasicuspidalFiniteLength.{uField, uCarrier} :
    LeviQuasicuspidalFiniteLengthStatement.{uField, uCarrier} := by
  intro p _ F T n B
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.leviT2Space B
  let := T.leviNonarchimedean B
  let := T.leviLocallyCompactSpace B
  intro A hAa hAc hAf
  let H := determinantUnitOpenSubgroup T B
  let : (H.toSubgroup ⊔ Subgroup.center (B.Levi F.Carrier)).FiniteIndex :=
    determinantUnit_sup_center_finiteIndex T B
  let : Module.Finite (MonoidAlgebra ℂ (B.Levi F.Carrier)) A.representation.asModule := hAf
  obtain ⟨K, _, _, hgen⟩ := QuasicuspidalFiniteLength.exists_fixedVectors_generating
    A.representation A.isSmooth H
  let : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) := hAa.2 K
  let : Module.Finite ℂ[H] (Representation.asModule (A.representation.comp H.toSubgroup.subtype)) :=
    QuasicuspidalFiniteLength.finite_of_fixedVectors_generating
      A.representation H.toSubgroup K.toSubgroup hgen
  let := determinantUnitNonarchimedean T B
  let := determinantUnitLocallyCompactSpace T B
  let : TotallySeparatedSpace (determinantUnitSubgroup T B) :=
    NonarchimedeanGroup.instTotallySeparated
  let : TotallyDisconnectedSpace (determinantUnitSubgroup T B) :=
    TotallySeparatedSpace.totallyDisconnectedSpace _
  let : MeasurableSpace (determinantUnitSubgroup T B) := borel _
  let : BorelSpace (determinantUnitSubgroup T B) := ⟨rfl⟩
  have hss := CompactCoefficientSemisimplicity.isSemisimpleRepresentation_of_compactCoefficients
    (MeasureTheory.Measure.haar (G := determinantUnitSubgroup T B))
    (determinantUnitRestriction T B A.representation)
    (isSmooth_determinantUnitRestriction T B A.isSmooth)
    ((leviHarishChandraTheorem p F T n B A).mp hAc)
  let : IsSemisimpleModule ℂ[H] (Representation.asModule (A.representation.comp H.toSubgroup.subtype)) :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hss
  apply QuasicuspidalFiniteLength.finiteLength_of_restriction A.representation H.toSubgroup
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end Langlands.CuspidalSupport
