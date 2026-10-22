import Langlands.Weil.Local.AssemblyStatement
import Langlands.ClassFieldTheory.Local.Galois
import Langlands.Topology.Nonarchimedean.Subgroup
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Algebra.Group.Pointwise

noncomputable section

namespace Langlands.Weil.Local

open Topology

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

theorem localResidueCardinality_eq :
    F.canonicalTopologicalData.residueCardinality = Nat.card (localResidueField F) := rfl

theorem localResidueMap_projection (w : localWeilGroup F) :
    localResidueMap F (localProjection F w) =
      Galois.FiniteField.geometricFrobenius (localResidueField F) ^ localDegreeInt F w := by
  let e := Galois.FiniteField.profiniteEquivalence (localResidueField F)
  have hw : e (localResidueMap F (localProjection F w)) =
      frobenius (localDegree F w) := w.property
  calc
    localResidueMap F (localProjection F w) =
        e.symm (e (localResidueMap F (localProjection F w))) :=
      (e.symm_apply_apply _).symm
    _ = e.symm (frobenius (localDegree F w)) := congrArg e.symm hw
    _ = _ := Galois.FiniteField.profiniteEquivalence_symm_frobenius
      (localResidueField F) (localDegree F w)

theorem localProjection_injective : Function.Injective (localProjection F) :=
  projection_injective (localResidueDegree F)

theorem localResidueDegree_isOpenMap : IsOpenMap (localResidueDegree F) :=
  (Galois.FiniteField.profiniteEquivalence (localResidueField F)).toHomeomorph.isOpenMap.comp
    (F.absoluteResidueHom_isOpenMap F.canonicalTopologicalData)

theorem localProjection_denseRange : DenseRange (localProjection F) := by
  have hr : Set.range (localProjection F) =
      (localResidueDegree F) ⁻¹' Set.range frobenius := by
    exact congrArg (fun S : Subgroup (Field.absoluteGaloisGroup F.Carrier) =>
      (S : Set (Field.absoluteGaloisGroup F.Carrier)))
      (projection_range (localResidueDegree F))
  change Dense (Set.range (localProjection F))
  rw [hr]
  exact (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree)).preimage
    (localResidueDegree_isOpenMap F)

theorem localInertia_eq_comap :
    localInertia F =
      (F.absoluteInertia F.canonicalTopologicalData).comap (localProjection F).toMonoidHom := by
  rw [← localResidueDegree_ker F]
  ext w
  change localDegree F w = 1 ↔ localResidueDegree F (localProjection F w) = 1
  rw [show localResidueDegree F (localProjection F w) =
    frobenius (localDegree F w) from w.property, ← map_one frobenius]
  exact frobenius_injective.eq_iff.symm

theorem localInertiaInclusion_range :
    Set.range (localInertiaInclusion F) = (localInertia F : Set (localWeilGroup F)) := by
  have hr : Set.range (localInertiaInclusion F) =
      Set.range (inertiaInclusion (localResidueDegree F)) := by
    change Set.range (inertiaInclusion (localResidueDegree F) ∘ localGaloisInertiaEquiv F) = _
    rw [Set.range_comp, (localGaloisInertiaEquiv F).surjective.range_eq, Set.image_univ]
  rw [hr]
  exact congrArg (fun S : Subgroup (localWeilGroup F) => (S : Set (localWeilGroup F)))
    (inertiaInclusion_range (localResidueDegree F))

theorem localInertiaInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding (localInertiaInclusion F) :=
  (topologyProperties (Field.absoluteGaloisGroup F.Carrier)
    (localResidueDegree F)).2.1.comp
      (localGaloisInertiaEquiv F).toHomeomorph.isOpenEmbedding

theorem localInertia_isOpen : IsOpen (localInertia F : Set (localWeilGroup F)) :=
  (topologyProperties (Field.absoluteGaloisGroup F.Carrier)
    (localResidueDegree F)).2.2.1

theorem localInertia_isCompact : IsCompact (localInertia F : Set (localWeilGroup F)) := by
  let := F.absoluteInertia_compactSpace F.canonicalTopologicalData
  rw [← localInertiaInclusion_range F]
  exact isCompact_range (localInertiaInclusion F).continuous

/-- The original inertia topology agrees with the degree-kernel topology. -/
def localInertiaEquiv :
    localInertia F ≃ₜ* F.absoluteInertia F.canonicalTopologicalData := by
  let forward : localInertia F → F.absoluteInertia F.canonicalTopologicalData :=
    fun i => ⟨localProjection F i, by
      change i.val ∈ (F.absoluteInertia F.canonicalTopologicalData).comap
        (localProjection F).toMonoidHom
      rw [← localInertia_eq_comap F]
      exact i.property⟩
  let backward : F.absoluteInertia F.canonicalTopologicalData → localInertia F :=
    fun i => ⟨localInertiaInclusion F i, by
      change localDegree F (localInertiaInclusion F i) = 1
      rfl⟩
  let e : localInertia F ≃* F.absoluteInertia F.canonicalTopologicalData :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro i
        apply Subtype.ext
        apply localProjection_injective F
        rfl
      right_inv := by
        intro i
        apply Subtype.ext
        rfl
      map_mul' := by
        intro i j
        exact Subtype.ext
          (map_mul (localProjection F) (i : localWeilGroup F) (j : localWeilGroup F)) }
  exact
    { toMulEquiv := e
      continuous_toFun :=
        ((localProjection F).continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (localInertiaInclusion F).continuous.subtype_mk _ }

theorem localInertiaEquiv_apply (i : localInertia F) :
    (localInertiaEquiv F i : Field.absoluteGaloisGroup F.Carrier) =
      localProjection F i := rfl

private theorem degree_nonarchimedean : NonarchimedeanGroup Degree where
  is_nonarchimedean U hU := by
    refine ⟨⟨⊥, isOpen_discrete _⟩, ?_⟩
    intro n hn
    have hn' : n = 1 := hn
    simpa only [hn'] using mem_of_mem_nhds hU

theorem localWeilGroup_nonarchimedean : NonarchimedeanGroup (localWeilGroup F) := by
  let := Langlands.LocalClassField.absoluteGaloisNonarchimedean F.Carrier
  let := degree_nonarchimedean
  exact Langlands.subgroupNonarchimedean (pullbackSubgroup (localResidueDegree F))

theorem localWeilGroup_locallyCompactSpace : LocallyCompactSpace (localWeilGroup F) :=
  (localInertia_isCompact F).locallyCompactSpace_of_mem_nhds_of_group
    ((localInertia_isOpen F).mem_nhds (localInertia F).one_mem)

theorem localWeilGroup_t2Space : T2Space (localWeilGroup F) := by
  let : T2Space (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure F.Carrier/F.Carrier))
  exact inferInstance

theorem localWeilGroup_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (localWeilGroup F) := by
  let := localWeilGroup_nonarchimedean F
  let := localWeilGroup_t2Space F
  exact inferInstance

theorem localGeometricFrobenius_residue :
    localResidueMap F (localProjection F (localGeometricFrobenius F)) =
      Galois.FiniteField.geometricFrobenius (localResidueField F) := by
  rw [localResidueMap_projection]
  change Galois.FiniteField.geometricFrobenius (localResidueField F) ^
    (localDegree F (localGeometricFrobenius F)).toAdd = _
  rw [localGeometricFrobenius_degree]
  exact zpow_one _

theorem localNormCharacter_apply (w : localWeilGroup F) :
    (localNormCharacter F w : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-localDegreeInt F w) :=
  residueNormCharacter_apply F.canonicalTopologicalData (localDegree F) w

theorem localNormCharacter_geometricFrobenius :
    (localNormCharacter F (localGeometricFrobenius F) : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ)⁻¹ :=
  residueNormCharacter_degree_one F.canonicalTopologicalData (localDegree F)
    (localGeometricFrobenius_degree F)

theorem localUnramifiedCharacter_on_inertia (z : ℂˣ) (i : localInertia F) :
    localUnramifiedCharacter F z i = 1 :=
  unramifiedCharacter_on_kernel (localDegree F) z i.property

theorem localUnramifiedCharacter_geometricFrobenius (z : ℂˣ) :
    localUnramifiedCharacter F z (localGeometricFrobenius F) = z :=
  unramifiedCharacter_degree_one (localDegree F) z (localGeometricFrobenius_degree F)

theorem localAssemblyProperties : LocalAssemblyProperties F := by
  exact ⟨localResidueCardinality_eq F, localResidueMap_projection F,
    localProjection_injective F, localProjection_denseRange F, localDegree_surjective F,
    localInertia_eq_comap F, localInertiaInclusion_range F,
    localInertiaInclusion_isOpenEmbedding F, localInertia_isOpen F, localInertia_isCompact F,
    inferInstance, ⟨localInertiaEquiv F, localInertiaEquiv_apply F⟩,
    localWeilGroup_nonarchimedean F, localWeilGroup_locallyCompactSpace F,
    localWeilGroup_t2Space F, localWeilGroup_totallyDisconnectedSpace F,
    localGeometricFrobenius_degree F, localGeometricFrobenius_residue F,
    localNormCharacter_apply F, localNormCharacter_geometricFrobenius F,
    localUnramifiedCharacter_on_inertia F, localUnramifiedCharacter_geometricFrobenius F⟩

theorem localAssembly : LocalAssemblyStatement.{u} := by
  intro p _ F
  exact localAssemblyProperties F

end Langlands.Weil.Local
