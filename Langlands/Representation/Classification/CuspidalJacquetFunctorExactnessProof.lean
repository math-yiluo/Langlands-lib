import Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessStatement
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.Group.GL.InverseTransposeIwahoriProof

noncomputable section

open CategoryTheory Representation

namespace Langlands.CuspidalJacquetMultiplicity

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- Inverse transpose transfers upper-radical finite containment to the
actual opposite ambient radical. -/
theorem oppositeUnipotent_finite_containment :
    letI := T.topology
    ∀ s : Finset (B.oppositeUnipotentSubgroup F.Carrier),
      ∃ K : OpenSubgroup (B.oppositeUnipotentSubgroup F.Carrier),
        IsCompact (K : Set (B.oppositeUnipotentSubgroup F.Carrier)) ∧
        ∀ u ∈ s, u ∈ K := by
  classical
  let := T.topology
  intro s
  let e₀ : B.oppositeUnipotentSubgroup F.Carrier ≃ₜ*
      B.unipotentSubgroup F.Carrier :=
    { toFun := fun g => ⟨GeneralLinear.inverseTranspose n F.Carrier g.val,
        (B.inverseTranspose_mem_unipotentSubgroup_iff F.Carrier g.val).mpr g.property⟩
      invFun := fun g => ⟨GeneralLinear.inverseTranspose n F.Carrier g.val,
        (B.inverseTranspose_mem_oppositeUnipotentSubgroup_iff F.Carrier g.val).mpr
          g.property⟩
      left_inv := by
        intro g
        apply Subtype.ext
        exact GeneralLinear.inverseTranspose_involutive n F.Carrier g.val
      right_inv := by
        intro g
        apply Subtype.ext
        exact GeneralLinear.inverseTranspose_involutive n F.Carrier g.val
      map_mul' := by
        intro g h
        apply Subtype.ext
        exact map_mul (GeneralLinear.inverseTranspose n F.Carrier) g.val h.val
      continuous_toFun := ((T.generalLinearInverseTranspose n).continuous.comp
        continuous_subtype_val).subtype_mk _
      continuous_invFun := ((T.generalLinearInverseTranspose n).continuous.comp
        continuous_subtype_val).subtype_mk _ }
  let e := e₀.trans (B.unipotentRadicalAmbientEquiv F.Carrier).symm
  obtain ⟨K, hK, hs⟩ := Parabolic.unipotentFiniteContainment F T B (s.image e)
  refine ⟨OpenSubgroup.comap e.toMonoidHom e.continuous K, ?_, ?_⟩
  · exact e.toHomeomorph.isClosedEmbedding.isCompact_preimage hK
  · intro u hu
    exact hs _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)

instance upperFunctor_additive :
    letI := T.generalLinearTopology n
    (upperFunctor.{uF, uV} T B).Additive := by
  let := T.generalLinearTopology n
  refine ⟨?_⟩
  intro A C f g
  ext x
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective A.representation x
  change B.jacquetMk C.representation
    ((SmoothRep.hom f) v + (SmoothRep.hom g) v) = _
  exact map_add (B.jacquetMk C.representation) _ _

instance upperFunctor_preservesMonomorphisms :
    letI := T.generalLinearTopology n
    (upperFunctor.{uF, uV} T B).PreservesMonomorphisms := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  refine ⟨?_⟩
  intro A C f hf
  apply (Rep.mono_iff_injective _).mpr
  change Function.Injective (T.normalizedJacquetMap B (SmoothRep.hom f)).toLinearMap
  rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
  exact coinvariants_map_injective_of_smooth (Parabolic.unipotentFiniteContainment F T B)
    _ ((SmoothRep.mono_iff_injective f).mp hf)
    (Parabolic.isSmooth_radical F T B C.representation C.isSmooth)

instance upperFunctor_preservesEpimorphisms :
    letI := T.generalLinearTopology n
    (upperFunctor.{uF, uV} T B).PreservesEpimorphisms := by
  let := T.generalLinearTopology n
  refine ⟨?_⟩
  intro A C f hf
  apply (Rep.epi_iff_surjective _).mpr
  change Function.Surjective (T.normalizedJacquetMap B (SmoothRep.hom f)).toLinearMap
  rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
  exact coinvariants_map_surjective _ ((SmoothRep.epi_iff_surjective f).mp hf)

instance oppositeFunctor_additive :
    letI := T.generalLinearTopology n
    (oppositeFunctor.{uF, uV} T B).Additive := by
  let := T.generalLinearTopology n
  refine ⟨?_⟩
  intro A C f g
  ext x
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective A.representation
    (B.oppositeUnipotentSubgroup F.Carrier) x
  change Jacquet.mk C.representation (B.oppositeUnipotentSubgroup F.Carrier)
    ((SmoothRep.hom f) v + (SmoothRep.hom g) v) = _
  exact map_add (Jacquet.mk C.representation
    (B.oppositeUnipotentSubgroup F.Carrier)) _ _

instance oppositeFunctor_preservesMonomorphisms :
    letI := T.generalLinearTopology n
    (oppositeFunctor.{uF, uV} T B).PreservesMonomorphisms := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  refine ⟨?_⟩
  intro A C f hf
  apply (Rep.mono_iff_injective _).mpr
  change Function.Injective (Coinvariants.map _ _
    (Jacquet.restrictMap (SmoothRep.hom f) (B.oppositeUnipotentSubgroup F.Carrier)))
  exact coinvariants_map_injective_of_smooth (oppositeUnipotent_finite_containment T B)
    _ ((SmoothRep.mono_iff_injective f).mp hf)
    (isSmooth_comp _ continuous_subtype_val C.isSmooth)

instance oppositeFunctor_preservesEpimorphisms :
    letI := T.generalLinearTopology n
    (oppositeFunctor.{uF, uV} T B).PreservesEpimorphisms := by
  let := T.generalLinearTopology n
  refine ⟨?_⟩
  intro A C f hf
  apply (Rep.epi_iff_surjective _).mpr
  change Function.Surjective (Coinvariants.map _ _
    (Jacquet.restrictMap (SmoothRep.hom f) (B.oppositeUnipotentSubgroup F.Carrier)))
  exact coinvariants_map_surjective _ ((SmoothRep.epi_iff_surjective f).mp hf)

end Langlands.CuspidalJacquetMultiplicity

namespace Langlands

universe uF uV

/-- Additivity and mono/epi preservation for both actual Jacquet functors. -/
theorem cuspidalJacquetFunctorExactness :
    CuspidalJacquetFunctorExactnessStatement.{uF, uV} := by
  intro p hp F T n B
  let := T.generalLinearTopology n
  exact ⟨inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance⟩

end Langlands
