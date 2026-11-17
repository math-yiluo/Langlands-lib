import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCompletedResidueStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteJointImage
import Langlands.Geometry.Analytic.StrictTestDomain.FibreComparison
import Langlands.Geometry.Analytic.ValuedField.SeparatedTensor

/-! # Canonical completed residue comparison for full affinoid domains -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K} {i : BoundedAlgHom K A B}
  {U : Set (BanachSpectrum A)}

/-- The full affinoid-test property also gives uniqueness of bounded maps
to every complete ultrametric normed commutative algebra. -/
theorem Represents.eq_of_comp_eq (hU : Represents K i U)
    {L : Type v} [NormedCommRing L] [NormedAlgebra K L]
    [IsUltrametricDist L] [CompleteSpace L]
    (f g : BoundedAlgHom K B L) (h : f.comp i = g.comp i) : f = g := by
  let D := finiteJointImage f g
  have hcomp : D.left.comp i = D.right.comp i := D.comp_eq i i h
  have himage : HasImageIn K (D.left.comp i) U := by
    intro z
    have hpoint : comap (D.left.comp i).toBoundedRingHom z =
        comap i.toBoundedRingHom (comap D.left.toBoundedRingHom z) :=
      BanachSpectrum.ext fun _ => rfl
    rw [hpoint]
    exact hU.hasImageIn _
  have hmaps : D.left = D.right :=
    (hU.2.2 D.algebra (D.left.comp i) himage).unique rfl hcomp.symm
  calc
    f = D.embed.comp D.left := D.embed_left.symm
    _ = D.embed.comp D.right := congrArg (fun η => D.embed.comp η) hmaps
    _ = g := D.embed_right

/-- The diagonal tensor test places every original-algebra residue value in
the image of the canonical completed residue-field map. -/
theorem Represents.completedResidueMap_mem_range (hU : Represents K i U)
    (y : BanachSpectrum B) (b : B) :
    completedResidueMap K y b ∈ Set.range (completedResidueComap K i y) := by
  let F := CompletedResidueField K (comap i.toBoundedRingHom y)
  let E := CompletedResidueField K y
  let φ : BoundedAlgHom K F E := completedResidueComap K i y
  let instFE : Algebra F E := φ.toAlgHom.toRingHom.toAlgebra
  have hφ (z : F) : ‖φ z‖ = ‖z‖ :=
    (isometry_completedResidueComap K i y).norm_map_of_map_zero (map_zero φ.toAlgHom) z
  let : NormedAlgebra F E :=
    { instFE with
      norm_smul_le := fun z e => by
        rw [Algebra.smul_def, norm_mul]
        exact le_of_eq (congrArg (fun r : ℝ => r * ‖e‖) (hφ z)) }
  let W := UniformSpace.Completion (SeparatedFieldTensor.NormedTensor F E E)
  let τ : E ⊗[F] E →ₐ[F] W := SeparatedFieldTensor.toCompletion F E E
  have hτ : Function.Injective τ := SeparatedFieldTensor.toCompletion_injective F E E
  have hτn (e e' : E) : ‖τ (e ⊗ₜ[F] e')‖ ≤ ‖e‖ * ‖e'‖ :=
    SeparatedFieldTensor.norm_toCompletion_tmul_le F E E e e'
  let instKW : Algebra K W :=
    ((algebraMap F W).comp (algebraMap K F)).toAlgebra
  let : NormedAlgebra K W :=
    { instKW with
      norm_smul_le := fun k w => by
        change ‖algebraMap F W (algebraMap K F k) * w‖ ≤ ‖k‖ * ‖w‖
        rw [← Algebra.smul_def]
        exact (norm_smul_le _ _).trans_eq (by rw [norm_algebraMap']) }
  let f : BoundedAlgHom K B W :=
    { toRingHom := τ.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom.comp
        (completedResidueMap K y).toAlgHom.toRingHom)
      commutes' := fun k => by
        change τ ((completedResidueMap K y).toAlgHom (algebraMap K B k) ⊗ₜ[F]
            (1 : E)) = algebraMap F W (algebraMap K F k)
        rw [(completedResidueMap K y).toAlgHom.commutes, ← φ.toAlgHom.commutes]
        change τ (algebraMap F E (algebraMap K F k) ⊗ₜ[F] (1 : E)) = _
        rw [← Algebra.TensorProduct.algebraMap_apply]
        exact τ.commutes _
      bounded := ⟨1, one_pos, fun q => by
        change ‖τ ((completedResidueMap K y).toAlgHom q ⊗ₜ[F] (1 : E))‖ ≤ 1 * ‖q‖
        refine (hτn _ _).trans ?_
        rw [norm_one, mul_one, one_mul]
        exact (norm_completedResidueMap K y q).trans_le (y.le_norm q)⟩ }
  let g : BoundedAlgHom K B W :=
    { toRingHom := τ.toRingHom.comp
        ((Algebra.TensorProduct.includeRight : E →ₐ[F] E ⊗[F] E).toRingHom.comp
          (completedResidueMap K y).toAlgHom.toRingHom)
      commutes' := fun k => by
        change τ ((1 : E) ⊗ₜ[F] (completedResidueMap K y).toAlgHom
            (algebraMap K B k)) = algebraMap F W (algebraMap K F k)
        rw [(completedResidueMap K y).toAlgHom.commutes, ← φ.toAlgHom.commutes]
        change τ ((1 : E) ⊗ₜ[F] algebraMap F E (algebraMap K F k)) = _
        rw [← Algebra.TensorProduct.algebraMap_apply']
        exact τ.commutes _
      bounded := ⟨1, one_pos, fun q => by
        change ‖τ ((1 : E) ⊗ₜ[F] (completedResidueMap K y).toAlgHom q)‖ ≤ 1 * ‖q‖
        refine (hτn _ _).trans ?_
        rw [norm_one, one_mul, one_mul]
        exact (norm_completedResidueMap K y q).trans_le (y.le_norm q)⟩ }
  have hcomp : f.comp i = g.comp i := by
    apply BoundedAlgHom.ext
    intro a
    change τ ((completedResidueMap K y).toAlgHom (i a) ⊗ₜ[F] (1 : E)) =
      τ ((1 : E) ⊗ₜ[F] (completedResidueMap K y).toAlgHom (i a))
    rw [← completedResidueComap_map K i y a]
    change τ (algebraMap F E (completedResidueMap K (comap i.toBoundedRingHom y) a)
        ⊗ₜ[F] (1 : E)) =
      τ ((1 : E) ⊗ₜ[F]
        algebraMap F E (completedResidueMap K (comap i.toBoundedRingHom y) a))
    rw [← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  have hfg : f = g := hU.eq_of_comp_eq f g hcomp
  have htensor : completedResidueMap K y b ⊗ₜ[F] (1 : E) =
      (1 : E) ⊗ₜ[F] completedResidueMap K y b :=
    hτ (congrArg (fun η : BoundedAlgHom K B W => η b) hfg)
  obtain ⟨z, hz⟩ := FieldTensor.mem_range_of_tmul_eq htensor
  exact ⟨z, hz⟩

/-- A full domain representation induces a surjective canonical completed
residue-field map at every spectrum point. -/
theorem domainCompletedResidueSurjectivity :
    DomainCompletedResidueSurjectivityStatement.{u} := by
  intro K _ _ _ A B i U hU y z
  have hclosed : IsClosed (Set.range (completedResidueComap K i y)) :=
    (isometry_completedResidueComap K i y).isClosedEmbedding.isClosed_range
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hclosed
  | ih a =>
    obtain ⟨b, c, _hc, ha⟩ := IsFractionRing.div_surjective (ResidueDomain y) a.ofAbs
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := y.kernel) b
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (I := y.kernel) c
    have ha' : a = residueFieldMap K y b / residueFieldMap K y c :=
      (WithAbs.equiv (fractionAbsoluteValue K y)).injective ha.symm
    rw [ha']
    rw [show ((residueFieldMap K y b / residueFieldMap K y c :
        NormedResidueField K y) : CompletedResidueField K y) =
        (residueFieldMap K y b : CompletedResidueField K y) /
          (residueFieldMap K y c : CompletedResidueField K y) from
      map_div₀ (UniformSpace.Completion.coeRingHom :
        NormedResidueField K y →+* CompletedResidueField K y) _ _]
    change completedResidueMap K y b / completedResidueMap K y c ∈
      Set.range (completedResidueComap K i y)
    obtain ⟨b', hb⟩ := hU.completedResidueMap_mem_range y b
    obtain ⟨c', hc⟩ := hU.completedResidueMap_mem_range y c
    exact ⟨b' / c', by rw [map_div₀, hb, hc]⟩

end Langlands.Analytic.PresentedAffinoidAlgebra
