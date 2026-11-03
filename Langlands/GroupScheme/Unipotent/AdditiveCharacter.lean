import Langlands.GroupScheme.Unipotent.PrimitiveCoordinate
import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Nontrivial additive characters of affine unipotent groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra Module
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding

variable {k : Type u} [Field k]
  {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A primitive element defines a one-coordinate primitive family on points. -/
theorem isPrimitiveFamily_of_isPrimitiveElem {b : B}
    (hb : letI := bialgebra e; Bialgebra.IsPrimitiveElem k b) :
    VectorGroup.IsPrimitiveFamily e (fun _ : Fin 1 => b) := by
  let := bialgebra e
  intro A x x' i
  rw [homEquiv_symm_mul, AlgHom.comp_apply,
    show AffineLinearEmbedding.comul e b = 1 ⊗ₜ[k] b + b ⊗ₜ[k] 1 from
      hb.comul_eq_tmul_add_tmul]
  simp only [map_add, Algebra.TensorProduct.productMap_apply_tmul, map_one,
    one_mul, mul_one]
  exact add_comm _ _

/-- The vector-group map of a nonzero one-coordinate primitive family is nonzero. -/
theorem quotientMap_ne_zero {b : B}
    (hy : VectorGroup.IsPrimitiveFamily e (fun _ : Fin 1 => b)) (hb : b ≠ 0) :
    VectorGroup.quotientMap hy ≠ 0 := by
  intro h0
  let x : (algSpec (CommRingCat.of k)).obj (op B) ⟶
      (Corepresented.groupScheme F e).X := 𝟙 _
  have h := Corepresented.groupSchemeMap_affinePoints e
    (VectorGroup.corepresentableBy (CommRingCat.of k) 1) (VectorGroup.coordinateMap hy) x
  change Corepresented.affinePointsEquiv _ _ B
    (x ≫ (VectorGroup.quotientMap hy).hom.hom) = _ at h
  rw [h0] at h
  change Corepresented.affinePointsEquiv _ _ B (x ≫ (1 : _ ⟶ _)) = _ at h
  rw [MonObj.comp_one, map_one] at h
  have hx : Corepresented.affinePointsEquiv F e B x = e.homEquiv (𝟙 B) := by
    change e.homEquiv (algSpec.fullyFaithful.preimage (𝟙 _)).unop = _
    rw [algSpec.fullyFaithful.preimage_id]
    rfl
  rw [hx] at h
  have h' := congrFun (congrArg Multiplicative.toAdd h) (0 : Fin 1)
  change 0 = (e.homEquiv.symm (e.homEquiv (𝟙 B))).hom b at h'
  rw [Equiv.symm_apply_apply] at h'
  exact hb h'.symm

/-- A corepresented group with no nonconstant coordinates is trivial on every test. -/
theorem range_id_eq_bot_of_all_mem_constants
    (hB : ∀ b : B, b ∈ k ∙ (1 : B)) :
    SubgroupFunctor.range (𝟙 (Corepresented.groupScheme F e)) = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro _
    apply (Subgroup.mem_bot).2
    apply (Corepresented.pointsEquiv F e T).injective
    rw [map_one]
    apply e.homEquiv.symm.injective
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hB b)
    simp
  · intro hx
    exact ⟨x, Category.comp_id x⟩

/-- Every nontrivial corepresented unipotent group has a nontrivial additive character. -/
theorem exists_additive_character_of_isUnipotent
    (hU : IsUnipotent (Corepresented.groupScheme F e))
    (hnt : SubgroupFunctor.range (𝟙 (Corepresented.groupScheme F e)) ≠ ⊥) :
    ∃ q : Corepresented.groupScheme F e ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1,
      q ≠ 0 := by
  classical
  have hconst : ∃ b : B, b ∉ k ∙ (1 : B) := by
    by_contra h
    exact hnt (range_id_eq_bot_of_all_mem_constants e (by simpa using h))
  let := bialgebra e
  obtain ⟨b, hb0, hb⟩ := exists_nonzero_primitive_of_oneMemStable
    (oneMemStable_of_isUnipotent e hU) hconst
  let hy := isPrimitiveFamily_of_isPrimitiveElem e hb
  exact ⟨VectorGroup.quotientMap hy, quotientMap_ne_zero e hy hb0⟩

/-- Every nontrivial affine unipotent group over a field has a nontrivial
homomorphism to the one-dimensional additive vector group. -/
theorem exists_additive_character {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine U.X.left] (hU : IsUnipotent U)
    (hnt : SubgroupFunctor.range (𝟙 U) ≠ ⊥) :
    ∃ q : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1, q ≠ 0 := by
  let eU := AffineCoordinates.groupSchemeIso U
  have hU' : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)) := IsUnipotent.of_iso eU hU
  have hnt' : SubgroupFunctor.range
      (𝟙 (Corepresented.groupScheme (AffineCoordinates.functor U)
        (AffineCoordinates.corepresentation U))) ≠ ⊥ := by
    intro h
    apply hnt
    exact RelativeRoot.HasSplitSeries.of_iso eU (n := 0) h
  obtain ⟨q, hq⟩ := exists_additive_character_of_isUnipotent
    (AffineCoordinates.corepresentation U) hU' hnt'
  refine ⟨eU.inv ≫ q, ?_⟩
  intro h0
  apply hq
  calc q = eU.hom ≫ (eU.inv ≫ q) := by simp
    _ = 0 := by rw [h0, Limits.comp_zero]

/-- A chosen nonzero additive character of a nontrivial affine unipotent group. -/
def nonzeroAdditiveCharacter {U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine U.X.left] (hU : IsUnipotent U)
    (hnt : SubgroupFunctor.range (𝟙 U) ≠ ⊥) :
    {q : U ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1 // q ≠ 0} :=
  ⟨Classical.choose (exists_additive_character hU hnt),
    Classical.choose_spec (exists_additive_character hU hnt)⟩

end Langlands.GroupScheme.Unipotent
