import Langlands.GroupScheme.SpecialLinearBinaryRootGenerationStatement
import Langlands.GroupScheme.SpecialLinearGeometry
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Scheme-theoretic generation of SL₂ by its additive roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SpecialLinear.BinaryRoot

/-- On a test scheme with a field of global sections, both roots generate every point. -/
private theorem mem_range_of_field_sections {R : CommRingCat.{u}}
    {H : GroupScheme (Spec R)} (q : H ⟶ SpecialLinear.groupScheme (Fin 2) R)
    (hu : FactorsThrough (upperMap R).hom.hom q)
    (hl : FactorsThrough (lowerMap R).hom.hom q)
    (T : Over (Spec R)) (hfield : IsField Γ(T.left, ⊤))
    (x : T ⟶ (SpecialLinear.groupScheme (Fin 2) R).X) :
    x ∈ (SubgroupFunctor.range q).carrier T := by
  let : Field Γ(T.left, ⊤) := hfield.toField
  let e := SpecialLinear.pointsEquiv (Fin 2) R T
  let P : Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤) → Prop :=
    fun a => e.symm a ∈ (SubgroupFunctor.range q).carrier T
  have htrans : ∀ (i j : Fin 2) (hij : i ≠ j) a,
      P (Matrix.SpecialLinearGroup.transvection hij a) := by
    intro i j hij a
    let v := (VectorGroup.coordinates R 1 T).symm (Multiplicative.ofAdd fun _ => a)
    have hv : e.symm (Matrix.SpecialLinearGroup.transvection hij a) =
        v ≫ (rootMap R hij).hom.hom := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      change _ = SpecialLinear.pointsEquiv (Fin 2) R T _
      rw [pointsEquiv_rootMap]
      dsimp only [v]
      rw [MulEquiv.apply_symm_apply]
      rfl
    change e.symm _ ∈ (SubgroupFunctor.range q).carrier T
    rw [hv]
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact (factorsThrough_iff_containsImage _ q).mp hu T v
    · exact (factorsThrough_iff_containsImage _ q).mp hl T v
    · exact (hij rfl).elim
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    intro a b ha hb
    change e.symm (a * b) ∈ (SubgroupFunctor.range q).carrier T
    rw [map_mul]
    exact ((SubgroupFunctor.range q).carrier T).mul_mem ha hb
  have hx := Matrix.SL2.transvection_induction P htrans hmul (e x)
  simpa only [P, MulEquiv.symm_apply_apply] using hx

/-- Every underlying point lifts through a subgroup containing both roots. -/
private theorem surjective_of_root_factors {R : CommRingCat.{u}}
    {H : GroupScheme (Spec R)} (q : H ⟶ SpecialLinear.groupScheme (Fin 2) R)
    (hu : FactorsThrough (upperMap R).hom.hom q)
    (hl : FactorsThrough (lowerMap R).hom.hom q) :
    Surjective q.hom.hom.left := by
  let G := SpecialLinear.groupScheme (Fin 2) R
  constructor
  intro x
  let T : Over (Spec R) := Over.mk (G.X.left.fromSpecResidueField x ≫ G.X.hom)
  let a : T ⟶ G.X := Over.homMk (G.X.left.fromSpecResidueField x) rfl
  have hfield : IsField Γ(T.left, ⊤) :=
    (Scheme.ΓSpecIso (G.X.left.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField (G.X.left.residueField x))
  obtain ⟨y, hy⟩ := mem_range_of_field_sections q hu hl T hfield a
  let t := IsLocalRing.closedPoint (G.X.left.residueField x)
  refine ⟨y.left t, ?_⟩
  have he := congrArg (fun f : T ⟶ G.X => f.left t) hy
  change q.hom.hom.left (y.left t) = G.X.left.fromSpecResidueField x t at he
  exact he.trans (Scheme.fromSpecResidueField_apply x t)

end SpecialLinear.BinaryRoot

/-- The two actual additive root maps generate the binary special linear group scheme. -/
theorem specialLinearBinaryRootGeneration : SpecialLinearBinaryRootGenerationStatement.{u} := by
  intro k _
  let R := CommRingCat.of k
  let G := SpecialLinear.groupScheme (Fin 2) R
  refine ⟨?_, ?_, ?_⟩
  · change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  · intro j
    exact ⟨_, Category.comp_id _⟩
  · intro H q hq hroot
    have hu : FactorsThrough (SpecialLinear.BinaryRoot.upperMap R).hom.hom q := by
      simpa using hroot 0
    have hl : FactorsThrough (SpecialLinear.BinaryRoot.lowerMap R).hom.hom q := by
      simpa using hroot 1
    let : IsClosedImmersion q.hom.hom.left := hq
    let : Surjective q.hom.hom.left :=
      SpecialLinear.BinaryRoot.surjective_of_root_factors q hu hl
    let : Smooth G.X.hom := SpecialLinear.smooth_groupScheme (Fin 2) 0 R
    let : IsReduced G.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        k G.X.left G.X.hom
    let : IsIso q.hom.hom.left := isIso_of_isClosedImmersion_of_surjective q.hom.hom.left
    have : IsIso ((Over.forget (Spec R)).map q.hom.hom) := by
      change IsIso q.hom.hom.left
      infer_instance
    have : IsIso q.hom.hom := isIso_of_reflects_iso q.hom.hom (Over.forget (Spec R))
    intro T x _
    change ∃ y : T ⟶ H.X, y ≫ q.hom.hom = x
    exact ⟨x ≫ inv q.hom.hom, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩

end Langlands.GroupScheme
