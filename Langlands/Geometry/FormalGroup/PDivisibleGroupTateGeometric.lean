import Langlands.Cohomology.DivisibleSystem.HomSurjective
import Langlands.Geometry.FormalGroup.PDivisibleGroupTateSections
import Langlands.RingTheory.FiniteTypeNonvanishingSpecializationProof
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Finite-level quotients of schematic Tate points on geometric tests -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

variable {R : CommRingCat.{u}} {G H J : CommGroupScheme (Spec R)}

/-- The last arrow of an affine fppf short exact sequence is surjective on
points over an algebraically closed field. -/
theorem AffineFppfShortExact.surjective_algebraicallyClosed {i : G ⟶ H} {q : H ⟶ J}
    (h : AffineFppfShortExact i q) (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K] :
    Function.Surjective (fun x : affineTest (CommAlgCat.of R K) ⟶ H.X =>
      x ≫ q.toMul.hom.hom) := by
  let A := CommAlgCat.of R K
  intro y
  obtain ⟨B, φ, hflat, hfinite, x, hx⟩ := h.2.2 A y
  let : Algebra K B := φ.hom.toRingHom.toAlgebra
  let : IsScalarTower R K B := IsScalarTower.of_algHom φ.hom
  let : Nontrivial B := Function.Injective.nontrivial hflat.injective
  let : Algebra.FiniteType K B := RingHom.FinitePresentation.of_finiteType.mpr hfinite
  obtain ⟨χ, _⟩ := Langlands.RingTheory.finiteTypeNonvanishingSpecialization K B ∅
    (by simpa only [Finset.prod_empty] using (not_isNilpotent_one : ¬ IsNilpotent (1 : B)))
  let ψ : B ⟶ A := CommAlgCat.ofHom (χ.restrictScalars R)
  have hψ : φ ≫ ψ = 𝟙 A := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    exact χ.commutes
  have hsection : (algSpec R).map ψ.op ≫ (algSpec R).map φ.op = 𝟙 (affineTest A) := by
    rw [← Functor.map_comp, ← op_comp, hψ, op_id]
    exact (algSpec R).map_id (op A)
  refine ⟨(algSpec R).map ψ.op ≫ x, ?_⟩
  change ((algSpec R).map ψ.op ≫ x) ≫ q.toMul.hom.hom = y
  rw [Category.assoc, hx, ← Category.assoc, hsection, Category.id_comp]

end Langlands.CommGroupScheme

namespace Langlands.PDivisibleGroup

open CommGroupScheme

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p)
variable (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]

local notation "T" => affineTest (CommAlgCat.of R K)

/-- Transfers between the actual finite group levels are surjective on geometric tests. -/
theorem schematicTateTestTransfer_surjective {m n : ℕ} (i : m ⟶ n) :
    Function.Surjective ((G.schematicTateTestDiagram T).map i.op) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom i)
  have hi : i = homOfLE (Nat.le_add_right m k) := Subsingleton.elim _ _
  subst i
  intro y
  obtain ⟨x, hx⟩ := (G.shortExact m k).surjective_algebraicallyClosed K y.toMul
  exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩

/-- Each geometric finite-level point is the projection of a schematic Tate section. -/
theorem schematicTatePointProjection_surjective (n : ℕ) :
    Function.Surjective ((G.schematicTatePointProjection n).app (op T)) := by
  let E := (evaluation ((Over (Spec R))ᵒᵖ) AddCommGrpCat.{u}).obj (op T)
  let F := (schematicTatePointSystem R p).obj G
  exact Langlands.Cohomology.concrete_surjective_π_app_of_surjective_map
    (isLimitOfPreserves E (limit.isLimit F))
    (fun k => G.schematicTateTestTransfer_surjective K (homOfLE (Nat.le_succ k))) n

/-- On a geometric test, quotienting by the kernel of projection gives the
actual finite group of points at that level. -/
def schematicTateProjectionQuotientEquiv (n : ℕ) :
    (((schematicTatePointFunctor R p).obj G).obj (op T) ⧸
      ((G.schematicTatePointProjection n).app (op T)).hom.ker) ≃+
      (GroupScheme.additivePoints (G.inclusions.obj n).toGrp).obj (op T) :=
  QuotientAddGroup.quotientKerEquivOfSurjective
    ((G.schematicTatePointProjection n).app (op T)).hom
    (G.schematicTatePointProjection_surjective K n)

end Langlands.PDivisibleGroup
