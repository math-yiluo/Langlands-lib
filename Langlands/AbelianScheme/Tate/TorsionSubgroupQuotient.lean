import Langlands.AbelianScheme.FiniteEtaleQuotientReverseMap
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra
import Langlands.AbelianScheme.Tate.FiniteMonodromy
import Langlands.AbelianScheme.Tate.FullIsogenyImages

/-! # Quotients of closed subgroups of actual torsion kernels -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme.FiniteEtaleSubgroup

variable {S : Scheme.{u}} (A : AbelianScheme S) (N : ℕ)
  (H : CommGroupScheme S) [IsFinite H.X.hom] [Etale H.X.hom]
  (i : H.toGrp ⟶ GroupScheme.kernel (GroupScheme.multiplication A.toGrp N))
  [IsClosedImmersion i.hom.hom.left]

/-- Compose a finite étale closed subgroup of the torsion kernel with its inclusion. -/
def ofTorsionSubgroup : FiniteEtaleSubgroup A where
  G := H
  inclusion := Additive.ofMul
    (i ≫ GroupScheme.kernelι (GroupScheme.multiplication A.toGrp N))
  isClosedImmersion := by
    change IsClosedImmersion
      (i.hom.hom.left ≫
        (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp N)).hom.hom.left)
    infer_instance

/-- The composite subgroup is killed by its torsion level as an actual scheme map. -/
theorem ofTorsionSubgroup_annihilated :
    (ofTorsionSubgroup A N H i).inclusion ≫ commHom (N • 𝟙 A) = 0 := by
  change Additive.ofMul
    ((i ≫ GroupScheme.kernelι (GroupScheme.multiplication A.toGrp N)) ≫
      groupHom (N • 𝟙 A)) = 0
  rw [Tate.groupHom_nsmul_id]
  apply congrArg Additive.ofMul
  apply Grp.hom_ext
  change (i.hom.hom ≫
    (GroupScheme.kernelι (GroupScheme.multiplication A.toGrp N)).hom.hom) ≫
      (GroupScheme.multiplication A.toGrp N).hom.hom = 1
  rw [Category.assoc, (GroupScheme.kernel_isPullback _).w, ← Category.assoc]
  exact congrArg (fun z => z ≫ η[A.X]) (comp_toUnit _)

namespace QuotientData

variable {A : AbelianScheme S} {K : FiniteEtaleSubgroup A} (D : K.QuotientData)

/-- The actual quotient kernel on arbitrary test-scheme points is exactly the inclusion image. -/
theorem comp_eq_one_iff_exists_inclusion (T : Over S) (x : T ⟶ A.X) :
    x ≫ (groupHom D.q).hom.hom = 1 ↔
      ∃ y : T ⟶ K.G.X, y ≫ (CommGroupScheme.groupHom K.inclusion).hom.hom = x := by
  constructor
  · intro hx
    let z := (GroupScheme.kernelPointsEquiv (groupHom D.q) T).symm ⟨x, hx⟩
    refine ⟨z ≫ D.kernelOverIso.inv, ?_⟩
    rw [← D.kernelOverIso_hom_inclusion]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg Subtype.val
      ((GroupScheme.kernelPointsEquiv (groupHom D.q) T).apply_symm_apply ⟨x, hx⟩)
  · rintro ⟨y, rfl⟩
    rw [← D.kernelOverIso_hom_inclusion, ← Category.assoc, Category.assoc]
    exact (GroupScheme.kernelPointsEquiv (groupHom D.q) T
      (y ≫ D.kernelOverIso.hom)).property

/-- The zero condition on a torsion coordinate is the same exact inclusion image condition. -/
theorem levelMap_eq_zero_iff_exists_inclusion
    (T : Over S) (N : ℕ) (x : GroupScheme.Tate.Level A.toGrp T N) :
    GroupScheme.Tate.levelMap T (groupHom D.q) N x = 0 ↔
      ∃ y : Additive (T ⟶ K.G.X),
        Additive.ofMul
          (y.toMul ≫ (CommGroupScheme.groupHom K.inclusion).hom.hom) =
            Additive.ofMul x.toMul.val := by
  have hz :
      GroupScheme.Tate.levelMap T (groupHom D.q) N x = 0 ↔
        x.toMul.val ≫ (groupHom D.q).hom.hom = 1 := by
    constructor
    · intro h
      exact congrArg (fun z : GroupScheme.Tate.Level D.B.toGrp T N => z.toMul.val) h
    · intro h
      exact GroupScheme.Tate.toSection_injective D.B.toGrp T N h
  rw [hz, D.comp_eq_one_iff_exists_inclusion]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y.toMul, congrArg Additive.toMul hy⟩

/-- The full Tate image of the actual reverse quotient map is the inverse image of
its subgroup on one torsion coordinate. -/
theorem exists_map_inverseMultiple_iff_exists_inclusion
    (T : Over S) (n : GroupScheme.Tate.Index (fun _ => True))
    (hK : K.inclusion ≫ commHom (n.val • 𝟙 A) = 0)
    (x : GroupScheme.Tate.Full A.toGrp T) :
    (∃ y : GroupScheme.Tate.Full D.B.toGrp T,
      GroupScheme.Tate.map T (fun _ => True)
        (groupHom (D.inverseMultiple n.val hK)) y = x) ↔
      ∃ y : Additive (T ⟶ K.G.X),
        Additive.ofMul
          (y.toMul ≫ (CommGroupScheme.groupHom K.inclusion).hom.hom) =
            Additive.ofMul
              (GroupScheme.Tate.evaluation A.toGrp T (fun _ => True) n x).toMul.val := by
  have hqr : groupHom D.q ≫ groupHom (D.inverseMultiple n.val hK) =
      GroupScheme.multiplication A.toGrp (n.val : ℤ) := by
    change groupHom (D.q ≫ D.inverseMultiple n.val hK) = _
    rw [D.q_inverseMultiple, Tate.groupHom_nsmul_id]
  have hrq : groupHom (D.inverseMultiple n.val hK) ≫ groupHom D.q =
      GroupScheme.multiplication D.B.toGrp (n.val : ℤ) := by
    change groupHom (D.inverseMultiple n.val hK ≫ D.q) = _
    rw [D.inverseMultiple_q, Tate.groupHom_nsmul_id]
  rw [GroupScheme.Tate.exists_map_reverse_iff T n (groupHom D.q)
    (groupHom (D.inverseMultiple n.val hK)) hqr hrq]
  exact D.levelMap_eq_zero_iff_exists_inclusion T n.val _

end QuotientData

end Langlands.AbelianScheme.FiniteEtaleSubgroup
