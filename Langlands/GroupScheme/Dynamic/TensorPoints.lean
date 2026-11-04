import Langlands.GroupScheme.Dynamic.BaseChangeCellTranslation

/-! # Base change of points along `Spec Ω → Spec k`

For a scheme `Y` over a field `k` and a field extension `Ω`, a point `z` of `Y` over a
`k`-algebra `K` gives a point `tensorPoint z` of `Y_Ω` over `Ω ⊗[k] K`. This is natural in `Y`.
For the corepresented group `G`, it is multiplicative and agrees with `bcPoint`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

variable {k : Type u} [Field k] {Ω : Type u} [Field Ω] [Algebra k Ω]

section General

variable {A : Type u} [CommRing A] [Algebra k A] [Algebra Ω A] [IsScalarTower k Ω A]

/-- A point of `Y` over the `Ω`-algebra `A`, regarded over `k`, gives a point of `Y_Ω`. -/
def pullbackPoint {Y : Over (Spec (CommRingCat.of k))} (z : algOver k A ⟶ Y) :
    testOver Ω A ⟶ (Over.pullback (scalarMap k Ω)).obj Y :=
  (Over.mapPullbackAdj (scalarMap k Ω)).homEquiv _ _ (testOverInv Ω A ≫ z)

theorem pullbackPoint_comp {Y Y' : Over (Spec (CommRingCat.of k))} (z : algOver k A ⟶ Y)
    (f : Y ⟶ Y') :
    pullbackPoint (Ω := Ω) (z ≫ f) = pullbackPoint z ≫ (Over.pullback (scalarMap k Ω)).map f := by
  rw [pullbackPoint, pullbackPoint, ← Category.assoc, Adjunction.homEquiv_naturality_right]

variable {K : Type u} [CommRing K] [Algebra k K]

variable (Ω) in
/-- The base change to `Ω ⊗[k] K` of a point of `Y` over `K`. -/
def tensorPoint {Y : Over (Spec (CommRingCat.of k))} (z : algOver k K ⟶ Y) :
    testOver Ω (Ω ⊗[k] K) ⟶ (Over.pullback (scalarMap k Ω)).obj Y :=
  pullbackPoint (algOverHom (Algebra.TensorProduct.includeRight : K →ₐ[k] Ω ⊗[k] K) ≫ z)

theorem tensorPoint_comp {Y Y' : Over (Spec (CommRingCat.of k))} (z : algOver k K ⟶ Y)
    (f : Y ⟶ Y') :
    tensorPoint Ω (z ≫ f) = tensorPoint Ω z ≫ (Over.pullback (scalarMap k Ω)).map f := by
  rw [tensorPoint, tensorPoint, ← Category.assoc, pullbackPoint_comp]

end General

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {K : Type u} [CommRing K] [Algebra k K]

variable (Ω) in
/-- The base change to `Ω ⊗[k] K` of a point of `G` over `K`, as a point of the group `G_Ω`. -/
def tensorGPoint (z : algOver k K ⟶ (groupScheme F e).X) :
    testOver Ω (Ω ⊗[k] K) ⟶ (baseChangeGroup F e Ω).X :=
  bcPoint F e Ω (Ω ⊗[k] K) (Algebra.TensorProduct.includeRight.comp (pointAlgHom z))

theorem tensorGPoint_eq (z : algOver k K ⟶ (groupScheme F e).X) :
    tensorGPoint Ω z = (baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) _).symm
      (testOverInv Ω (Ω ⊗[k] K) ≫ algOverHom Algebra.TensorProduct.includeRight ≫ z) := by
  rw [tensorGPoint, bcPoint, ← algOverHom_comp_ofAlgHom, ofAlgHom_pointAlgHom]

/-- For the group `G`, `tensorPoint` is `tensorGPoint`. -/
theorem tensorPoint_eq_tensorGPoint (z : algOver k K ⟶ (groupScheme F e).X) :
    tensorPoint Ω z = tensorGPoint Ω z := by
  rw [tensorGPoint_eq]
  rfl

/-- `tensorGPoint` is multiplicative. -/
theorem tensorGPoint_mul (z z' : algOver k K ⟶ (groupScheme F e).X) :
    tensorGPoint Ω (z * z') = tensorGPoint Ω z * tensorGPoint Ω z' := by
  rw [tensorGPoint_eq, tensorGPoint_eq, tensorGPoint_eq, ← map_mul, MonObj.comp_mul,
    MonObj.comp_mul]

/-- `tensorGPoint` carries `U_G(ν)` into `U_{G_Ω}(ν_Ω)`. -/
theorem tensorGPoint_mem_unipotent (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)
    {z : algOver k K ⟶ (groupScheme F e).X} (hz : z ∈ (Dynamic.unipotent ν).carrier _) :
    tensorGPoint Ω z ∈
      (Dynamic.unipotent (Dynamic.baseChangeCocharacter (scalarMap k Ω) ν)).carrier _ := by
  rw [Dynamic.unipotent_baseChange, SubgroupFunctor.mem_baseChange, tensorGPoint_eq,
    MulEquiv.apply_symm_apply]
  exact (Dynamic.unipotent ν).comp_mem _ ((Dynamic.unipotent ν).comp_mem _ hz)

/-- Restricting a constant point gives the constant point. -/
theorem algOverHom_comp_ofAlgHom_ofId {A A' : Type u} [CommRing A] [Algebra k A] [CommRing A']
    [Algebra k A'] (ψ : A →ₐ[k] A') (a : B →ₐ[k] k) :
    algOverHom ψ ≫ ofAlgHom F e ((Algebra.ofId k A).comp a) =
      ofAlgHom F e ((Algebra.ofId k A').comp a) := by
  rw [algOverHom_comp_ofAlgHom, ← AlgHom.comp_assoc]
  congr 2
  exact AlgHom.ext fun r => ψ.commutes r

/-- The base change of a constant point is the constant point. -/
theorem tensorGPoint_ofAlgHom_ofId (a : B →ₐ[k] k) :
    tensorGPoint Ω (ofAlgHom F e ((Algebra.ofId k K).comp a)) =
      bcPoint F e Ω (Ω ⊗[k] K) ((Algebra.ofId k (Ω ⊗[k] K)).comp a) := by
  rw [tensorGPoint, pointAlgHom_ofAlgHom, ← AlgHom.comp_assoc]
  congr 2
  exact AlgHom.ext fun r => Algebra.TensorProduct.includeRight.commutes r

end Corepresented

end Langlands.GroupScheme
