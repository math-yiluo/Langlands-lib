import Langlands.GroupScheme.Torus.WeilRestrictionBaseChange

/-! # Weil points over an affine base with raw global-section scalar maps -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.AffineWeilPoints

variable (S : Scheme.{u}) [IsAffine S]

/-- Global sections with the scalar map supplied by the actual structure map
to the affine base. -/
def sections (T : Over S) : CommAlgCat Γ(S, ⊤) :=
  letI := T.hom.appTop.hom.toAlgebra
  CommAlgCat.of Γ(S, ⊤) Γ(T.left, ⊤)

/-- The spectrum-based and actual-base global-section algebras are canonically
identified by the identity on their underlying ring. -/
def sectionsEquiv (T : Over S) :
    ((algΓ Γ(S, ⊤)).obj ((Over.map S.isoSpec.hom).obj T)).unop ≃ₐ[Γ(S, ⊤)] sections S T := by
  refine { RingEquiv.refl Γ(T.left, ⊤) with commutes' := ?_ }
  intro r
  change (T.hom ≫ S.isoSpec.hom).appTop.hom ((Scheme.ΓSpecIso Γ(S, ⊤)).inv r) =
    T.hom.appTop.hom r
  rw [Scheme.Hom.comp_appTop]
  change T.hom.appTop.hom (S.toSpecΓ.appTop.hom ((Scheme.ΓSpecIso Γ(S, ⊤)).inv r)) = _
  rw [Scheme.toSpecΓ_appTop]
  exact congrArg T.hom.appTop.hom ((Scheme.ΓSpecIso Γ(S, ⊤)).inv_hom_id_apply r)

/-- Pullback on global sections, with the actual structure-map scalar actions. -/
def sectionsMap {T T' : Over S} (a : T' ⟶ T) : sections S T →ₐ[Γ(S, ⊤)] sections S T' := by
  refine { a.left.appTop.hom with commutes' := ?_ }
  intro r
  change a.left.appTop.hom (T.hom.appTop.hom r) = T'.hom.appTop.hom r
  change (T.hom.appTop ≫ a.left.appTop).hom r = _
  rw [← Scheme.Hom.comp_appTop, Over.w a]

variable (E : Type u) [CommRing E] [Algebra Γ(S, ⊤) E]
  [Module.Finite Γ(S, ⊤) E] [Module.Projective Γ(S, ⊤) E]

/-- The actual Weil group over the affine scheme. -/
abbrev group : GroupScheme S :=
  (GroupScheme.baseChange S.isoSpec.hom).obj (WeilGm.groupScheme Γ(S, ⊤) E)

/-- Its point model uses the actual-base scalar map on global sections. -/
def pointsEquiv (T : Over S) :
    (T ⟶ (group S E).X) ≃* (E ⊗[Γ(S, ⊤)] sections S T)ˣ :=
  (GroupScheme.baseChangePointsEquiv S.isoSpec.hom (WeilGm.groupScheme Γ(S, ⊤) E) T).trans
    ((WeilGm.pointsEquiv Γ(S, ⊤) E ((Over.map S.isoSpec.hom).obj T)).trans
      (Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R := Γ(S, ⊤)) (A₁ := E))
        (sectionsEquiv S T)).toMulEquiv))

omit [Module.Finite Γ(S, ⊤) E] [Module.Projective Γ(S, ⊤) E] in
/-- The identity comparison of section algebras is natural after tensoring. -/
theorem tensorSectionsEquiv_naturality {T T' : Over S} (a : T' ⟶ T)
    (z : E ⊗[Γ(S, ⊤)] ((algΓ Γ(S, ⊤)).obj ((Over.map S.isoSpec.hom).obj T)).unop) :
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := Γ(S, ⊤)) (A₁ := E)) (sectionsEquiv S T')
        (Algebra.TensorProduct.lTensor (S := E) E
          ((algΓ Γ(S, ⊤)).map ((Over.map S.isoSpec.hom).map a)).unop.hom z) =
      Algebra.TensorProduct.lTensor (S := E) E (sectionsMap S a)
        (Algebra.TensorProduct.congr (AlgEquiv.refl (R := Γ(S, ⊤)) (A₁ := E))
          (sectionsEquiv S T) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul e t => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Weil points commute with arbitrary relative test morphisms using the
actual global-section restriction maps. -/
theorem pointsEquiv_naturality {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ (group S E).X) :
    pointsEquiv S E T' (a ≫ x) =
      Units.map (Algebra.TensorProduct.lTensor (S := E) E (sectionsMap S a) :
        E ⊗[Γ(S, ⊤)] sections S T →* E ⊗[Γ(S, ⊤)] sections S T') (pointsEquiv S E T x) := by
  simp only [pointsEquiv, MulEquiv.trans_apply, GroupScheme.baseChangePointsEquiv_naturality,
    WeilGm.pointsEquiv_naturality]
  apply Units.ext
  exact tensorSectionsEquiv_naturality S E a _

end Langlands.GroupScheme.AffineWeilPoints
