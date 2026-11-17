import Langlands.GroupScheme.Reductive.WeilChartDiagonal
import Langlands.GroupScheme.AffinePointFaithfullyFlatDescent

/-! # The diagonal factor projection of `G` on algebras over the descended coefficient algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.WeilChart

open Langlands.Algebra.GraphIdempotent

variable {A A' C B : Type u} [CommRing A] [CommRing A'] [CommRing C] [CommRing B]
  [Algebra A A'] [Algebra A' C] [Algebra A B] (e : A' ⊗[A] B ≃ₐ[A'] C)
  [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))

omit [Algebra.Etale A' C] in
theorem chartFactor_congr {T : CommAlgCat.{u} (CommRingCat.of A)} (f : A' →ₐ[A] T)
    {e₁ e₂ : letI := chartAlgebra f; C ⊗[A'] T} (h : e₁ = e₂) (h₁ : IsIdempotentElem e₁)
    (h₂ : IsIdempotentElem e₂) : chartFactor P f e₁ h₁ = chartFactor P f e₂ h₂ := by
  subst h
  rfl

section DiagProj

variable {T : CommAlgCat.{u} (CommRingCat.of A)}

/-- The diagonal factor projection of the points of `G` over `T`, through a chart map `f`, for an
algebra map `φ : B → T`. -/
def diagProj (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) : G.affinePoints T →* G.affinePoints T :=
  gpt (chartFactor P f (diagIdem e φ f) (diagIdem_isIdempotentElem e φ f)) (Under.mk (𝟙 T))

theorem diagProj_chart (φ : B →ₐ[A] T) (f₁ f₂ : A' →ₐ[A] T)
    (hinv : ∀ b : B, chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b))) :
    diagProj e P φ f₁ = diagProj e P φ f₂ := by
  rw [diagProj, diagProj, chartFactor_diagIdem e P hR hred hsimple φ f₁ f₂ hinv]

theorem diagProj_idem (φ : B →ₐ[A] T) (f : A' →ₐ[A] T) (x : G.affinePoints T) :
    diagProj e P φ f (diagProj e P φ f x) = diagProj e P φ f x :=
  congrArg (fun ψ => gpt ψ (Under.mk (𝟙 T)) x)
    (chartFactor_idem P f (diagIdem_isIdempotentElem e φ f))

theorem diagProj_map {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) (φ : B →ₐ[A] T)
    (f : A' →ₐ[A] T) (x : G.affinePoints T) :
    G.affinePointMap χ (diagProj e P φ f x) =
      diagProj e P (χ.hom.comp φ) (χ.hom.comp f) (G.affinePointMap χ x) := by
  have hn := congrArg (fun h => GrpCat.Hom.hom h x)
    ((chartFactor P f (diagIdem e φ f) (diagIdem_isIdempotentElem e φ f)).naturality
      (show Under.mk (𝟙 T) ⟶ (Under.map χ).obj (Under.mk (𝟙 T₁)) from
        Under.homMk χ (by simp)))
  calc G.affinePointMap χ (diagProj e P φ f x)
      = gpt (grestrict G χ (chartFactor P f (diagIdem e φ f) (diagIdem_isIdempotentElem e φ f)))
          (Under.mk (𝟙 T₁)) (G.affinePointMap χ x) := hn.symm
    _ = gpt (chartFactor P (χ.hom.comp f)
          (letI := chartAlgebra f
           letI := chartAlgebra (χ.hom.comp f)
           Algebra.TensorProduct.lTensor (S := C) C (chartMap f χ) (diagIdem e φ f))
          (letI := chartAlgebra f
           letI := chartAlgebra (χ.hom.comp f)
           (diagIdem_isIdempotentElem e φ f).map _))
          (Under.mk (𝟙 T₁)) (G.affinePointMap χ x) :=
        congrArg (fun ψ => gpt ψ (Under.mk (𝟙 T₁)) (G.affinePointMap χ x))
          (grestrict_chartFactor P f χ (diagIdem_isIdempotentElem e φ f))
    _ = diagProj e P (χ.hom.comp φ) (χ.hom.comp f) (G.affinePointMap χ x) :=
        congrArg (fun ψ => gpt ψ (Under.mk (𝟙 T₁)) (G.affinePointMap χ x))
          (chartFactor_congr P (χ.hom.comp f) (diagIdem_map e χ φ f) _ _)

end DiagProj

section Ext

variable (A') in
/-- The base change `T ⊗[A] A'` of a test algebra to the cover. -/
abbrev extT (T : CommAlgCat.{u} (CommRingCat.of A)) : CommAlgCat.{u} (CommRingCat.of A) :=
  CommAlgCat.of (CommRingCat.of A) (T ⊗[A] A')

variable (A') in
/-- The inclusion `T → T ⊗[A] A'`. -/
def extι (T : CommAlgCat.{u} (CommRingCat.of A)) : T ⟶ extT A' T :=
  CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := T) (B := A'))

/-- The chart map `A' → T ⊗[A] A'`. -/
def extChart (T : CommAlgCat.{u} (CommRingCat.of A)) : A' →ₐ[A] extT A' T :=
  Algebra.TensorProduct.includeRight

theorem extι_faithfullyFlat [Module.FaithfullyFlat A A'] (T : CommAlgCat.{u} (CommRingCat.of A)) :
    (extι A' T).hom.toRingHom.FaithfullyFlat :=
  (RingHom.faithfullyFlat_algebraMap_iff (R := T) (S := T ⊗[A] A')).2 inferInstance

/-- The map `T ⊗[A] A' → T₁ ⊗[A] A'` induced by `χ : T ⟶ T₁`. -/
def extMap {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) : extT A' T ⟶ extT A' T₁ :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map χ.hom (AlgHom.id A A'))

theorem extι_comp_extMap {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) :
    extι A' T ≫ extMap χ = χ ≫ extι A' T₁ := by
  refine CommAlgCat.hom_ext (AlgHom.ext fun t => ?_)
  exact Algebra.TensorProduct.map_tmul _ _ _ _

theorem extMap_comp_extChart {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) :
    (extMap (A' := A') χ).hom.comp (extChart T) = extChart T₁ := by
  apply AlgHom.ext
  intro a
  change Algebra.TensorProduct.map χ.hom (AlgHom.id A A') ((1 : T) ⊗ₜ[A] a) = (1 : T₁) ⊗ₜ[A] a
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

end Ext

section Descend

variable [Module.FaithfullyFlat A A']
  (hinv : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T) (b : B),
    chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b)))

variable {T : CommAlgCat.{u} (CommRingCat.of A)}

include hinv in
theorem exists_descProj (φ : B →ₐ[A] T) (x : G.affinePoints T) :
    ∃ y : G.affinePoints T, G.affinePointMap (extι A' T) y =
      diagProj e P ((extι A' T).hom.comp φ) (extChart T) (G.affinePointMap (extι A' T) x) := by
  refine AffinePointDescent.exists_affinePointMap_eq G (extι A' T) (extι_faithfullyFlat T) _
    (fun Z a b hab => ?_)
  have h1 : G.affinePointMap a (G.affinePointMap (extι A' T) x) =
      G.affinePointMap b (G.affinePointMap (extι A' T) x) := by
    rw [← MonoidHom.comp_apply, ← G.affinePointMap_comp, hab, G.affinePointMap_comp,
      MonoidHom.comp_apply]
  have h2 : a.hom.comp ((extι A' T).hom.comp φ) = b.hom.comp ((extι A' T).hom.comp φ) := by
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    exact congrArg (fun χ : T ⟶ Z => χ.hom.comp φ) hab
  rw [diagProj_map, diagProj_map, h1, h2,
    diagProj_chart e P hR hred hsimple _ _ _ (hinv Z _ _)]

/-- The diagonal factor projection of the points of `G` over an `A`-algebra `T` with an algebra
map `φ : B → T`, descended from `T ⊗[A] A'`. -/
def descProj (φ : B →ₐ[A] T) : G.affinePoints T →* G.affinePoints T where
  toFun x := Classical.choose (exists_descProj e P hR hred hsimple hinv φ x)
  map_one' := by
    apply AffinePointDescent.affinePointMap_injective G (extι A' T) (extι_faithfullyFlat T)
    rw [Classical.choose_spec (exists_descProj e P hR hred hsimple hinv φ 1), map_one, map_one]
  map_mul' x y := by
    apply AffinePointDescent.affinePointMap_injective G (extι A' T) (extι_faithfullyFlat T)
    rw [Classical.choose_spec (exists_descProj e P hR hred hsimple hinv φ (x * y)), map_mul,
      map_mul, map_mul, Classical.choose_spec (exists_descProj e P hR hred hsimple hinv φ x),
      Classical.choose_spec (exists_descProj e P hR hred hsimple hinv φ y)]

theorem descProj_spec (φ : B →ₐ[A] T) (x : G.affinePoints T) :
    G.affinePointMap (extι A' T) (descProj e P hR hred hsimple hinv φ x) =
      diagProj e P ((extι A' T).hom.comp φ) (extChart T) (G.affinePointMap (extι A' T) x) :=
  Classical.choose_spec (exists_descProj e P hR hred hsimple hinv φ x)

/-- **Chart formula**: through any chart map, the descended projection is the diagonal factor
projection. -/
theorem descProj_eq_diagProj (φ : B →ₐ[A] T) (g : A' →ₐ[A] T) (x : G.affinePoints T) :
    descProj e P hR hred hsimple hinv φ x = diagProj e P φ g x := by
  apply AffinePointDescent.affinePointMap_injective G (extι A' T) (extι_faithfullyFlat T)
  rw [descProj_spec, diagProj_map,
    diagProj_chart e P hR hred hsimple _ _ _ (hinv _ (extChart T) ((extι A' T).hom.comp g))]

theorem descProj_idem (φ : B →ₐ[A] T) (x : G.affinePoints T) :
    descProj e P hR hred hsimple hinv φ (descProj e P hR hred hsimple hinv φ x) =
      descProj e P hR hred hsimple hinv φ x := by
  apply AffinePointDescent.affinePointMap_injective G (extι A' T) (extι_faithfullyFlat T)
  rw [descProj_spec, descProj_spec, diagProj_idem]

theorem descProj_map {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) (φ : B →ₐ[A] T)
    (x : G.affinePoints T) :
    G.affinePointMap χ (descProj e P hR hred hsimple hinv φ x) =
      descProj e P hR hred hsimple hinv (χ.hom.comp φ) (G.affinePointMap χ x) := by
  apply AffinePointDescent.affinePointMap_injective G (extι A' T₁) (extι_faithfullyFlat T₁)
  have hc : ∀ y : G.affinePoints T, G.affinePointMap (extι A' T₁) (G.affinePointMap χ y) =
      G.affinePointMap (extMap χ) (G.affinePointMap (extι A' T) y) := by
    intro y
    rw [← MonoidHom.comp_apply, ← G.affinePointMap_comp, ← MonoidHom.comp_apply,
      ← G.affinePointMap_comp, extι_comp_extMap]
  have hφ : (extMap (A' := A') χ).hom.comp ((extι A' T).hom.comp φ) =
      (extι A' T₁).hom.comp (χ.hom.comp φ) := by
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    exact congrArg (fun ξ : T ⟶ extT A' T₁ => ξ.hom.comp φ) (extι_comp_extMap χ)
  rw [hc, descProj_spec, diagProj_map, hφ, extMap_comp_extChart, descProj_spec, hc]

end Descend

end Langlands.GroupScheme.WeilChart
