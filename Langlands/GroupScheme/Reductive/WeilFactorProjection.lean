import Langlands.GroupScheme.AffineIdempotentPoints
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Factor projections of a Weil restriction attached to idempotents -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilFactor

theorem lTensor_lTensor {A B X Y Z : Type u} [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
    [CommRing Z] [Algebra A B] [Algebra A X] [Algebra A Y] [Algebra A Z]
    (f : X →ₐ[A] Y) (g : Y →ₐ[A] Z) (x : B ⊗[A] X) :
    Algebra.TensorProduct.lTensor (S := B) B g (Algebra.TensorProduct.lTensor (S := B) B f x) =
      Algebra.TensorProduct.lTensor (S := B) B (g.comp f) x := by
  induction x with
  | tmul b t => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [Module.Projective A B] (G : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

/-- The group functor of `R_{B/A}(G)` on `T`-algebras. -/
abbrev Fun (T : CommAlgCat.{u} (CommRingCat.of A)) : Under T ⥤ GrpCat.{u} :=
  Under.forget T ⋙ (AffineWeil.groupScheme A B G).affinePointFunctor

variable {A B}

/-- The image of `e ∈ B ⊗ T` in `B ⊗ X` for a `T`-algebra `X`. -/
abbrev baseIdem {T : CommAlgCat.{u} (CommRingCat.of A)} (X : Under T) (e : B ⊗[A] T) :
    B ⊗[A] X.right :=
  Algebra.TensorProduct.lTensor (S := B) B X.hom.hom e

variable (A B)

/-- The factor projection of `R_{B/A}(G)` over `T` attached to `e ∈ B ⊗_A T`: on points over a
`T`-algebra `X` it keeps the `e`-component and kills the `(1 - e)`-component. -/
def factorProjection {T : CommAlgCat.{u} (CommRingCat.of A)} (e : B ⊗[A] T)
    (he : IsIdempotentElem e) : Fun A B G T ⟶ Fun A B G T where
  app X := GrpCat.ofHom
    (((AffineWeil.pointsEquiv A B G X.right).symm.toMonoidHom.comp
      (IdempotentPoints.proj G (baseIdem X e))).comp
        (AffineWeil.pointsEquiv A B G X.right).toMonoidHom)
  naturality X Y a := by
    refine GrpCat.ext ?_
    intro (x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right))
    set_option maxRecDepth 1024 in
    change (AffineWeil.pointsEquiv A B G Y.right).symm
        (IdempotentPoints.proj G (baseIdem Y e) (AffineWeil.pointsEquiv A B G Y.right
          ((AffineWeil.groupScheme A B G).affinePointMap (CommAlgCat.ofHom a.right.hom) x))) =
      (AffineWeil.groupScheme A B G).affinePointMap (CommAlgCat.ofHom a.right.hom)
          ((AffineWeil.pointsEquiv A B G X.right).symm
            (IdempotentPoints.proj G (baseIdem X e) (AffineWeil.pointsEquiv A B G X.right x)))
    apply (AffineWeil.pointsEquiv A B G Y.right).injective
    rw [MulEquiv.apply_symm_apply, AffineWeil.pointsEquiv_naturality,
      AffineWeil.pointsEquiv_naturality, MulEquiv.apply_symm_apply]
    have hY : Algebra.TensorProduct.lTensor (S := B) B a.right.hom (baseIdem X e) =
        baseIdem Y e := by
      rw [baseIdem, baseIdem, lTensor_lTensor, ← CommAlgCat.hom_comp, Under.w a]
    rw [IdempotentPoints.proj_map G _ (he.map _) hY]

variable {A B G} {T : CommAlgCat.{u} (CommRingCat.of A)}

/-- A transformation of `Fun A B G T` acting on points over the test algebra `X`. -/
abbrev pt (ψ : Fun A B G T ⟶ Fun A B G T) (X : Under T) :
    (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right) →*
      (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right) :=
  (ψ.app X).hom

theorem pt_comp (ψ ψ' : Fun A B G T ⟶ Fun A B G T) (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (ψ ≫ ψ') X x = pt ψ' X (pt ψ X x) := rfl

theorem ext_pt {ψ ψ' : Fun A B G T ⟶ Fun A B G T} (h : ∀ X x, pt ψ X x = pt ψ' X x) :
    ψ = ψ' := by
  refine NatTrans.ext (funext fun X => GrpCat.ext ?_)
  intro x
  exact h X x

theorem pointsEquiv_pt_factorProjection {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    AffineWeil.pointsEquiv A B G X.right (pt (factorProjection A B G e he) X x) =
      IdempotentPoints.proj G (baseIdem X e) (AffineWeil.pointsEquiv A B G X.right x) :=
  MulEquiv.apply_symm_apply _ _

omit [Module.Finite A B] [Module.Projective A B] in
theorem baseIdem_isIdempotentElem {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T) :
    IsIdempotentElem (baseIdem X e) :=
  he.map _

/-- The factor projection has the defining property of the rigidity statement. -/
theorem factorProjection_spec {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    IdempotentPoints.fst G (baseIdem X e)
        (AffineWeil.pointsEquiv A B G X.right (pt (factorProjection A B G e he) X x)) =
      IdempotentPoints.fst G (baseIdem X e) (AffineWeil.pointsEquiv A B G X.right x) ∧
    IdempotentPoints.snd G (baseIdem X e)
        (AffineWeil.pointsEquiv A B G X.right (pt (factorProjection A B G e he) X x)) = 1 := by
  rw [pointsEquiv_pt_factorProjection]
  exact ⟨IdempotentPoints.fst_proj G (baseIdem_isIdempotentElem he X) _,
    IdempotentPoints.snd_proj G (baseIdem_isIdempotentElem he X) _⟩

/-- A transformation with the defining property for `e` is the factor projection of `e`. -/
theorem eq_factorProjection {e : B ⊗[A] T} (he : IsIdempotentElem e)
    (ψ : Fun A B G T ⟶ Fun A B G T)
    (hψ : ∀ (X : Under T)
      (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)),
      IdempotentPoints.fst G (baseIdem X e)
          (AffineWeil.pointsEquiv A B G X.right (pt ψ X x)) =
        IdempotentPoints.fst G (baseIdem X e) (AffineWeil.pointsEquiv A B G X.right x) ∧
      IdempotentPoints.snd G (baseIdem X e)
          (AffineWeil.pointsEquiv A B G X.right (pt ψ X x)) = 1) :
    ψ = factorProjection A B G e he := by
  refine ext_pt fun X x => ?_
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [pointsEquiv_pt_factorProjection]
  exact (IdempotentPoints.eq_proj_iff G (baseIdem_isIdempotentElem he X)).mpr (hψ X x)

theorem factorProjection_comp {e f : B ⊗[A] T} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) :
    factorProjection A B G e he ≫ factorProjection A B G f hf =
      factorProjection A B G (f * e) (hf.mul he) := by
  refine ext_pt fun X x => ?_
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [pt_comp, pointsEquiv_pt_factorProjection, pointsEquiv_pt_factorProjection,
    pointsEquiv_pt_factorProjection,
    IdempotentPoints.proj_proj G (baseIdem_isIdempotentElem hf X)
      (baseIdem_isIdempotentElem he X), baseIdem, baseIdem, baseIdem, map_mul]

theorem factorProjection_idem {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    factorProjection A B G e he ≫ factorProjection A B G e he = factorProjection A B G e he := by
  rw [factorProjection_comp]
  congr 1

theorem pt_factorProjection_zero (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (factorProjection A B G (0 : B ⊗[A] T) IsIdempotentElem.zero) X x = 1 := by
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [pointsEquiv_pt_factorProjection, map_one, baseIdem, map_zero,
    IdempotentPoints.proj_zero]

theorem pt_factorProjection_conj {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T)
    (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (factorProjection A B G e he) X (h * x * h⁻¹) =
      h * pt (factorProjection A B G e he) X x * h⁻¹ := by
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [pointsEquiv_pt_factorProjection, map_mul (AffineWeil.pointsEquiv A B G X.right),
    map_mul (AffineWeil.pointsEquiv A B G X.right), map_inv (AffineWeil.pointsEquiv A B G X.right),
    IdempotentPoints.proj_conj G (baseIdem_isIdempotentElem he X),
    map_mul (AffineWeil.pointsEquiv A B G X.right), map_mul (AffineWeil.pointsEquiv A B G X.right),
    map_inv (AffineWeil.pointsEquiv A B G X.right), pointsEquiv_pt_factorProjection]

/-- Restriction of a transformation over `T` to `T₁`-algebras along `χ : T ⟶ T₁`. -/
def restrict {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (ψ : Fun A B G T ⟶ Fun A B G T) : Fun A B G T₁ ⟶ Fun A B G T₁ where
  app X := ψ.app ((Under.map χ).obj X)
  naturality _ _ a := ψ.naturality ((Under.map χ).map a)

theorem pt_restrict {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (ψ : Fun A B G T ⟶ Fun A B G T) (X : Under T₁)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (restrict χ ψ) X x = pt ψ ((Under.map χ).obj X) x := rfl

theorem restrict_factorProjection {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    restrict χ (factorProjection A B G e he) =
      factorProjection A B G (Algebra.TensorProduct.lTensor (S := B) B χ.hom e) (he.map _) := by
  refine ext_pt fun X x => ?_
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [pt_restrict, pointsEquiv_pt_factorProjection]
  refine (pointsEquiv_pt_factorProjection (G := G) he ((Under.map χ).obj X) x).trans ?_
  have hb : baseIdem ((Under.map χ).obj X) e =
      baseIdem X (Algebra.TensorProduct.lTensor (S := B) B χ.hom e) := by
    rw [baseIdem, baseIdem, lTensor_lTensor]
    rfl
  rw [hb]
  rfl

theorem restrict_comp {T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (ψ ψ' : Fun A B G T ⟶ Fun A B G T) :
    restrict χ (ψ ≫ ψ') = restrict χ ψ ≫ restrict χ ψ' := rfl

end Langlands.GroupScheme.WeilFactor
