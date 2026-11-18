import Langlands.GroupScheme.Reductive.WeilAbelianImageTransfer
import Langlands.GroupScheme.Reductive.IdempotentPointsFamily

/-! # Homomorphisms from a Weil restriction over split test algebras -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.WeilAbelianImage

open WeilFactor Langlands.Algebra.GraphIdempotent IdempotentPoints

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

section Graph

variable {T : CommAlgCat.{u} (CommRingCat.of A)} (X : Under T) (φ : B →ₐ[A] X.right)

/-- `X` with the `B`-structure `φ`, as an algebra under `B ⊗[A] T`. -/
def graphUnder : Under (tensorT B T) :=
  letI : Algebra B X.right := φ.toRingHom.toAlgebra
  Under.mk (CommAlgCat.ofHom (X := B ⊗[A] T) (Y := X.right)
    { (Algebra.TensorProduct.productMap φ X.hom.hom).toRingHom with
      commutes' := fun b => by
        change Algebra.TensorProduct.productMap φ X.hom.hom (b ⊗ₜ[A] (1 : T)) = φ b
        rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one] })

/-- The identity of `X`, from the `A`-algebra restricted from `graphUnder X φ`. -/
def graphIsoHom : (resA A B).obj (graphUnder X φ).right ⟶ X.right :=
  ConcreteCategory.ofHom (C := CommAlgCat.{u} (CommRingCat.of A))
    (X := (resA A B).obj (graphUnder X φ).right) (Y := X.right)
    (@AlgHom.mk (CommRingCat.of A) ((resA A B).obj (graphUnder X φ).right) X.right _ _ _
      (CommAlgCat.algebra _) (CommAlgCat.algebra X.right) (RingHom.id X.right)
      (fun a => φ.commutes a))

/-- The identity of `X`, to the `A`-algebra restricted from `graphUnder X φ`. -/
def graphIsoInv : X.right ⟶ (resA A B).obj (graphUnder X φ).right :=
  ConcreteCategory.ofHom (C := CommAlgCat.{u} (CommRingCat.of A))
    (X := X.right) (Y := (resA A B).obj (graphUnder X φ).right)
    (@AlgHom.mk (CommRingCat.of A) X.right ((resA A B).obj (graphUnder X φ).right) _ _ _
      (CommAlgCat.algebra X.right) (CommAlgCat.algebra _) (RingHom.id X.right)
      (fun a => (φ.commutes a).symm))

theorem graphIsoInv_hom : graphIsoInv X φ ≫ graphIsoHom X φ = 𝟙 _ :=
  CommAlgCat.hom_ext (DFunLike.ext _ _ fun _ => rfl)

/-- The identity of `X`, as a map of `T`-algebras from the restriction of `graphUnder X φ`. -/
def graphUnderHom : underA (graphUnder X φ) ⟶ X :=
  Under.homMk (graphIsoHom X φ) (by
    refine CommAlgCat.hom_ext (DFunLike.ext _ _ fun t => ?_)
    change Algebra.TensorProduct.productMap φ X.hom.hom ((1 : B) ⊗ₜ[A] t) = X.hom.hom t
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul])

end Graph

/-- Graph idempotents are carried to graph idempotents by `lT`. -/
theorem lT_eq_of_isGraphIdempotent {T₁ T₂ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T₁ ⟶ T₂) {φ₁ : B →ₐ[A] T₁}
    {φ₂ : B →ₐ[A] T₂} (hφ : χ.hom.comp φ₁ = φ₂) {e₁ : B ⊗[A] T₁} {e₂ : B ⊗[A] T₂}
    (he₁ : IsGraphIdempotent φ₁ e₁) (he₂ : IsGraphIdempotent φ₂ e₂) :
    lT (B := B) χ e₁ = e₂ := by
  rw [lT_apply]
  subst hφ
  exact (he₁.map χ.hom).unique he₂

section Kill

variable [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B]
  (G' : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G'.X.left] [LocallyOfFiniteType G'.X.hom]
  {M : GroupScheme (Spec (CommRingCat.of A))} {T : CommAlgCat.{u} (CommRingCat.of A)}
  (c : Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor ⟶
    Under.forget T ⋙ M.affinePointFunctor)
  (hc : ∀ (X : Under T)
    (x y : (Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor).obj X),
    Commute (c.app X x) (c.app X y))
  (hred : IsReductive G') (hss : ∀ s, IsSemisimple (geometricFiber G' s))

include hc hred hss in
/-- **Points through a retract onto a restricted algebra.** Let `X` be a retract (as an
`A`-algebra, with the retraction a map of `T`-algebras) of the `A`-algebra underlying a
`(B ⊗[A] T)`-algebra `Z`. If the image of `x` over `Z` lies in the factor of the graph idempotent of
`B → Z`, then `c` kills `x`. -/
theorem app_eq_one_of_retract (X : Under T) (Z : Under (tensorT B T)) (u : underA Z ⟶ X)
    (v : X.right ⟶ (resA A B).obj Z.right) (huv : v ≫ u.right = 𝟙 X.right)
    (x : (AffineWeil.groupScheme A B G').affinePoints X.right)
    (hfix : snd G' (graphIdem A Z.right)
      (AffineWeil.pointsEquiv A B G' ((resA A B).obj Z.right)
        ((AffineWeil.groupScheme A B G').affinePointMap v x)) = 1) :
    c.app X x = 1 := by
  have hx : (AffineWeil.groupScheme A B G').affinePointMap u.right
      ((AffineWeil.groupScheme A B G').affinePointMap v x) = x := by
    have h1 := GroupScheme.affinePointMap_comp (AffineWeil.groupScheme A B G') v u.right
    rw [huv, GroupScheme.affinePointMap_id] at h1
    exact (DFunLike.congr_fun h1 x).symm
  have hemb := embNat_projNat_of_snd G' Z.right _ hfix
  have hk := app_embNat_eq_one G' c hc hred hss Z
    (((projNat A G').app Z.right).hom ((AffineWeil.groupScheme A B G').affinePointMap v x))
  have hnat := congrArg (fun k => GrpCat.Hom.hom k
    ((AffineWeil.groupScheme A B G').affinePointMap v x)) (c.naturality u)
  calc c.app X x = c.app X ((AffineWeil.groupScheme A B G').affinePointMap u.right
        ((AffineWeil.groupScheme A B G').affinePointMap v x)) := by rw [hx]
    _ = M.affinePointMap u.right (c.app (underA Z)
        ((AffineWeil.groupScheme A B G').affinePointMap v x)) := hnat
    _ = M.affinePointMap u.right (c.app (underA Z) (((embNat A G').app Z.right).hom
        (((projNat A G').app Z.right).hom
          ((AffineWeil.groupScheme A B G').affinePointMap v x)))) := by rw [hemb]
    _ = 1 := by rw [hk, map_one]

include hc hred hss in
/-- **The component at a graph idempotent is killed.** -/
theorem app_proj_graph_eq_one (X : Under T) (φ : B →ₐ[A] X.right) {e : B ⊗[A] X.right}
    (he : IsGraphIdempotent φ e)
    (x : (AffineWeil.groupScheme A B G').affinePoints X.right) :
    c.app X ((AffineWeil.pointsEquiv A B G' X.right).symm
      (proj G' e (AffineWeil.pointsEquiv A B G' X.right x))) = 1 := by
  refine app_eq_one_of_retract G' c hc hred hss X (graphUnder X φ) (graphUnderHom X φ)
    (graphIsoInv X φ) (graphIsoInv_hom X φ) _ ?_
  have hn := AffineWeil.pointsEquiv_naturality A B G' (graphIsoInv X φ).hom
    ((AffineWeil.pointsEquiv A B G' X.right).symm
      (proj G' e (AffineWeil.pointsEquiv A B G' X.right x)))
  have hn' : AffineWeil.pointsEquiv A B G' ((resA A B).obj (graphUnder X φ).right)
      ((AffineWeil.groupScheme A B G').affinePointMap (graphIsoInv X φ)
        ((AffineWeil.pointsEquiv A B G' X.right).symm
          (proj G' e (AffineWeil.pointsEquiv A B G' X.right x)))) =
      G'.affinePointMap (CommAlgCat.ofHom (lT (B := B) (graphIsoInv X φ)))
        (proj G' e (AffineWeil.pointsEquiv A B G' X.right x)) := by
    rw [MulEquiv.apply_symm_apply] at hn
    exact hn
  have hidem : lT (B := B) (graphIsoInv X φ) e = graphIdem A (graphUnder X φ).right :=
    lT_eq_of_isGraphIdempotent (graphIsoInv X φ)
      (AlgHom.ext fun _ => rfl) he (graphIdem_spec (A := A) (graphUnder X φ).right)
  rw [hn', proj_map G' _ he.isIdempotentElem hidem]
  exact snd_proj G' (graphIdem_spec (A := A) (graphUnder X φ).right).isIdempotentElem _

include hc hred hss in
/-- **Split case.** If `B ⊗[A] X` has a complete orthogonal family of graph idempotents, then `c`
is trivial on the points over `X`. -/
theorem app_eq_one_of_split (X : Under T) {n : ℕ} (φ : Fin n → (B →ₐ[A] X.right))
    (e : Fin n → B ⊗[A] X.right) (he : ∀ i, IsGraphIdempotent (φ i) (e i))
    (horth : ∀ i j, i ≠ j → e i * e j = 0) (hsum : ∑ i, e i = 1)
    (x : (AffineWeil.groupScheme A B G').affinePoints X.right) : c.app X x = 1 := by
  have h := map_eq_one_of_family G'
    ((c.app X).hom.comp (AffineWeil.pointsEquiv A B G' X.right).symm.toMonoidHom) e
    (fun i => (he i).isIdempotentElem) horth hsum
    (fun i g => by
      have := app_proj_graph_eq_one G' c hc hred hss X (φ i) (he i)
        ((AffineWeil.pointsEquiv A B G' X.right).symm g)
      rw [MulEquiv.apply_symm_apply] at this
      exact this)
    (AffineWeil.pointsEquiv A B G' X.right x)
  change (c.app X).hom ((AffineWeil.pointsEquiv A B G' X.right).symm
    (AffineWeil.pointsEquiv A B G' X.right x)) = 1 at h
  rw [MulEquiv.symm_apply_apply] at h
  exact h

end Kill

end Langlands.GroupScheme.WeilAbelianImage
