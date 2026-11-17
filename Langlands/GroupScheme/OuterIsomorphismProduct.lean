import Langlands.GroupScheme.OuterIsomorphismScheme

/-! # Outer quotients from an equivariant product presentation -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (I : GroupIsomorphismScheme G H) (a : AutomorphicAction A G)
  {Q : Over S} (e : A.X ⊗ Q ≅ I.parameter)
  (he : ∀ (T : Over S) (d x : T ⟶ A.X) (q : T ⟶ Q),
    lift d (lift x q ≫ e.hom) ≫ I.actionHom a = lift (d * x) q ≫ e.hom)

/-- The class morphism in a supplied equivariant product presentation. -/
def productClassMap : I.parameter ⟶ Q :=
  e.inv ≫ snd A.X Q

/-- The group coordinate of a point in the supplied product presentation. -/
def productGroupCoordinate {T : Over S} (p : T ⟶ I.parameter) : T ⟶ A.X :=
  p ≫ e.inv ≫ fst A.X Q

theorem product_coordinates {T : Over S} (p : T ⟶ I.parameter) :
    lift (I.productGroupCoordinate e p) (p ≫ I.productClassMap e) ≫ e.hom = p := by
  simp only [productGroupCoordinate, productClassMap, ← comp_lift, lift_fst_snd,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

include he in
/-- In product coordinates, the isomorphism action multiplies the first coordinate. -/
theorem product_action {T : Over S} (d : T ⟶ A.X) (p : T ⟶ I.parameter) :
    lift d p ≫ I.actionHom a =
      lift (d * I.productGroupCoordinate e p) (p ≫ I.productClassMap e) ≫
        e.hom := by
  conv_lhs => rw [← I.product_coordinates e p]
  exact he T d _ _

include he in
theorem productClassMap_invariant (T : Over S) (d : T ⟶ A.X)
    (p : T ⟶ I.parameter) :
    (lift d p ≫ I.actionHom a) ≫ I.productClassMap e =
      p ≫ I.productClassMap e := by
  rw [I.product_action a e he]
  simp only [productClassMap, Category.assoc, Iso.hom_inv_id_assoc, lift_snd]

include he in
theorem productGroupCoordinate_action (T : Over S) (d : T ⟶ A.X)
    (p : T ⟶ I.parameter) :
    I.productGroupCoordinate e (lift d p ≫ I.actionHom a) =
      d * I.productGroupCoordinate e p := by
  rw [I.product_action a e he]
  simp only [productGroupCoordinate, Category.assoc, Iso.hom_inv_id_assoc, lift_fst]

include he in
/-- Equal classes differ by one unique point of the acting group on the same test. -/
theorem productClassMap_orbit (T : Over S) (p q : T ⟶ I.parameter)
    (hpq : p ≫ I.productClassMap e = q ≫ I.productClassMap e) :
    ∃! d : T ⟶ A.X, lift d p ≫ I.actionHom a = q := by
  refine ⟨I.productGroupCoordinate e q * (I.productGroupCoordinate e p)⁻¹,
    ?_, ?_⟩
  · dsimp only
    rw [I.product_action a e he, inv_mul_cancel_right, hpq,
      I.product_coordinates e q]
  · intro d hd
    have hc := congrArg (I.productGroupCoordinate e) hd
    rw [I.productGroupCoordinate_action a e he] at hc
    exact (eq_mul_inv_iff_mul_eq).mpr hc

/-- A group factor has a section, so its product projection is surjective. -/
theorem productProjection_surjective :
    Surjective (snd A.X Q).left := by
  let s : Q ⟶ A.X ⊗ Q := lift (1 : Q ⟶ A.X) (𝟙 Q)
  have hs : s.left ≫ (snd A.X Q).left = 𝟙 Q.left := by
    exact congrArg (fun f => f.left) (lift_snd (1 : Q ⟶ A.X) (𝟙 Q))
  have : Surjective (s.left ≫ (snd A.X Q).left) := by
    rw [hs]
    infer_instance
  exact Surjective.of_comp s.left (snd A.X Q).left

/-- An equivariant product presentation supplies the full outer quotient.
Only the acting group is assumed flat and quasi-compact over the base. -/
def outerOfProduct [Flat A.X.hom] [QuasiCompact A.X.hom] :
    OuterIsomorphismScheme I a where
  parameter := Q
  classMap := I.productClassMap e
  flat := by
    have : IsIso e.inv.left := by
      change IsIso ((Over.forget S).map e.inv)
      infer_instance
    have : Flat (snd A.X Q).left := by
      change Flat (pullback.snd A.X.hom Q.hom)
      infer_instance
    change Flat (e.inv.left ≫ (snd A.X Q).left)
    infer_instance
  surjective := by
    have : IsIso e.inv.left := by
      change IsIso ((Over.forget S).map e.inv)
      infer_instance
    have := productProjection_surjective (A := A) (Q := Q)
    change Surjective (e.inv.left ≫ (snd A.X Q).left)
    infer_instance
  quasiCompact := by
    have : IsIso e.inv.left := by
      change IsIso ((Over.forget S).map e.inv)
      infer_instance
    have : QuasiCompact (snd A.X Q).left := by
      change QuasiCompact (pullback.snd A.X.hom Q.hom)
      infer_instance
    change QuasiCompact (e.inv.left ≫ (snd A.X Q).left)
    infer_instance
  invariant := I.productClassMap_invariant a e he
  orbit := I.productClassMap_orbit a e he

end GroupIsomorphismScheme

end Langlands.GroupScheme
