import Langlands.GroupScheme.Rational.VectorActionCharZero
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Changing natural vector coordinates by a natural additive transition -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable (k : Type u) [Field k] (n : ℕ)

/-- Additive automorphisms of the coordinate vectors over every `k`-algebra,
natural in `k`-algebra maps. -/
structure NaturalCoordinateEquiv where
  /-- The transition over one coefficient algebra. -/
  equiv : ∀ A : CommAlgCat.{u} (CommRingCat.of k), (Fin n → A) ≃+ (Fin n → A)
  /-- The transition commutes with every algebra map. -/
  naturality : ∀ {A B : CommAlgCat.{u} (CommRingCat.of k)} (f : A ⟶ B) (x : Fin n → A),
    equiv B (fun j => f.hom (x j)) = fun j => f.hom (equiv A x j)

variable {k n}
    {V : GroupScheme (Spec (CommRingCat.of k))}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (Y : NaturalCoordinateEquiv k n)

/-- Change vector coordinates by a natural additive transition. -/
def recoordinatize (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)) :=
  (e T).trans (AddEquiv.toMultiplicative
    (Y.equiv (((algΓ (CommRingCat.of k)).obj T).unop) :
      (Fin n → Γ(T.left, ⊤)) ≃+ (Fin n → Γ(T.left, ⊤))))

theorem recoordinatize_apply (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ V.X) :
    (recoordinatize e Y T x).toAdd =
      Y.equiv (((algΓ (CommRingCat.of k)).obj T).unop) (e T x).toAdd := rfl

variable {e}

/-- The changed coordinates are natural. -/
theorem IsNaturalVectorCoordinates.recoordinatize (he : IsNaturalVectorCoordinates e) :
    IsNaturalVectorCoordinates (recoordinatize e Y) := by
  intro T W f x
  let fΓ : ((algΓ (CommRingCat.of k)).obj T).unop ⟶
      ((algΓ (CommRingCat.of k)).obj W).unop :=
    ((algΓ (CommRingCat.of k)).map f).unop
  change Y.equiv (((algΓ (CommRingCat.of k)).obj W).unop) (e W (f ≫ x)).toAdd =
    fun i => fΓ.hom (Y.equiv (((algΓ (CommRingCat.of k)).obj T).unop) (e T x).toAdd i)
  rw [he T W f]
  exact Y.naturality fΓ _

/-- On an affine test, the changed coordinates are the same transition in the
coefficient algebra. -/
theorem vectorAffineCoordinates_recoordinatize
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : Lie.AffinePoints V A) :
    (vectorAffineCoordinates (recoordinatize e Y) A x).toAdd =
      Y.equiv A (vectorAffineCoordinates e A x).toAdd := by
  let T := (algSpec (CommRingCat.of k)).obj (op A)
  let f := (Corepresented.affineSectionsIso A).hom
  have hf (z : ((algΓ (CommRingCat.of k)).obj T).unop) :
      f.hom z = (Scheme.ΓSpecIso (CommRingCat.of A)).hom z :=
    congrArg (fun g => g z) (Corepresented.affineSectionsIso_hom_ringHom A)
  have h := Y.naturality f (e T x).toAdd
  have hf' : (fun i => f.hom ((e T x).toAdd i)) =
      (vectorAffineCoordinates e A x).toAdd := by
    funext i
    exact hf _
  rw [hf'] at h
  funext i
  exact (hf _).symm.trans (congrFun h i).symm

/-- The inverse of the changed coordinates on an affine test. -/
theorem vectorAffineCoordinates_recoordinatize_symm
    (A : CommAlgCat.{u} (CommRingCat.of k)) (z : Fin n → A) :
    (vectorAffineCoordinates (recoordinatize e Y) A).symm (Multiplicative.ofAdd z) =
      (vectorAffineCoordinates e A).symm
        (Multiplicative.ofAdd ((Y.equiv A).symm z)) := by
  apply (vectorAffineCoordinates (recoordinatize e Y) A).injective
  apply Multiplicative.toAdd.injective
  rw [MulEquiv.apply_symm_apply, vectorAffineCoordinates_recoordinatize Y,
    MulEquiv.apply_symm_apply]
  simp only [toAdd_ofAdd, AddEquiv.apply_symm_apply]

variable {H : GroupScheme (Spec (CommRingCat.of k))} {a : AutomorphicAction H V}

/-- Scalar linearity in changed coordinates, stated through the original coordinates:
the conjugate of every coefficient action by the transition is scalar linear. -/
theorem isAffineLinearVectorCoordinates_recoordinatize
    (hY : ∀ (A : CommAlgCat.{u} (CommRingCat.of k)) (h : Lie.AffinePoints H A)
      (c : A) (z : Fin n → A),
      Y.equiv A (vectorAffineCoordinates e A (a.act h
        ((vectorAffineCoordinates e A).symm
          (Multiplicative.ofAdd ((Y.equiv A).symm (c • z)))))).toAdd =
        c • Y.equiv A (vectorAffineCoordinates e A (a.act h
          ((vectorAffineCoordinates e A).symm
            (Multiplicative.ofAdd ((Y.equiv A).symm z))))).toAdd) :
    IsAffineLinearVectorCoordinates a (recoordinatize e Y) := by
  intro A h c v
  obtain ⟨z, rfl⟩ : ∃ z, (vectorAffineCoordinates (recoordinatize e Y) A).symm
      (Multiplicative.ofAdd z) = v :=
    ⟨(vectorAffineCoordinates (recoordinatize e Y) A v).toAdd, by
      rw [ofAdd_toAdd, MulEquiv.symm_apply_apply]⟩
  simp only [MulEquiv.apply_symm_apply, toAdd_ofAdd]
  rw [vectorAffineCoordinates_recoordinatize_symm Y,
    vectorAffineCoordinates_recoordinatize_symm Y,
    vectorAffineCoordinates_recoordinatize Y,
    vectorAffineCoordinates_recoordinatize Y]
  exact hY A h c z

end Langlands.GroupScheme.RelativeRoot
