import Langlands.GroupScheme.MuAffinePresentationStatement
import Langlands.GroupScheme.MultiplicativeLaurent

/-! # Affine quotient presentation of the roots-of-unity kernel -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme
namespace MuAffinePresentation

/-- The equation defining the quotient coordinate algebra. -/
abbrev equation (A : CommRingCat.{u}) (n : ℕ) : Polynomial A :=
  Polynomial.X ^ n - 1

/-- The quotient spectrum with its canonical coefficient structural map. -/
abbrev model (A : CommRingCat.{u}) (n : ℕ) : Over (Spec A) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot (equation A n)))))

lemma root_pow (A : CommRingCat.{u}) (n : ℕ) :
    AdjoinRoot.root (equation A n) ^ n = 1 := by
  have h := AdjoinRoot.eval₂_root (equation A n)
  simpa only [equation, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_one, sub_eq_zero] using h

/-- Positivity makes the quotient coordinate a unit and a root of unity. -/
def coordinate (A : CommRingCat.{u}) (n : ℕ) (hn : 0 < n) :
    rootsOfUnity n (AdjoinRoot (equation A n)) :=
  ⟨Units.ofPowEqOne _ n (root_pow A n) (Nat.ne_of_gt hn),
    (mem_rootsOfUnity n _).mpr (Units.pow_ofPowEqOne _ _)⟩

/-- Pulling back the quotient coordinate gives a root of unity on any test scheme. -/
def roots {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n) (T : Over (Spec A))
    (x : T ⟶ model A n) : rootsOfUnity n Γ(T.left, ⊤) :=
  restrictRootsOfUnity (Gm.specHomEquiv T.left _ x.left).hom n (coordinate A n hn)

lemma roots_val {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n) (T : Over (Spec A))
    (x : T ⟶ model A n) :
    ((roots n hn T x : (Γ(T.left, ⊤))ˣ) : Γ(T.left, ⊤)) =
      (Gm.specHomEquiv T.left _ x.left) (AdjoinRoot.root (equation A n)) := rfl

lemma roots_comp {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n)
    {T T' : Over (Spec A)} (a : T' ⟶ T) (x : T ⟶ model A n) :
    roots n hn T' (a ≫ x) =
      restrictRootsOfUnity a.left.appTop.hom n (roots n hn T x) := rfl

lemma eval_equation {A : CommRingCat.{u}} {B : Type u} [CommRing B]
    (n : ℕ) (i : A →+* B) (ζ : rootsOfUnity n B) :
    Polynomial.eval₂ i (ζ.val : B) (equation A n) = 0 := by
  have h := congrArg (fun z : Bˣ => (z : B)) ((mem_rootsOfUnity n _).mp ζ.property)
  simpa only [equation, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_one, Units.val_pow_eq_pow_val,
    Units.val_one, sub_eq_zero] using h

/-- A root of unity defines a quotient-spectrum point using the fixed coefficient map. -/
def lift {A : CommRingCat.{u}} (n : ℕ) (T : Over (Spec A))
    (ζ : rootsOfUnity n Γ(T.left, ⊤)) : T ⟶ model A n :=
  Over.homMk
    ((Gm.specHomEquiv T.left _).symm
      (CommRingCat.ofHom (AdjoinRoot.lift (Gm.specHomEquiv T.left A T.hom).hom
        (ζ.val : Γ(T.left, ⊤)) (eval_equation n _ ζ)))) (by
        apply (Gm.specHomEquiv T.left A).injective
        dsimp only [model, Over.mk_hom]
        rw [Gm.specHomEquiv_specMap, Equiv.apply_symm_apply]
        apply CommRingCat.hom_ext
        change (AdjoinRoot.lift (Gm.specHomEquiv T.left A T.hom).hom
          (ζ.val : Γ(T.left, ⊤)) (eval_equation n _ ζ)).comp
            (AdjoinRoot.of (equation A n)) = _
        exact AdjoinRoot.lift_comp_of (eval_equation n _ ζ))

lemma roots_lift {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n)
    (T : Over (Spec A)) (ζ : rootsOfUnity n Γ(T.left, ⊤)) :
    roots n hn T (lift n T ζ) = ζ := by
  apply Subtype.ext
  apply Units.ext
  rw [roots_val]
  change (Gm.specHomEquiv T.left (CommRingCat.of (AdjoinRoot (equation A n)))
    ((Gm.specHomEquiv T.left _).symm _)) (AdjoinRoot.root (equation A n)) = _
  rw [Equiv.apply_symm_apply]
  exact AdjoinRoot.lift_root (eval_equation n _ ζ)

lemma lift_roots {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n)
    (T : Over (Spec A)) (x : T ⟶ model A n) :
    lift n T (roots n hn T x) = x := by
  apply Over.OverMorphism.ext
  apply (Gm.specHomEquiv T.left _).injective
  change (Gm.specHomEquiv T.left _ ((Gm.specHomEquiv T.left _).symm _)) = _
  rw [Equiv.apply_symm_apply]
  apply CommRingCat.hom_ext
  change AdjoinRoot.lift (Gm.specHomEquiv T.left A T.hom).hom
    ((roots n hn T x).val : Γ(T.left, ⊤)) (eval_equation n _ (roots n hn T x)) =
      (Gm.specHomEquiv T.left _ x.left).hom
  apply AdjoinRoot.ringHom_ext
  · rw [AdjoinRoot.lift_comp_of]
    have h := congrArg (Gm.specHomEquiv T.left A) (Over.w x)
    dsimp only [model, Over.mk_hom] at h
    rw [Gm.specHomEquiv_specMap] at h
    exact congrArg CommRingCat.Hom.hom h.symm
  · rw [AdjoinRoot.lift_root]
    rfl

/-- The quotient spectrum represents roots of unity on every scheme over the affine base. -/
def homEquiv {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n) (T : Over (Spec A)) :
    (T ⟶ model A n) ≃ rootsOfUnity n Γ(T.left, ⊤) where
  toFun := roots n hn T
  invFun := lift n T
  left_inv := lift_roots n hn T
  right_inv := roots_lift n hn T

/-- The natural comparison with points of the actual torsion kernel. -/
def comparison {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n) (T : Over (Spec A)) :
    (T ⟶ (mu (Spec A) n).X) ≃ (T ⟶ model A n) :=
  (mu.pointsEquiv (Spec A) n T).toEquiv.trans (homEquiv n hn T).symm

lemma comparison_comp {A : CommRingCat.{u}} (n : ℕ) (hn : 0 < n)
    {T T' : Over (Spec A)} (a : T' ⟶ T) (x : T ⟶ (mu (Spec A) n).X) :
    comparison n hn T' (a ≫ x) = a ≫ comparison n hn T x := by
  apply (homEquiv n hn T').injective
  change homEquiv n hn T' ((homEquiv n hn T').symm _) =
    roots n hn T' (a ≫ comparison n hn T x)
  rw [Equiv.apply_symm_apply]
  change mu.pointsEquiv (Spec A) n T' (a ≫ x) = _
  rw [mu.pointsEquiv_naturality, roots_comp]
  change _ = restrictRootsOfUnity _ n ((homEquiv n hn T) ((homEquiv n hn T).symm _))
  rw [Equiv.apply_symm_apply]
  rfl

/-- Yoneda upgrades the natural comparison on all test schemes to an Over-isomorphism. -/
def iso (A : CommRingCat.{u}) (n : ℕ) (hn : 0 < n) :
    (mu (Spec A) n).X ≅ model A n :=
  Yoneda.ext _ _ (fun {_} => comparison n hn _) (fun {_} => (comparison n hn _).symm)
    (fun _ => Equiv.symm_apply_apply _ _) (fun _ => Equiv.apply_symm_apply _ _)
    (comparison_comp n hn)

end MuAffinePresentation

/-- The actual roots-of-unity kernel has the canonical affine quotient presentation. -/
theorem muAffinePresentation : MuAffinePresentationStatement.{u} := by
  intro A n hn
  exact ⟨MuAffinePresentation.iso A n hn⟩

end Langlands.GroupScheme
