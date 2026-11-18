import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Translation reduction for infinitesimal homomorphism rigidity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MultiplicativeTypeRigidity

variable {S S₀ : Scheme.{u}} {H G : GroupScheme S}

/-- Pullback triviality makes the homomorphism trivial on each test over the new base. -/
theorem comp_eq_one_of_baseChange_eq_one (i : S₀ ⟶ S) (f : H ⟶ G)
    (hf : ((baseChange i).map f).hom.hom = 1) (T : Over S₀)
    (t : (Over.map i).obj T ⟶ H.X) : t ≫ f.hom.hom = 1 := by
  let t₀ := (baseChangePointsEquiv i H T).symm t
  have ht := baseChangePointsEquiv_comp i f T t₀
  rw [hf, MonObj.comp_one, map_one] at ht
  simpa only [t₀, MulEquiv.apply_symm_apply] using ht.symm

/-- If the quotient base change is trivial, it is trivial on every affine test
whose algebra annihilates the ideal. -/
theorem comp_eq_one_of_quotient_eq_one {R : CommRingCat.{u}}
    {H G : GroupScheme (Spec R)} (f : H ⟶ G) (I : Ideal R)
    (hf : ((baseChange (Spec.algebraMap R (R ⧸ I))).map f).hom.hom = 1)
    (C : CommAlgCat.{u} R) (hC : ∀ r : R, r ∈ I → algebraMap R C r = 0)
    (t : (algSpec R).obj (op C) ⟶ H.X) : t ≫ f.hom.hom = 1 := by
  let q : R ⧸ I →+* C := Ideal.Quotient.lift I (algebraMap R C) hC
  let T₀ : Over (Spec (CommRingCat.of (R ⧸ I))) :=
    Over.mk (Spec.map (CommRingCat.ofHom q))
  let e : (Over.map (Spec.algebraMap R (R ⧸ I))).obj T₀ ≅
      (algSpec R).obj (op C) := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.algebraMap R C =
      Spec.map (CommRingCat.ofHom q) ≫ Spec.algebraMap R (R ⧸ I)
    rw [Category.id_comp]
    change Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom q) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
    rw [← Spec.map_comp]
    congr 1)
  apply (cancel_epi e.hom).mp
  rw [MonObj.comp_one]
  exact comp_eq_one_of_baseChange_eq_one _ f hf T₀ (e.hom ≫ t)

/-- Left translations by the image of a group-scheme homomorphism. -/
@[instance_reducible] def translationAction (f : H ⟶ G) : SchemeAction H G.X :=
  (show SchemeAction G G.X from ModObj.regular G.X).restrict f

@[simp] theorem translationAction_act (f : H ⟶ G) {T : Over S}
    (t : T ⟶ H.X) (x : T ⟶ G.X) :
    (translationAction f).act t x = (t ≫ f.hom.hom) * x := by
  rw [translationAction, SchemeAction.restrict_act]
  rfl

/-- A trivial translation action forces its defining homomorphism to be trivial. -/
theorem eq_one_of_translationAction_hom (f : H ⟶ G)
    (h : (translationAction f).hom = snd H.X G.X) : f.hom.hom = 1 := by
  calc
    f.hom.hom = (translationAction f).act (𝟙 H.X) 1 := by
      rw [translationAction_act, Category.id_comp, mul_one]
    _ = 1 := by rw [SchemeAction.act, h, lift_snd]

/-- Action rigidity for the standard diagonalizable source implies homomorphism
rigidity for that source, with arbitrary target. -/
theorem standard_eq_one_of_action_rigidity {R : CommRingCat.{u}}
    {M : Type u} [AddCommGroup M] {G : GroupScheme (Spec R)}
    (f : (Diagonalizable.groupScheme R M).toGrp ⟶ G)
    (I : Ideal R) (_hI : IsNilpotent I)
    (hact : ∀ a : SchemeAction (Diagonalizable.groupScheme R M).toGrp G.X,
      (∀ C : CommAlgCat.{u} R, (∀ r : R, r ∈ I → algebraMap R C r = 0) →
        ∀ (t : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X)
          (x : (algSpec R).obj (op C) ⟶ G.X), a.act t x = x) →
        a.hom = snd _ _)
    (hf : ((baseChange (Spec.algebraMap R (R ⧸ I))).map f).hom.hom = 1) :
    f.hom.hom = 1 := by
  apply eq_one_of_translationAction_hom
  apply hact
  intro C hC t x
  rw [translationAction_act, comp_eq_one_of_quotient_eq_one f I hf C hC t, one_mul]

/-- The standard diagonalizable presentation transfers action rigidity to every
relatively diagonalizable source over an affine base. -/
theorem diagonalizable_eq_one_of_action_rigidity {R : CommRingCat.{u}}
    {G H : GroupScheme (Spec R)} (f : H ⟶ G)
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (I : Ideal R) (hI : IsNilpotent I)
    (hact : ∀ (M : Type u) [AddCommGroup M]
      (a : SchemeAction (Diagonalizable.groupScheme R M).toGrp G.X),
      (∀ C : CommAlgCat.{u} R, (∀ r : R, r ∈ I → algebraMap R C r = 0) →
        ∀ (t : (algSpec R).obj (op C) ⟶ (Diagonalizable.groupScheme R M).X)
          (x : (algSpec R).obj (op C) ⟶ G.X), a.act t x = x) →
        a.hom = snd _ _)
    (hf : ((baseChange (Spec.algebraMap R (R ⧸ I))).map f).hom.hom = 1) :
    f.hom.hom = 1 := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let d : (Diagonalizable.groupScheme R M).toGrp ≅ H :=
    (Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M).symm ≪≫ e.symm
  have hd : ((baseChange (Spec.algebraMap R (R ⧸ I))).map (d.hom ≫ f)).hom.hom = 1 := by
    rw [Functor.map_comp, Grp.comp_hom_hom, hf, MonObj.comp_one]
  have h := standard_eq_one_of_action_rigidity (d.hom ≫ f) I hI (hact M) hd
  apply (cancel_epi d.hom.hom.hom).mp
  simpa only [Grp.comp_hom_hom, MonObj.comp_one] using h

end Langlands.GroupScheme.MultiplicativeTypeRigidity
