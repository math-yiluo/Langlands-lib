import Langlands.AbelianScheme.KernelPairFactorization
import Langlands.AlgebraicGeometry.Picard.PoincarePointClasses
import Langlands.AlgebraicGeometry.Modules.PullbackTransport
import Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismScalarProof
import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundleTensorPow

/-! # The scalar defect of kernel translations on a line bundle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace KernelTranslation

variable {S : Scheme.{u}} {A B : AbelianScheme S} (q : A ⟶ B)

abbrev kernel := GroupScheme.kernel (groupHom q)

abbrev inclusion : (kernel q).X ⟶ A.X := (GroupScheme.kernelι (groupHom q)).hom.hom

/-- Translation on a point of the abelian scheme by a point of the actual kernel. -/
abbrev act {T : Over S} (x : T ⟶ A.X) (k : T ⟶ (kernel q).X) : T ⟶ A.X :=
  x * (k ≫ inclusion q)

lemma act_mul {T : Over S} (x : T ⟶ A.X) (k l : T ⟶ (kernel q).X) :
    act q (act q x k) l = act q x (k * l) := by
  simp only [act, MonObj.mul_comp, mul_assoc]

private lemma comp_act {T U : Over S} (a : U ⟶ T) (x : T ⟶ A.X)
    (k : T ⟶ (kernel q).X) : a ≫ act q x k = act q (a ≫ x) (a ≫ k) := by
  simp only [act, MonObj.comp_mul, Category.assoc]

/-- An isomorphism between the two actual pullbacks along the universal kernel translation. -/
abbrev Lift (L : LineBundle A.X.left) :=
  (Scheme.Modules.pullback (relativeSnd A (kernel q).X).left).obj L.obj ≅
    (Scheme.Modules.pullback (act q (relativeSnd A (kernel q).X)
      (relativeFst A (kernel q).X)).left).obj L.obj

variable {q} {L : LineBundle A.X.left} (α : Lift q L)

private lemma pair_fst {T : Over S} (k : T ⟶ (kernel q).X) (x : T ⟶ A.X) :
    pairOver A k x ≫ relativeFst A (kernel q).X = k := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, pairOver_left, relativeFst_left, pullback.lift_fst]

private lemma pair_snd {T : Over S} (k : T ⟶ (kernel q).X) (x : T ⟶ A.X) :
    pairOver A k x ≫ relativeSnd A (kernel q).X = x := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, pairOver_left, relativeSnd_left, pullback.lift_snd]

private lemma pair_act {T : Over S} (k : T ⟶ (kernel q).X) (x : T ⟶ A.X) :
    pairOver A k x ≫ act q (relativeSnd A (kernel q).X) (relativeFst A (kernel q).X) =
      act q x k := by
  rw [comp_act, pair_snd, pair_fst]

private abbrev fibre {T : Over S} (x : T ⟶ A.X) := (Scheme.Modules.pullback x.left).obj L.obj

/-- The pulled-back translation isomorphism on any test scheme. The final point is written
explicitly so that adjacent translations compose without changing pullback objects. -/
def step {T : Over S} (k : T ⟶ (kernel q).X) (x y : T ⟶ A.X) (h : act q x k = y) :
    fibre (L := L) x ⟶ fibre (L := L) y :=
  transport (pairOver A k x).left (congrArg CommaMorphism.left (pair_snd k x))
    (congrArg CommaMorphism.left ((pair_act k x).trans h)) α.hom

instance step_isIso {T : Over S} (k : T ⟶ (kernel q).X) (x y : T ⟶ A.X)
    (h : act q x k = y) : IsIso (step α k x y h) := by
  unfold step
  infer_instance

/-- The translation isomorphism is natural under further pullback. -/
lemma step_precomp {T U : Over S} (a : U ⟶ T) (k : T ⟶ (kernel q).X)
    (x y : T ⟶ A.X) (h : act q x k = y) (h' : act q (a ≫ x) (a ≫ k) = a ≫ y) :
    transport a.left (u' := (a ≫ x).left) (v' := (a ≫ y).left) rfl rfl (step α k x y h) =
      step α (a ≫ k) (a ≫ x) (a ≫ y) h' := by
  unfold step
  exact transport_transport_eq (pairOver A k x).left a.left
    (comp_pairOver_left A a k x) _ _ rfl rfl _ _ α.hom

private theorem scalar_cancel {T : Over S} {x y : T ⟶ A.X}
    (f : fibre (L := L) x ⟶ fibre (L := L) y) [IsIso f] {a b : Γ(T.left, ⊤)ˣ}
    (h : (a : Γ(T.left, ⊤)) • f = (b : Γ(T.left, ⊤)) • f) : a = b := by
  apply Units.ext
  have hL : IsLocallyFreeRankOne (fibre (L := L) x) := ((LineBundle.pullback x.left).obj L).property
  apply smul_id_injective_of_isLocallyFreeRankOne hL
  have eq := congrArg (· ≫ inv f) h
  simpa only [Linear.smul_comp, IsIso.hom_inv_id] using eq

private def comparisonScalar {U : Scheme.{u}} {F G : U.Modules}
    (hF : IsLocallyFreeRankOne F) (f g : F ⟶ G) [IsIso f] [IsIso g] : Γ(U, ⊤)ˣ :=
  (lineBundleAutomorphismScalar U F hF (asIso (f ≫ inv g))).choose

private lemma comparisonScalar_spec {U : Scheme.{u}} {F G : U.Modules}
    (hF : IsLocallyFreeRankOne F) (f g : F ⟶ G) [IsIso f] [IsIso g] :
    f = (comparisonScalar hF f g : Γ(U, ⊤)) • g := by
  have h := (lineBundleAutomorphismScalar U F hF (asIso (f ≫ inv g))).choose_spec.1
  change f ≫ inv g = (comparisonScalar hF f g : Γ(U, ⊤)) • 𝟙 F at h
  have h' := congrArg (· ≫ g) h
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Linear.smul_comp,
    Category.id_comp] using h'

private def defect {T : Over S} (k l : T ⟶ (kernel q).X) (x : T ⟶ A.X) : Γ(T.left, ⊤)ˣ :=
  let y := act q x k
  let z := act q y l
  comparisonScalar (L.property.pullback x.left) (step α k x y rfl ≫ step α l y z rfl)
    (step α (k * l) x z (act_mul q x k l).symm)

private lemma defect_spec_at_translate {T : Over S} (k l : T ⟶ (kernel q).X) (x : T ⟶ A.X) :
    let y := act q x k
    let z := act q y l
    step α k x y rfl ≫ step α l y z rfl =
      (defect α k l x : Γ(T.left, ⊤)) • step α (k * l) x z (act_mul q x k l).symm := by
  dsimp only
  unfold defect
  exact comparisonScalar_spec (L.property.pullback x.left)
    (step α k x (act q x k) rfl ≫ step α l (act q x k) (act q (act q x k) l) rfl)
    (step α (k * l) x (act q (act q x k) l) (act_mul q x k l).symm)

private lemma defect_spec {T : Over S} (k l : T ⟶ (kernel q).X) (x y z : T ⟶ A.X)
    (hxy : act q x k = y) (hyz : act q y l = z) (hxz : act q x (k * l) = z) :
    step α k x y hxy ≫ step α l y z hyz =
      (defect α k l x : Γ(T.left, ⊤)) • step α (k * l) x z hxz := by
  cases hxy
  cases hyz
  exact defect_spec_at_translate α k l x

private lemma defect_precomp {T U : Over S} (a : U ⟶ T)
    (k l : T ⟶ (kernel q).X) (x : T ⟶ A.X) :
    defect α (a ≫ k) (a ≫ l) (a ≫ x) =
      Units.map a.left.appTop.hom.toMonoidHom (defect α k l x) := by
  let y := act q x k
  let z := act q y l
  have hy : act q (a ≫ x) (a ≫ k) = a ≫ y := (comp_act q a x k).symm
  have hz : act q (a ≫ y) (a ≫ l) = a ≫ z := (comp_act q a y l).symm
  have hmul : a ≫ (k * l) = (a ≫ k) * (a ≫ l) := MonObj.comp_mul _ _ _
  have hxy : act q x k = y := rfl
  have hyz : act q y l = z := rfl
  have hxz : act q x (k * l) = z := (act_mul q x k l).symm
  have hxz' : act q (a ≫ x) ((a ≫ k) * (a ≫ l)) = a ≫ z := by
    rw [← act_mul, hy, hz]
  have ht := congrArg (transport a.left (u' := (a ≫ x).left) (v' := (a ≫ z).left) rfl rfl)
    (defect_spec α k l x y z hxy hyz hxz)
  rw [transport_comp a.left (v' := (a ≫ y).left) rfl rfl rfl, transport_smul,
    step_precomp α a k x y hxy hy, step_precomp α a l y z hyz hz,
    step_precomp α a (k * l) x z hxz (by rw [hmul]; exact hxz')] at ht
  have ht' : step α (a ≫ (k * l)) (a ≫ x) (a ≫ z) (by rw [hmul]; exact hxz') =
      step α ((a ≫ k) * (a ≫ l)) (a ≫ x) (a ≫ z) hxz' := by
    congr 1
  rw [ht'] at ht
  apply scalar_cancel (step α ((a ≫ k) * (a ≫ l)) (a ≫ x) (a ≫ z) hxz')
  exact (defect_spec α (a ≫ k) (a ≫ l) (a ≫ x) (a ≫ y) (a ≫ z) hy hz hxz').symm.trans ht

/-- Evaluate the defect at the unit point of the abelian scheme. -/
def scalar {T : Over S} (k l : T ⟶ (kernel q).X) : Γ(T.left, ⊤)ˣ := defect α k l 1

lemma scalar_precomp {T U : Over S} (a : U ⟶ T) (k l : T ⟶ (kernel q).X) :
    scalar α (a ≫ k) (a ≫ l) = Units.map a.left.appTop.hom.toMonoidHom (scalar α k l) := by
  unfold scalar
  simpa only [MonObj.comp_one] using defect_precomp α a k l 1

private lemma defect_eq_scalar {T : Over S} (k l : T ⟶ (kernel q).X) (x : T ⟶ A.X) :
    defect α k l x = scalar α k l := by
  let π := relativeFst A T
  let v := relativeSnd A T
  let d := defect α (π ≫ k) (π ≫ l) v
  let e := relativeUnitDescend A (universalGlobalFunctions A) T d
  have he (w : T ⟶ A.X) : defect α k l w = e := by
    let a := pairOver A (𝟙 T) w
    have hπ : a ≫ π = 𝟙 T := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, pairOver_left, relativeFst_left, pullback.lift_fst, Over.id_left]
    have hv : a ≫ v = w := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, pairOver_left, relativeSnd_left, pullback.lift_snd]
    have h := defect_precomp α a (π ≫ k) (π ≫ l) v
    rw [← Category.assoc, ← Category.assoc, hπ, Category.id_comp, Category.id_comp, hv] at h
    rw [h]
    change Units.map a.left.appTop.hom.toMonoidHom d = e
    have hd : relativeUnitsPullback A T e = d := relativeUnitsPullback_descend A _ T d
    rw [← hd]
    apply Units.ext
    change a.left.appTop.hom (π.left.appTop.hom (e : Γ(T.left, ⊤))) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, hπ,
      Over.id_left, Scheme.Hom.id_appTop]
    rfl
  exact (he x).trans (he 1).symm

/-- Two lifted translations compose up to the scalar two-cocycle on the parameter scheme. -/
lemma step_comp {T : Over S} (k l : T ⟶ (kernel q).X) (x y z : T ⟶ A.X)
    (hxy : act q x k = y) (hyz : act q y l = z) (hxz : act q x (k * l) = z) :
    step α k x y hxy ≫ step α l y z hyz =
      (scalar α k l : Γ(T.left, ⊤)) • step α (k * l) x z hxz := by
  rw [defect_spec α k l x y z hxy hyz hxz, defect_eq_scalar]

/-- Comparing the two parenthesizations of three lifted translations gives the two-cocycle law. -/
lemma scalar_cocycle {T : Over S} (k l m : T ⟶ (kernel q).X) :
    scalar α k l * scalar α (k * l) m = scalar α l m * scalar α k (l * m) := by
  let x : T ⟶ A.X := 1
  let y := act q x k
  let z := act q y l
  let w := act q z m
  have hxz : act q x (k * l) = z := (act_mul q x k l).symm
  have hyw : act q y (l * m) = w := (act_mul q y l m).symm
  have hxw : act q x (k * (l * m)) = w := by rw [← act_mul, hyw]
  have hxw' : act q x ((k * l) * m) = w := by rw [mul_assoc, hxw]
  have hu : step α ((k * l) * m) x w hxw' = step α (k * (l * m)) x w hxw := by
    congr 1
    exact mul_assoc _ _ _
  apply scalar_cancel (step α (k * (l * m)) x w hxw)
  change (↑(scalar α k l) * ↑(scalar α (k * l) m) : Γ(T.left, ⊤)) • _ =
    (↑(scalar α l m) * ↑(scalar α k (l * m)) : Γ(T.left, ⊤)) • _
  rw [mul_smul, mul_smul, ← hu, ← step_comp α (k * l) m x z w hxz rfl hxw',
    ← Linear.smul_comp, ← step_comp α k l x y z rfl rfl hxz, Category.assoc,
    step_comp α l m y z w rfl rfl hyw, Linear.comp_smul, step_comp α k (l * m) x y w rfl hyw hxw, hu]

end KernelTranslation

end Langlands.AbelianScheme
