import Langlands.GroupScheme.Torus.MultiplicativeTypePurelyInseparableStatement
import Langlands.GroupScheme.Descent.FpqcHomDescent
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.BaseChangeReflection
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-! # Proof: purely inseparable extensions do not change groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace MultiplicativeTypePurelyInseparable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-! ### Points with a chosen lift of the structure morphism -/

section Transfer

variable {B S : Scheme.{u}} (p : S ⟶ B)

/-- Precomposition with a morphism of test schemes, on point groups. -/
def precomp (G : GroupScheme B) {Y Y' : Over B} (a : Y' ⟶ Y) :
    (Y ⟶ G.X) →* (Y' ⟶ G.X) where
  toFun x := a ≫ x
  map_one' := MonObj.comp_one a
  map_mul' x y := MonObj.comp_mul a x y

@[simp] theorem precomp_apply (G : GroupScheme B) {Y Y' : Over B} (a : Y' ⟶ Y)
    (x : Y ⟶ G.X) : precomp G a x = a ≫ x := rfl

/-- A test scheme over `B` together with a lift `j` of its structure morphism through `p`. -/
def liftIso (Y : Over B) {j : Y.left ⟶ S} (hj : j ≫ p = Y.hom) :
    (Over.map p).obj (Over.mk j) ≅ Y :=
  Over.isoMk (Iso.refl _) (by simpa using hj.symm)

@[simp] theorem liftIso_hom_left (Y : Over B) {j : Y.left ⟶ S} (hj : j ≫ p = Y.hom) :
    (liftIso p Y hj).hom.left = 𝟙 _ := rfl

@[simp] theorem liftIso_inv_left (Y : Over B) {j : Y.left ⟶ S} (hj : j ≫ p = Y.hom) :
    (liftIso p Y hj).inv.left = 𝟙 _ := rfl

variable {G H : GroupScheme B} (f : (baseChange p).obj G ⟶ (baseChange p).obj H)

/-- Apply a homomorphism defined after base change along `p` to a point over `B`, using a
chosen lift `j` of the structure morphism of the test scheme. -/
def transfer (Y : Over B) (j : Y.left ⟶ S) (hj : j ≫ p = Y.hom) :
    (Y ⟶ G.X) →* (Y ⟶ H.X) :=
  (precomp H (liftIso p Y hj).inv).comp <|
    (baseChangePointsEquiv p H (Over.mk j)).toMonoidHom.comp <|
      ((pointsMap f).app (op (Over.mk j))).hom.comp <|
        (baseChangePointsEquiv p G (Over.mk j)).symm.toMonoidHom.comp
          (precomp G (liftIso p Y hj).hom)

theorem transfer_left (Y : Over B) (j : Y.left ⟶ S) (hj : j ≫ p = Y.hom) (x : Y ⟶ G.X) :
    (transfer p f Y j hj x).left =
      pullback.lift x.left j (by rw [Over.w x, hj]) ≫ f.hom.hom.left ≫
        pullback.fst H.X.hom p := by
  change 𝟙 _ ≫ ((((baseChangePointsEquiv p G (Over.mk j)).symm
      ((liftIso p Y hj).hom ≫ x)) ≫ f.hom.hom).left ≫ pullback.fst H.X.hom p) = _
  rw [Category.id_comp, Over.comp_left, Category.assoc]
  congr 1
  apply pullback.hom_ext
  · change (((Over.mapPullbackAdj p).homEquiv (Over.mk j) G.X)
      ((liftIso p Y hj).hom ≫ x)).left ≫ _ = _
    simp [Over.mapPullbackAdj]
  · change (((Over.mapPullbackAdj p).homEquiv (Over.mk j) G.X)
      ((liftIso p Y hj).hom ≫ x)).left ≫ _ = _
    simp [Over.mapPullbackAdj]

theorem transfer_congr (Y : Over B) {j j' : Y.left ⟶ S} (h : j = j')
    (hj : j ≫ p = Y.hom) (hj' : j' ≫ p = Y.hom) :
    transfer p f Y j hj = transfer p f Y j' hj' := by
  subst h
  rfl

theorem transfer_congr_apply (Y : Over B) {j j' : Y.left ⟶ S} (h : j = j')
    (hj : j ≫ p = Y.hom) (hj' : j' ≫ p = Y.hom) (x : Y ⟶ G.X) :
    transfer p f Y j hj x = transfer p f Y j' hj' x := by
  subst h
  rfl

theorem transfer_naturality {Y Y' : Over B} (a : Y' ⟶ Y) (j : Y.left ⟶ S)
    (hj : j ≫ p = Y.hom) (x : Y ⟶ G.X) :
    transfer p f Y' (a.left ≫ j) (by rw [Category.assoc, hj, Over.w a]) (a ≫ x) =
      a ≫ transfer p f Y j hj x := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, transfer_left, transfer_left]
  have e : pullback.lift (a ≫ x).left (a.left ≫ j)
      (by rw [Over.comp_left, Category.assoc, Over.w x, Category.assoc, hj]) =
      a.left ≫ pullback.lift x.left j (by rw [Over.w x, hj]) := by
    apply pullback.hom_ext <;> simp
  simp only [e, Category.assoc]

theorem transfer_naturality' {Y Y' : Over B} (a : Y' ⟶ Y) {j : Y.left ⟶ S}
    (hj : j ≫ p = Y.hom) {j' : Y'.left ⟶ S} (hj' : j' ≫ p = Y'.hom) (hjj' : a.left ≫ j = j')
    (x : Y ⟶ G.X) :
    transfer p f Y' j' hj' (a ≫ x) = a ≫ transfer p f Y j hj x := by
  subst hjj'
  exact transfer_naturality p f a j hj x

/-- Lifts of structure morphisms do not matter for the transfer of `f`. -/
def LiftIndependent : Prop :=
  ∀ (Y : Over B) (j₁ j₂ : Y.left ⟶ S) (h₁ : j₁ ≫ p = Y.hom) (h₂ : j₂ ≫ p = Y.hom)
    (x : Y ⟶ G.X), transfer p f Y j₁ h₁ x = transfer p f Y j₂ h₂ x

/-- Lift independence identifies the values above two points with the same image. -/
theorem comp_eq_of_fst_eq (hf : LiftIndependent p f) {Z : Scheme.{u}}
    (a b : Z ⟶ ((baseChange p).obj G).X.left)
    (hab : a ≫ pullback.fst G.X.hom p = b ≫ pullback.fst G.X.hom p) :
    a ≫ f.hom.hom.left ≫ pullback.fst H.X.hom p =
      b ≫ f.hom.hom.left ≫ pullback.fst H.X.hom p := by
  let Y : Over B := Over.mk (a ≫ pullback.fst G.X.hom p ≫ G.X.hom)
  let x : Y ⟶ G.X := Over.homMk (a ≫ pullback.fst G.X.hom p) (by simp [Y])
  have h₁ : (a ≫ pullback.snd G.X.hom p) ≫ p = Y.hom := by
    simp [Y, pullback.condition]
  have h₂ : (b ≫ pullback.snd G.X.hom p) ≫ p = Y.hom := by
    simp only [Y, Over.mk_hom, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, ← hab, Category.assoc]
  have h : (transfer p f Y _ h₁ x).left = (transfer p f Y _ h₂ x).left := by
    rw [hf Y _ _ h₁ h₂ x]
  rw [transfer_left, transfer_left] at h
  have ea : pullback.lift x.left (a ≫ pullback.snd G.X.hom p)
      (by rw [Over.w x, h₁]) = a := by
    apply pullback.hom_ext <;> simp [x]
  have eb : pullback.lift x.left (b ≫ pullback.snd G.X.hom p)
      (by rw [Over.w x, h₂]) = b := by
    apply pullback.hom_ext
    · simp [x, hab]
    · simp
  rw [ea, eb] at h
  exact h

@[reassoc] theorem baseChange_map_fst {T S' : Scheme.{u}} (r : T ⟶ S') {G' H' : GroupScheme S'}
    (a : G' ⟶ H') :
    ((baseChange r).map a).hom.hom.left ≫ pullback.fst H'.X.hom r =
      pullback.fst G'.X.hom r ≫ a.hom.hom.left :=
  pullback.lift_fst _ _ _

theorem hom_ext_original (C : GroupScheme B) {T : Scheme.{u}} (r : T ⟶ S)
    {G' : GroupScheme T} {a b : G' ⟶ (baseChange r).obj ((baseChange p).obj C)}
    (h : a.hom.hom.left ≫ pullback.fst ((baseChange p).obj C).X.hom r ≫
        pullback.fst C.X.hom p =
      b.hom.hom.left ≫ pullback.fst ((baseChange p).obj C).X.hom r ≫
        pullback.fst C.X.hom p) : a = b := by
  apply (cancel_mono (Descent.pullbackComparison p r (r ≫ p) rfl C).hom).mp
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      Descent.pullbackComparison_hom_fst] using h
  · exact (Over.w (a ≫ (Descent.pullbackComparison p r (r ≫ p) rfl C).hom).hom.hom).trans
      (Over.w (b ≫ (Descent.pullbackComparison p r (r ≫ p) rfl C).hom).hom.hom).symm

/-- Lift independence gives compatibility with the canonical descent data. -/
theorem compatible_of_liftIndependent (hf : LiftIndependent p f) :
    Descent.Compatible (Descent.canonicalDatum p G) (Descent.canonicalDatum p H) f := by
  have key := comp_eq_of_fst_eq p f hf
    (pullback.fst ((baseChange p).obj G).X.hom (Descent.fst p))
    ((Descent.canonicalOverlap p G).hom.hom.hom.left ≫
      pullback.fst ((baseChange p).obj G).X.hom (Descent.snd p))
    (by rw [Category.assoc, Descent.canonicalOverlap_fst])
  simp only [Category.assoc] at key
  apply hom_ext_original p H (Descent.snd p)
  simp only [Descent.canonicalDatum, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    Descent.canonicalOverlap_fst, baseChange_map_fst_assoc]
  exact key

end Transfer

/-! ### Points of split groups as characters -/

section Chars

variable {B : Scheme.{u}}

/-- Precomposition with an isomorphism of test schemes, on point groups. -/
def precompEquiv (G : GroupScheme B) {Y Y' : Over B} (i : Y' ≅ Y) :
    (Y ⟶ G.X) ≃* (Y' ⟶ G.X) where
  toFun x := i.hom ≫ x
  invFun x := i.inv ≫ x
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := MonObj.comp_mul i.hom x y

/-- Postcomposition with an isomorphism of group schemes, on point groups. -/
def postcompEquiv {G' H' : GroupScheme B} (e : G' ≅ H') (T : Over B) :
    (T ⟶ G'.X) ≃* (T ⟶ H'.X) where
  toFun x := x ≫ e.hom.hom.hom
  invFun x := x ≫ e.inv.hom.hom
  left_inv x := by
    change x ≫ e.hom.hom.hom ≫ e.inv.hom.hom = x
    rw [← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv x := by
    change x ≫ e.inv.hom.hom ≫ e.hom.hom.hom = x
    rw [← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  map_mul' x y := ((pointsMap e.hom).app (op T)).hom.map_mul x y

variable {RK : CommRingCat.{u}} (pK : Spec RK ⟶ B) {G : GroupScheme B}
  {Λ : Type u} [AddCommGroup Λ]
  (e : (baseChange pK).obj G ≅ (Diagonalizable.groupScheme RK Λ).toGrp)

/-- Points over a test scheme with a lift `σ` to the splitting base, as characters. -/
def chars (Y : Over B) (σ : Y.left ⟶ Spec RK) (hσ : σ ≫ pK = Y.hom) :
    (Y ⟶ G.X) ≃* (Multiplicative Λ →* (Γ(Y.left, ⊤))ˣ) :=
  ((precompEquiv G (liftIso pK Y hσ)).trans
    (baseChangePointsEquiv pK G (Over.mk σ)).symm).trans
    ((postcompEquiv e (Over.mk σ)).trans
      (Diagonalizable.characterPointsEquiv RK Λ (Over.mk σ)))

theorem chars_naturality {Y Y' : Over B} (a : Y' ⟶ Y) {σ : Y.left ⟶ Spec RK}
    (hσ : σ ≫ pK = Y.hom) {σ' : Y'.left ⟶ Spec RK} (hσ' : σ' ≫ pK = Y'.hom)
    (hσσ' : a.left ≫ σ = σ') (x : Y ⟶ G.X) (m : Multiplicative Λ) :
    chars pK e Y' σ' hσ' (a ≫ x) m =
      Units.map a.left.appTop.hom.toMonoidHom (chars pK e Y σ hσ x m) := by
  subst hσσ'
  let a' : Over.mk (a.left ≫ σ) ⟶ Over.mk σ := Over.homMk a.left rfl
  have h₁ : (baseChangePointsEquiv pK G (Over.mk (a.left ≫ σ))).symm
      ((liftIso pK Y' hσ').hom ≫ a ≫ x) =
      a' ≫ (baseChangePointsEquiv pK G (Over.mk σ)).symm ((liftIso pK Y hσ).hom ≫ x) := by
    apply (baseChangePointsEquiv pK G (Over.mk (a.left ≫ σ))).injective
    rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality,
      MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    simp [a']
  change Diagonalizable.characterPointsEquiv RK Λ (Over.mk (a.left ≫ σ))
      ((baseChangePointsEquiv pK G (Over.mk (a.left ≫ σ))).symm
        ((liftIso pK Y' hσ').hom ≫ a ≫ x) ≫ e.hom.hom.hom) m = _
  rw [h₁, Category.assoc]
  exact Diagonalizable.characterPointsEquiv_naturality RK Λ a' _ m.toAdd

end Chars


/-! ### Rigidity of transfers over a ring with a nil comparison map -/

section Rigidity

open DiagonalizableCharacter CharacterAction

variable {Bk S : Scheme.{u}} (p : S ⟶ Bk) {R : CommRingCat.{u}} (rU : Spec R ⟶ Bk)

/-- A test scheme over `Spec R`, viewed over `Bk` through `rU`. -/
abbrev under (V : Over (Spec R)) : Over Bk := Over.mk (V.hom ≫ rU)

/-- A morphism of test schemes over `Spec R`, viewed over `Bk`. -/
def underMap {V V' : Over (Spec R)} (a : V' ⟶ V) : under rU V' ⟶ under rU V :=
  Over.homMk a.left (by
    change a.left ≫ V.hom ≫ rU = V'.hom ≫ rU
    rw [← Category.assoc, Over.w a])

theorem lift_comp_eq {X T : Scheme.{u}} {pT : T ⟶ Bk} {σ : Spec R ⟶ T} (h : σ ≫ pT = rU)
    (ψ : X ⟶ Spec R) : (ψ ≫ σ) ≫ pT = (Over.mk (ψ ≫ rU)).hom := by
  rw [Category.assoc, h]
  rfl

variable {RG RH : CommRingCat.{u}} {pG : Spec RG ⟶ Bk} {pH : Spec RH ⟶ Bk}
  {ΛG ΛH : Type u} [AddCommGroup ΛG] [AddCommGroup ΛH] {G H : GroupScheme Bk}
  (eG : (baseChange pG).obj G ≅ (Diagonalizable.groupScheme RG ΛG).toGrp)
  (eH : (baseChange pH).obj H ≅ (Diagonalizable.groupScheme RH ΛH).toGrp)
  {σG : Spec R ⟶ Spec RG} (hσG : σG ≫ pG = rU) {σH : Spec R ⟶ Spec RH}
  (hσH : σH ≫ pH = rU) (f : (baseChange p).obj G ⟶ (baseChange p).obj H)

/-- The homomorphism on points of `D_R(ΛG)` attached to a lift `q` of `rU` and a character `m`
of `H`: transport the point to `G` with `eG`, transfer it along `f` using `q`, and evaluate the
resulting point of `H`, read through `eH`, at `m`. -/
def natApp (q : Spec R ⟶ S) (hq : q ≫ p = rU) (m : ΛH) (V : Over (Spec R)) :
    (V ⟶ (Diagonalizable.groupScheme R ΛG).X) →* (Γ(V.left, ⊤))ˣ where
  toFun x := chars pH eH (under rU V) (V.hom ≫ σH) (lift_comp_eq rU hσH V.hom)
    (transfer p f (under rU V) (V.hom ≫ q) (lift_comp_eq rU hq V.hom)
      ((chars pG eG (under rU V) (V.hom ≫ σG) (lift_comp_eq rU hσG V.hom)).symm
        (Diagonalizable.characterPointsEquiv R ΛG V x))) (.ofAdd m)
  map_one' := by simp only [map_one, MonoidHom.one_apply]
  map_mul' x y := by simp only [map_mul, MonoidHom.mul_apply]

theorem natApp_apply (q : Spec R ⟶ S) (hq : q ≫ p = rU) (m : ΛH) (V : Over (Spec R))
    (x : V ⟶ (Diagonalizable.groupScheme R ΛG).X) :
    natApp p rU eG eH hσG hσH f q hq m V x =
      chars pH eH (under rU V) (V.hom ≫ σH) (lift_comp_eq rU hσH V.hom)
        (transfer p f (under rU V) (V.hom ≫ q) (lift_comp_eq rU hq V.hom)
          ((chars pG eG (under rU V) (V.hom ≫ σG) (lift_comp_eq rU hσG V.hom)).symm
            (Diagonalizable.characterPointsEquiv R ΛG V x))) (.ofAdd m) := rfl

theorem chars_symm_naturality {V V' : Over (Spec R)} (a : V' ⟶ V)
    (x : V ⟶ (Diagonalizable.groupScheme R ΛG).X) :
    (chars pG eG (under rU V') (V'.hom ≫ σG) (lift_comp_eq rU hσG V'.hom)).symm
        (Diagonalizable.characterPointsEquiv R ΛG V' (a ≫ x)) =
      underMap rU a ≫ (chars pG eG (under rU V) (V.hom ≫ σG) (lift_comp_eq rU hσG V.hom)).symm
        (Diagonalizable.characterPointsEquiv R ΛG V x) := by
  apply (chars pG eG (under rU V') (V'.hom ≫ σG) (lift_comp_eq rU hσG V'.hom)).injective
  apply MonoidHom.ext
  intro m'
  rw [MulEquiv.apply_symm_apply, chars_naturality pG eG (underMap rU a)
    (lift_comp_eq rU hσG V.hom) (lift_comp_eq rU hσG V'.hom)
    (by change a.left ≫ V.hom ≫ σG = V'.hom ≫ σG; rw [← Category.assoc, Over.w a]),
    MulEquiv.apply_symm_apply]
  exact Diagonalizable.characterPointsEquiv_naturality R ΛG a x m'.toAdd

/-- The natural family of units attached to a lift `q` of `rU` and a character `m` of `H`. -/
def natUnits (q : Spec R ⟶ S) (hq : q ≫ p = rU) (m : ΛH) : NaturalUnits R ΛG where
  app := natApp p rU eG eH hσG hσH f q hq m
  naturality {V V'} a x := by
    rw [natApp_apply, natApp_apply, chars_symm_naturality rU eG hσG a x,
      transfer_naturality' p f (underMap rU a) (lift_comp_eq rU hq V.hom)
        (lift_comp_eq rU hq V'.hom)
        (by change a.left ≫ V.hom ≫ q = V'.hom ≫ q; rw [← Category.assoc, Over.w a])]
    exact chars_naturality pH eH (underMap rU a) (lift_comp_eq rU hσH V.hom)
      (lift_comp_eq rU hσH V'.hom)
      (by change a.left ≫ V.hom ≫ σH = V'.hom ≫ σH; rw [← Category.assoc, Over.w a]) _ _

theorem natUnits_app (q : Spec R ⟶ S) (hq : q ≫ p = rU) (m : ΛH) (V : Over (Spec R))
    (x : V ⟶ (Diagonalizable.groupScheme R ΛG).X) :
    (natUnits p rU eG eH hσG hσH f q hq m).app V x =
      chars pH eH (under rU V) (V.hom ≫ σH) (lift_comp_eq rU hσH V.hom)
        (transfer p f (under rU V) (V.hom ≫ q) (lift_comp_eq rU hq V.hom)
          ((chars pG eG (under rU V) (V.hom ≫ σG) (lift_comp_eq rU hσG V.hom)).symm
            (Diagonalizable.characterPointsEquiv R ΛG V x))) (.ofAdd m) := rfl

theorem natUnits_app_congr {q₁ q₂ : Spec R ⟶ S} (h₁ : q₁ ≫ p = rU) (h₂ : q₂ ≫ p = rU)
    (m : ΛH) (V : Over (Spec R)) (hV : V.hom ≫ q₁ = V.hom ≫ q₂)
    (x : V ⟶ (Diagonalizable.groupScheme R ΛG).X) :
    (natUnits p rU eG eH hσG hσH f q₁ h₁ m).app V x =
      (natUnits p rU eG eH hσG hσH f q₂ h₂ m).app V x := by
  rw [natUnits_app, natUnits_app,
    transfer_congr p f _ hV (lift_comp_eq rU h₁ V.hom) (lift_comp_eq rU h₂ V.hom)]

include eG eH hσG hσH in
/-- **Rigidity.** If `R` maps to `D` with nil kernel and two lifts `q₁`, `q₂` of `rU` agree
on `Spec D`, then they give the same transfer of `f` on every test scheme over `Spec R`. -/
theorem transfer_eq_of_nil {D : CommAlgCat.{u} R} (π : baseAlg R ⟶ D)
    (hker : ∀ x, π.hom x = 0 → IsNilpotent x)
    {q₁ q₂ : Spec R ⟶ S} (h₁ : q₁ ≫ p = rU) (h₂ : q₂ ≫ p = rU)
    (hD : Spec.map (CommRingCat.ofHom (algebraMap R D)) ≫ q₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) ≫ q₂)
    (V : Over (Spec R)) (y : under rU V ⟶ G.X) :
    transfer p f _ (V.hom ≫ q₁) (lift_comp_eq rU h₁ V.hom) y =
      transfer p f _ (V.hom ≫ q₂) (lift_comp_eq rU h₂ V.hom) y := by
  have hB : (NaturalUnits.affine (algebra (M := ΛG) D)).hom ≫ q₁ =
      (NaturalUnits.affine (algebra (M := ΛG) D)).hom ≫ q₂ := by
    have e : CommRingCat.ofHom (algebraMap R D) ≫
        CommRingCat.ofHom (constant (M := ΛG) D).hom.toRingHom =
        CommRingCat.ofHom (algebraMap R (algebra (M := ΛG) D)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (constant (M := ΛG) D).hom.commutes r
    change Spec.map (CommRingCat.ofHom (algebraMap R (algebra (M := ΛG) D))) ≫ q₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R (algebra (M := ΛG) D))) ≫ q₂
    rw [← e, Spec.map_comp, Category.assoc, Category.assoc, hD]
  have hv : ∀ m, (natUnits p rU eG eH hσG hσH f q₁ h₁ m).value =
      (natUnits p rU eG eH hσG hσH f q₂ h₂ m).value := by
    intro m
    apply isGrouplike_lift_unique π hker (NaturalUnits.isGrouplike_value _)
      (NaturalUnits.isGrouplike_value _)
    change (evaluate (π ≫ constant D) (universal (M := ΛG) D)).hom _ =
      (evaluate (π ≫ constant D) (universal (M := ΛG) D)).hom _
    rw [evaluate_eq_lift, evaluate_eq_lift]
    apply NaturalUnits.toSections_injective (algebra (M := ΛG) D)
    rw [NaturalUnits.toSections_lift, NaturalUnits.toSections_lift,
      natUnits_app_congr p rU eG eH hσG hσH f h₁ h₂ m _ hB]
  have happ : ∀ m (x : V ⟶ (Diagonalizable.groupScheme R ΛG).X),
      (natUnits p rU eG eH hσG hσH f q₁ h₁ m).app V x =
        (natUnits p rU eG eH hσG hσH f q₂ h₂ m).app V x := by
    intro m x
    apply Units.ext
    rw [NaturalUnits.app_eq, NaturalUnits.app_eq, hv m]
  apply (chars pH eH (under rU V) (V.hom ≫ σH) (lift_comp_eq rU hσH V.hom)).injective
  apply MonoidHom.ext
  intro m
  have h := happ m.toAdd ((Diagonalizable.characterPointsEquiv R ΛG V).symm
    (chars pG eG (under rU V) (V.hom ≫ σG) (lift_comp_eq rU hσG V.hom) y))
  rw [natUnits_app, natUnits_app, MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply] at h
  exact h

include eG eH hσG hσH in
/-- Rigidity on a test scheme over `Bk` with a chosen map `ψ` to `Spec R`. -/
theorem transfer_eq_of_nil' {D : CommAlgCat.{u} R} (π : baseAlg R ⟶ D)
    (hker : ∀ x, π.hom x = 0 → IsNilpotent x)
    {q₁ q₂ : Spec R ⟶ S} (h₁ : q₁ ≫ p = rU) (h₂ : q₂ ≫ p = rU)
    (hD : Spec.map (CommRingCat.ofHom (algebraMap R D)) ≫ q₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R D)) ≫ q₂)
    (Y : Over Bk) (ψ : Y.left ⟶ Spec R) (hψ : ψ ≫ rU = Y.hom) (y : Y ⟶ G.X) :
    transfer p f Y (ψ ≫ q₁) (by rw [Category.assoc, h₁, hψ]) y =
      transfer p f Y (ψ ≫ q₂) (by rw [Category.assoc, h₂, hψ]) y := by
  let i : under rU (Over.mk ψ) ≅ Y := Over.isoMk (Iso.refl _) (by simp [hψ])
  have e : ∀ (q : Spec R ⟶ S) (hq : q ≫ p = rU),
      transfer p f Y (ψ ≫ q) (by rw [Category.assoc, hq, hψ]) y =
        i.inv ≫ transfer p f (under rU (Over.mk ψ)) ((Over.mk ψ).hom ≫ q)
          (lift_comp_eq rU hq _) (i.hom ≫ y) := by
    intro q hq
    rw [← transfer_naturality' p f i.inv (lift_comp_eq rU hq _)
      (by rw [Category.assoc, hq, hψ]) (by simp [i]), Iso.inv_hom_id_assoc]
  rw [e q₁ h₁, e q₂ h₂, transfer_eq_of_nil p rU eG eH hσG hσH f π hker h₁ h₂ hD]

end Rigidity

/-! ### Purely inseparable field extensions -/

section Field

open Algebra.TensorProduct in
/-- Two field extensions of `k` admit `k`-embeddings into a common field. -/
theorem exists_field_algHom₂ (k K₁ K₂ : Type u) [Field k] [Field K₁] [Field K₂] [Algebra k K₁]
    [Algebra k K₂] : ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω),
      Nonempty (K₁ →ₐ[k] Ω) ∧ Nonempty (K₂ →ₐ[k] Ω) := by
  have : Nontrivial (K₁ ⊗[k] K₂) := nontrivial_of_algebraMap_injective_of_isDomain k K₁ K₂
    (algebraMap k K₁).injective (algebraMap k K₂).injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K₁ ⊗[k] K₂)
  let : Field ((K₁ ⊗[k] K₂) ⧸ m) := Ideal.Quotient.field m
  exact ⟨(K₁ ⊗[k] K₂) ⧸ m, inferInstance, inferInstance,
    ⟨(Ideal.Quotient.mkₐ k m).comp includeLeft⟩, ⟨(Ideal.Quotient.mkₐ k m).comp includeRight⟩⟩

/-- Three field extensions of `k` admit `k`-embeddings into a common field. -/
theorem exists_field_algHom₃ (k K₁ K₂ K₃ : Type u) [Field k] [Field K₁] [Field K₂] [Field K₃]
    [Algebra k K₁] [Algebra k K₂] [Algebra k K₃] : ∃ (Ω : Type u) (_ : Field Ω) (_ : Algebra k Ω),
      Nonempty (K₁ →ₐ[k] Ω) ∧ Nonempty (K₂ →ₐ[k] Ω) ∧ Nonempty (K₃ →ₐ[k] Ω) := by
  obtain ⟨L, _, _, ⟨γ₂⟩, ⟨γ₃⟩⟩ := exists_field_algHom₂ k K₂ K₃
  obtain ⟨Ω, _, _, ⟨γ₁⟩, ⟨γL⟩⟩ := exists_field_algHom₂ k K₁ L
  exact ⟨Ω, inferInstance, inferInstance, ⟨γ₁⟩, ⟨γL.comp γ₂⟩, ⟨γL.comp γ₃⟩⟩

theorem spec_comp_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) (h : A →+* C) (hfg : ∀ a, g (f a) = h a) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact hfg

variable {k k' Ω : Type u} [Field k] [Field k'] [Field Ω] [Algebra k k'] [Algebra k Ω]

/-- The multiplication map `k' ⊗[k] Ω → Ω` attached to a `k`-embedding `γ : k' → Ω`. -/
def mulMap (γ : k' →ₐ[k] Ω) : k' ⊗[k] Ω →ₐ[k] Ω :=
  Algebra.TensorProduct.lift γ (AlgHom.id k Ω) (fun _ _ => Commute.all _ _)

theorem mulMap_tmul (γ : k' →ₐ[k] Ω) (a : k') (ω : Ω) : mulMap γ (a ⊗ₜ ω) = γ a * ω := by
  simp [mulMap]

/-- For a purely inseparable `k'`, every element of `k' ⊗[k] Ω` differs from the image of its
product under `mulMap γ` by a nilpotent element. -/
theorem isNilpotent_sub_mulMap [IsPurelyInseparable k k'] (γ : k' →ₐ[k] Ω) (x : k' ⊗[k] Ω) :
    IsNilpotent (x - Algebra.TensorProduct.includeRight (mulMap γ x)) := by
  have : Nontrivial (k' ⊗[k] Ω) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k k' Ω
      (algebraMap k k').injective (algebraMap k Ω).injective
  have : ExpChar (k' ⊗[k] Ω) (ringExpChar k) :=
    expChar_of_injective_ringHom (algebraMap k (k' ⊗[k] Ω)).injective (ringExpChar k)
  induction x using TensorProduct.inductionOn with
  | tmul a ω =>
    have ha : IsNilpotent (a ⊗ₜ[k] (1 : Ω) - 1 ⊗ₜ γ a) := by
      obtain ⟨n, r, hr⟩ := IsPurelyInseparable.pow_mem k (ringExpChar k) a
      refine ⟨ringExpChar k ^ n, ?_⟩
      rw [sub_pow_expChar_pow, Algebra.TensorProduct.tmul_pow, one_pow,
        Algebra.TensorProduct.tmul_pow, one_pow, ← map_pow, ← hr, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        sub_self]
    have e : a ⊗ₜ[k] ω - Algebra.TensorProduct.includeRight (mulMap γ (a ⊗ₜ ω)) =
        (a ⊗ₜ[k] (1 : Ω) - 1 ⊗ₜ γ a) * (1 ⊗ₜ ω) := by
      simp only [mulMap_tmul, Algebra.TensorProduct.includeRight_apply, sub_mul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    exact (Commute.all _ _).isNilpotent_mul_right ha
  | add x y hx hy =>
    rw [map_add, map_add, add_sub_add_comm]
    exact (Commute.all _ _).isNilpotent_add hx hy

theorem isNilpotent_of_mulMap_eq_zero [IsPurelyInseparable k k'] (γ : k' →ₐ[k] Ω)
    (x : k' ⊗[k] Ω) (hx : mulMap γ x = 0) : IsNilpotent x := by
  simpa [hx] using isNilpotent_sub_mulMap γ x

omit [Field Ω] [Algebra k Ω] in
theorem q₁_comp (Ω : Type u) [Field Ω] [Algebra k Ω] :
    Spec.map (CommRingCat.ofHom (algebraMap k' (k' ⊗[k] Ω))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k k')) =
        Spec.map (CommRingCat.ofHom (algebraMap k (k' ⊗[k] Ω))) :=
  spec_comp_eq _ _ _ fun r => (IsScalarTower.algebraMap_apply k k' (k' ⊗[k] Ω) r).symm

omit [Field k'] [Algebra k k'] in
theorem incl_comp (k' : Type u) [Field k'] [Algebra k k'] {K : Type u} [Field K] [Algebra k K]
    (γK : K →ₐ[k] Ω) :
    Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight : Ω →ₐ[k] k' ⊗[k] Ω).toRingHom.comp γK.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        Spec.map (CommRingCat.ofHom (algebraMap k (k' ⊗[k] Ω))) :=
  spec_comp_eq _ _ _ fun r => by
    change Algebra.TensorProduct.includeRight (γK (algebraMap k K r)) =
      algebraMap k (k' ⊗[k] Ω) r
    rw [γK.commutes, AlgHom.commutes]

/-- Rigidity over `k' ⊗[k] Ω`: the two lifts `k' → k' ⊗[k] Ω` (the left inclusion, and
`γ` followed by the right inclusion) give the same transfer of `f`. -/
theorem transfer_eq_tensor [IsPurelyInseparable k k'] (γ : k' →ₐ[k] Ω)
    {KG KH : Type u} [Field KG] [Field KH] [Algebra k KG] [Algebra k KH]
    (γG : KG →ₐ[k] Ω) (γH : KH →ₐ[k] Ω) {ΛG ΛH : Type u} [AddCommGroup ΛG] [AddCommGroup ΛH]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (eG : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k KG)))).obj G ≅
      (Diagonalizable.groupScheme (CommRingCat.of KG) ΛG).toGrp)
    (eH : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k KH)))).obj H ≅
      (Diagonalizable.groupScheme (CommRingCat.of KH) ΛH).toGrp)
    (f : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj G ⟶
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj H)
    (Y : Over (Spec (CommRingCat.of k))) (ψ : Y.left ⟶ Spec (CommRingCat.of (k' ⊗[k] Ω)))
    (hψ : ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (k' ⊗[k] Ω))) = Y.hom)
    (y : Y ⟶ G.X) :
    transfer (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f Y
        (ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (k' ⊗[k] Ω))))
        (by rw [Category.assoc, q₁_comp, hψ]) y =
      transfer (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f Y
        (ψ ≫ Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : Ω →ₐ[k] k' ⊗[k] Ω).toRingHom.comp
            γ.toRingHom)))
        (by rw [Category.assoc, incl_comp, hψ]) y := by
  let : Algebra (k' ⊗[k] Ω) Ω := (mulMap γ).toRingHom.toAlgebra
  have hD₁ : Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of (k' ⊗[k] Ω))
        (CommAlgCat.of (CommRingCat.of (k' ⊗[k] Ω)) Ω))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k' (k' ⊗[k] Ω))) =
        Spec.map (CommRingCat.ofHom γ.toRingHom) :=
    spec_comp_eq _ _ _ fun a => by
      change mulMap γ (a ⊗ₜ 1) = γ a
      rw [mulMap_tmul, mul_one]
  have hD₂ : Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of (k' ⊗[k] Ω))
        (CommAlgCat.of (CommRingCat.of (k' ⊗[k] Ω)) Ω))) ≫
      Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : Ω →ₐ[k] k' ⊗[k] Ω).toRingHom.comp
          γ.toRingHom)) =
        Spec.map (CommRingCat.ofHom γ.toRingHom) :=
    spec_comp_eq _ _ _ fun a => by
      change mulMap γ (1 ⊗ₜ γ a) = γ a
      rw [mulMap_tmul, map_one, one_mul]
  exact transfer_eq_of_nil' (Spec.map (CommRingCat.ofHom (algebraMap k k')))
    (Spec.map (CommRingCat.ofHom (algebraMap k (k' ⊗[k] Ω)))) eG eH (incl_comp k' γG)
    (incl_comp k' γH) f (D := CommAlgCat.of (CommRingCat.of (k' ⊗[k] Ω)) Ω)
    (CommAlgCat.ofHom (Algebra.ofId _ _)) (fun x hx => isNilpotent_of_mulMap_eq_zero γ x hx)
    (q₁_comp Ω) (incl_comp k' γ) (hD₁.trans hD₂.symm) Y ψ hψ y

/-- **Lift independence** for groups of multiplicative type and a purely inseparable
extension. -/
theorem liftIndependent [IsPurelyInseparable k k'] {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsMultiplicativeType G) (hH : IsMultiplicativeType H)
    (f : (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj G ⟶
      (baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).obj H) :
    LiftIndependent (Spec.map (CommRingCat.ofHom (algebraMap k k'))) f := by
  obtain ⟨KG, _, _, ΛG, _, _, ⟨eG⟩⟩ := hG
  obtain ⟨KH, _, _, ΛH, _, _, ⟨eH⟩⟩ := hH
  obtain ⟨Ω, _, _, ⟨γ⟩, ⟨γG⟩, ⟨γH⟩⟩ := exists_field_algHom₃ k k' KG KH
  intro Y j₁ j₂ hj₁ hj₂ x
  obtain ⟨Z, g, s, hgs, hg⟩ : ∃ (Z : Scheme.{u}) (g : Z ⟶ Y.left)
      (s : Z ⟶ Spec (CommRingCat.of Ω)),
      g ≫ Y.hom = s ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧ Epi g := by
    obtain ⟨hs, hfl, hqc⟩ := fieldExtension_fpqc k Ω
    exact ⟨_, pullback.fst _ _, pullback.snd _ _, pullback.condition, inferInstance⟩
  let a : Over.mk (g ≫ Y.hom) ⟶ Y := Over.homMk g rfl
  have hs' : (s ≫ Spec.map (CommRingCat.ofHom γ.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k k')) = (Over.mk (g ≫ Y.hom)).hom := by
    rw [Category.assoc, spec_comp_eq _ _ (algebraMap k Ω) (fun r => γ.commutes r), ← hgs]
    rfl
  have key : ∀ (j : Y.left ⟶ Spec (CommRingCat.of k'))
      (hj : j ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) = Y.hom),
      a ≫ transfer _ f Y j hj x =
        transfer _ f (Over.mk (g ≫ Y.hom)) (s ≫ Spec.map (CommRingCat.ofHom γ.toRingHom))
          hs' (a ≫ x) := by
    intro j hj
    have w : (g ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap k k')) =
        s ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) := by
      rw [Category.assoc, hj, hgs]
    obtain ⟨ψ, hψ₁, hψs, hψ⟩ : ∃ ψ : Z ⟶ Spec (CommRingCat.of (k' ⊗[k] Ω)),
        ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k' (k' ⊗[k] Ω))) = g ≫ j ∧
        ψ ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Ω →ₐ[k] k' ⊗[k] Ω).toRingHom) = s ∧
        ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k (k' ⊗[k] Ω))) =
          (Over.mk (g ≫ Y.hom)).hom := by
      refine ⟨pullback.lift (g ≫ j) s w ≫ (pullbackSpecIso k k' Ω).hom, ?_, ?_, ?_⟩
      · rw [Category.assoc, pullbackSpecIso_hom_fst', pullback.lift_fst]
      · exact (Category.assoc _ _ _).trans ((congrArg (fun t => pullback.lift (g ≫ j) s w ≫ t)
          (pullbackSpecIso_hom_snd k k' Ω)).trans (pullback.lift_snd _ _ _))
      · rw [Category.assoc, pullbackSpecIso_hom_base, pullback.lift_fst_assoc, Category.assoc, hj]
        rfl
    have hψ₂ : ψ ≫ Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : Ω →ₐ[k] k' ⊗[k] Ω).toRingHom.comp
          γ.toRingHom)) = s ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) := by
      rw [← spec_comp_eq γ.toRingHom
        (Algebra.TensorProduct.includeRight : Ω →ₐ[k] k' ⊗[k] Ω).toRingHom _ (fun _ => rfl),
        ← Category.assoc, hψs]
    rw [← transfer_naturality' _ f a hj (j' := g ≫ j) (by rw [Category.assoc, hj]; rfl) rfl]
    exact (transfer_congr_apply _ f _ hψ₁.symm _ _ (a ≫ x)).trans
      ((transfer_eq_tensor γ γG γH eG eH f _ ψ hψ (a ≫ x)).trans
        (transfer_congr_apply _ f _ hψ₂ _ _ (a ≫ x)))
  apply Over.OverMorphism.ext
  apply (cancel_epi g).mp
  have hl := congrArg CommaMorphism.left ((key j₁ hj₁).trans (key j₂ hj₂).symm)
  exact hl

end Field

end MultiplicativeTypePurelyInseparable

open MultiplicativeTypePurelyInseparable in
/-- **Purely inseparable descent for groups of multiplicative type.** -/
theorem multiplicativeTypePurelyInseparable :
    MultiplicativeTypePurelyInseparableStatement.{u} := by
  intro k k' _ _ _ hk
  have part2 : ∀ G H : GroupScheme (Spec (CommRingCat.of k)),
      IsMultiplicativeType G → IsMultiplicativeType H →
      Function.Bijective (fun f : G ⟶ H =>
        (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).map f) := by
    intro G H hG hH
    obtain ⟨hs, hfl, hqc⟩ := fieldExtension_fpqc k k'
    refine ⟨fun a b hab => ?_, fun f => ?_⟩
    · have hc := Descent.canonicalDatum_compatible
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) a
      exact (Descent.FpqcHomDescent.unique _ _ hc a rfl).trans
        (Descent.FpqcHomDescent.unique _ _ hc b hab.symm).symm
    · have hc := compatible_of_liftIndependent _ f (liftIndependent hG hH f)
      exact ⟨Descent.FpqcHomDescent.hom _ f hc, Descent.FpqcHomDescent.baseChange_hom _ f hc⟩
  refine ⟨fun H Λ _ _ ⟨e⟩ => ?_, part2⟩
  let p := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let bD := Diagonalizable.baseChangeIso p Λ
  have hH : IsMultiplicativeType H := ⟨k', inferInstance, inferInstance, Λ, inferInstance,
    inferInstance, ⟨e⟩⟩
  have hD : IsMultiplicativeType (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp :=
    ⟨k', inferInstance, inferInstance, Λ, inferInstance, inferInstance, ⟨bD⟩⟩
  obtain ⟨φ, hφ⟩ := (part2 _ _ hH hD).2 (e ≪≫ bD.symm).hom
  obtain ⟨ψ, hψ⟩ := (part2 _ _ hD hH).2 (e ≪≫ bD.symm).inv
  have h₁ : (GroupScheme.baseChange p).map φ = (e ≪≫ bD.symm).hom := hφ
  have h₂ : (GroupScheme.baseChange p).map ψ = (e ≪≫ bD.symm).inv := hψ
  refine ⟨Λ, inferInstance, inferInstance, ⟨Iso.mk φ ψ ?_ ?_⟩⟩
  · apply (part2 _ _ hH hH).1
    change (GroupScheme.baseChange p).map (φ ≫ ψ) = (GroupScheme.baseChange p).map (𝟙 H)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, h₁, h₂,
      Iso.hom_inv_id]
  · apply (part2 _ _ hD hD).1
    change (GroupScheme.baseChange p).map (ψ ≫ φ) = (GroupScheme.baseChange p).map (𝟙 _)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, h₁, h₂,
      Iso.inv_hom_id]

end Langlands.GroupScheme
