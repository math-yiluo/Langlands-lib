import Langlands.GroupScheme.LinearAdditiveExtension.ClosedAdditivePolynomial
import Langlands.AlgebraicGeometry.AffineAdditiveCocycle
import Langlands.AbelianScheme.Kernel

/-! # An equivariant additive function on an extension by a closed additive subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LinearAdditiveExtension

open RelativeRoot.AdditiveGroupQuotient

variable {k : Type u} [Field k]

local notation "𝔾ₐ" => VectorGroup.groupScheme (CommRingCat.of k) 1

/-! ### Coordinates on every test scheme -/

section Coordinates

variable {T T' : Over (Spec (CommRingCat.of k))}

/-- The coordinate of an additive point on a test scheme. -/
abbrev cd (v : T ⟶ (𝔾ₐ).X) : Γ(T.left, ⊤) :=
  coord ClosedAdditivePolynomial.ga v

theorem cd_comp (b : T' ⟶ T) (v : T ⟶ (𝔾ₐ).X) : cd (b ≫ v) = b.left.appTop.hom (cd v) :=
  coord_comp _ ClosedAdditivePolynomial.ga_comp b v

@[simp] theorem cd_mul (v w : T ⟶ (𝔾ₐ).X) : cd (v * w) = cd v + cd w :=
  coord_mul _ v w

@[simp] theorem cd_one : cd (1 : T ⟶ (𝔾ₐ).X) = 0 :=
  coord_one _

@[simp] theorem cd_inv (v : T ⟶ (𝔾ₐ).X) : cd v⁻¹ = -cd v := by
  have h := cd_mul v⁻¹ v
  rw [inv_mul_cancel, cd_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem cd_injective {v w : T ⟶ (𝔾ₐ).X} (h : cd v = cd w) : v = w :=
  coord_injective _ h

@[simp] theorem cd_ofCoord (c : Γ(T.left, ⊤)) :
    cd (ofCoord ClosedAdditivePolynomial.ga c : T ⟶ (𝔾ₐ).X) = c :=
  coord_ofCoord _ c

theorem cd_act {S : CommGroupScheme (Spec (CommRingCat.of k))} (χ : characterLattice S)
    (s : T ⟶ S.X) (v : T ⟶ (𝔾ₐ).X) :
    cd ((VectorGroup.weightAction (n := 1) χ).act s v) = VectorGroup.charValue χ T s * cd v := by
  change ((VectorGroup.coordinates (CommRingCat.of k) 1 T
    ((VectorGroup.weightAction (n := 1) χ).act s v)).toAdd 0) = _
  rw [VectorGroup.coordinates_weightAction_act]
  rfl

theorem charValue_mul_inv {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) (s : T ⟶ S.X) :
    VectorGroup.charValue χ T s * VectorGroup.charValue χ T s⁻¹ = 1 := by
  rw [← VectorGroup.charValue_mul, mul_inv_cancel, VectorGroup.charValue_one]

theorem charValue_pow {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (χ : characterLattice S) (s : T ⟶ S.X) (n : ℕ) :
    VectorGroup.charValue χ T (s ^ n) = VectorGroup.charValue χ T s ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, VectorGroup.charValue_one]
  | succ n ih => rw [pow_succ, pow_succ, VectorGroup.charValue_mul, ih]

end Coordinates

/-! ### The extension data -/

variable {Λ : Type u} [AddCommGroup Λ]

local notation "𝔻" => Diagonalizable.groupScheme (CommRingCat.of k) Λ

variable {E : GroupScheme (Spec (CommRingCat.of k))}
  (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
  (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1)
  (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))

section Points

variable {T T' : Over (Spec (CommRingCat.of k))}

/-- The value of `χ` at the image of a point of `E`. -/
abbrev chi (g : T ⟶ E.X) : Γ(T.left, ⊤) := VectorGroup.charValue χ T (g ≫ q.hom.hom)

theorem chi_mul (g h : T ⟶ E.X) : chi q χ (g * h) = chi q χ g * chi q χ h := by
  rw [chi, MonObj.mul_comp, VectorGroup.charValue_mul]

@[simp] theorem chi_one : chi q χ (1 : T ⟶ E.X) = 1 := by
  rw [chi, MonObj.one_comp, VectorGroup.charValue_one]

theorem chi_mul_inv (g : T ⟶ E.X) : chi q χ g * chi q χ g⁻¹ = 1 := by
  rw [← chi_mul, mul_inv_cancel, chi_one]

theorem chi_comp (b : T' ⟶ T) (g : T ⟶ E.X) : chi q χ (b ≫ g) = b.left.appTop.hom (chi q χ g) := by
  rw [chi, chi, Category.assoc, VectorGroup.charValue_comp]

theorem kernel_comp_q (u : T ⟶ (kernel q).X) : (u ≫ (kernelι q).hom.hom) ≫ q.hom.hom = 1 := by
  rw [Category.assoc, (kernel_isPullback q).w, ← Category.assoc, comp_toUnit]
  rfl

@[simp] theorem chi_kernel (u : T ⟶ (kernel q).X) : chi q χ (u ≫ (kernelι q).hom.hom) = 1 := by
  rw [chi, kernel_comp_q, VectorGroup.charValue_one]

theorem mul_kernel_comp_q (g : T ⟶ E.X) (u : T ⟶ (kernel q).X) :
    (g * (u ≫ (kernelι q).hom.hom)) ≫ q.hom.hom = g ≫ q.hom.hom := by
  rw [MonObj.mul_comp, kernel_comp_q, mul_one]

theorem chi_mul_kernel (g : T ⟶ E.X) (u : T ⟶ (kernel q).X) :
    chi q χ (g * (u ≫ (kernelι q).hom.hom)) = chi q χ g := by
  rw [chi, mul_kernel_comp_q]

/-- The kernel point `g⁻¹ g'` of two points of `E` with the same image. -/
def kpt (g g' : T ⟶ E.X) (h : g ≫ q.hom.hom = g' ≫ q.hom.hom) : T ⟶ (kernel q).X :=
  (kernelPointsEquiv q T).symm ⟨g⁻¹ * g', by
    change (g⁻¹ * g') ≫ q.hom.hom = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, h, inv_mul_cancel]⟩

theorem kpt_comp (g g' : T ⟶ E.X) (h : g ≫ q.hom.hom = g' ≫ q.hom.hom) :
    kpt q g g' h ≫ (kernelι q).hom.hom = g⁻¹ * g' := by
  rw [kpt, ← kernelPointsEquiv_val, MulEquiv.apply_symm_apply]

theorem eq_kpt {g g' : T ⟶ E.X} (h : g ≫ q.hom.hom = g' ≫ q.hom.hom) {u : T ⟶ (kernel q).X}
    (hu : u ≫ (kernelι q).hom.hom = g⁻¹ * g') : u = kpt q g g' h :=
  (cancel_mono (kernelι q).hom.hom).mp (by rw [hu, kpt_comp])

/-- The cocycle value `χ(g) · a(g⁻¹ g')` of two points with the same image. -/
def pairValue (g g' : T ⟶ E.X) (h : g ≫ q.hom.hom = g' ≫ q.hom.hom) : Γ(T.left, ⊤) :=
  chi q χ g * cd (kpt q g g' h ≫ a.hom.hom)

theorem pairValue_congr {g₁ g₂ g₁' g₂' : T ⟶ E.X} (hg : g₁ = g₂) (hg' : g₁' = g₂')
    (h₁ : g₁ ≫ q.hom.hom = g₁' ≫ q.hom.hom) (h₂ : g₂ ≫ q.hom.hom = g₂' ≫ q.hom.hom) :
    pairValue q a χ g₁ g₁' h₁ = pairValue q a χ g₂ g₂' h₂ := by
  subst hg hg'
  rfl

theorem pairValue_comp (b : T' ⟶ T) (g g' : T ⟶ E.X) (h : g ≫ q.hom.hom = g' ≫ q.hom.hom)
    (h' : (b ≫ g) ≫ q.hom.hom = (b ≫ g') ≫ q.hom.hom) :
    pairValue q a χ (b ≫ g) (b ≫ g') h' = b.left.appTop.hom (pairValue q a χ g g' h) := by
  have hk : kpt q (b ≫ g) (b ≫ g') h' = b ≫ kpt q g g' h := by
    symm
    apply eq_kpt
    rw [Category.assoc, kpt_comp, MonObj.comp_mul, GrpObj.comp_inv]
  rw [pairValue, pairValue, hk, Category.assoc, cd_comp, chi_comp, map_mul]

theorem pairValue_trans (g g' g'' : T ⟶ E.X) (h₁ : g ≫ q.hom.hom = g' ≫ q.hom.hom)
    (h₂ : g' ≫ q.hom.hom = g'' ≫ q.hom.hom) (h₃ : g ≫ q.hom.hom = g'' ≫ q.hom.hom) :
    pairValue q a χ g g'' h₃ = pairValue q a χ g g' h₁ + pairValue q a χ g' g'' h₂ := by
  have hk : kpt q g g'' h₃ = kpt q g g' h₁ * kpt q g' g'' h₂ := by
    symm
    apply eq_kpt
    rw [MonObj.mul_comp, kpt_comp, kpt_comp]
    group
  have hc : chi q χ g' = chi q χ g := by rw [chi, chi, h₁]
  rw [pairValue, pairValue, pairValue, hk, MonObj.mul_comp, cd_mul, hc, mul_add]

end Points

/-! ### The cocycle on the cover `q` -/

section Cocycle

open Langlands.AlgebraicGeometry.AffineAdditiveCocycle

/-- The cover `q`, as a scheme over the underlying scheme of `D`. -/
abbrev cover : Over (𝔻).X.left := Over.mk q.hom.hom.left

/-- A scheme over `D`, viewed over `Spec k`. -/
abbrev lowerObj (Z : Over (𝔻).X.left) : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Z.hom ≫ (𝔻).X.hom)

/-- A point of the cover, viewed as a point of `E` over `Spec k`. -/
def lowerPt {Z : Over (𝔻).X.left} (x : Z ⟶ cover q) : lowerObj Z ⟶ E.X :=
  Over.homMk x.left (by
    have hx := Over.w x
    have hq := Over.w q.hom.hom
    simp only [Over.mk_hom] at hx hq ⊢
    rw [← hq, ← Category.assoc, hx])

theorem lowerPt_left {Z : Over (𝔻).X.left} (x : Z ⟶ cover q) : (lowerPt q x).left = x.left :=
  rfl

theorem lowerPt_comp_q {Z : Over (𝔻).X.left} (x y : Z ⟶ cover q) :
    lowerPt q x ≫ q.hom.hom = lowerPt q y ≫ q.hom.hom := by
  apply Over.OverMorphism.ext
  have hx := Over.w x
  have hy := Over.w y
  simp only [Over.mk_hom] at hx hy
  change x.left ≫ q.hom.hom.left = y.left ≫ q.hom.hom.left
  rw [hx, hy]

/-- The morphism of lowered schemes induced by a morphism over `D`. -/
def lowerHom {Z Z' : Over (𝔻).X.left} (t : Z' ⟶ Z) : lowerObj Z' ⟶ lowerObj Z :=
  Over.homMk t.left (by
    simp only [Over.mk_hom]
    rw [← Category.assoc, Over.w t])

/-- The additive cocycle `(x, y) ↦ χ(x) · a(x⁻¹ y)` on the cover `q`. -/
def cocycle : AddCocycle (cover q) where
  toFun x y := pairValue q a χ (lowerPt q x) (lowerPt q y) (lowerPt_comp_q q x y)
  naturality t x y := by
    have hx : lowerPt q (t ≫ x) = lowerHom t ≫ lowerPt q x := Over.OverMorphism.ext rfl
    have hy : lowerPt q (t ≫ y) = lowerHom t ≫ lowerPt q y := Over.OverMorphism.ext rfl
    rw [pairValue_congr q a χ hx hy _ (by rw [← hx, ← hy]; exact lowerPt_comp_q q _ _),
      pairValue_comp]
    rfl
  cocycle x y z := pairValue_trans q a χ _ _ _ _ _ _

/-- There is a function `f` on `E` with `f(g · u) = f(g) + χ(g) a(u)` for every kernel point
`u`, on every test scheme. -/
theorem exists_equivariant [IsAffineHom E.X.hom] (hflat : Flat q.hom.hom.left)
    (hsurj : Surjective q.hom.hom.left) :
    ∃ fE : E.X ⟶ (𝔾ₐ).X, ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X)
      (u : T ⟶ (kernel q).X),
      cd ((g * (u ≫ (kernelι q).hom.hom)) ≫ fE) =
        cd (g ≫ fE) + chi q χ g * cd (u ≫ a.hom.hom) := by
  have : IsAffine (𝔻).X.left := isAffine_of_isAffineHom (𝔻).X.hom
  have : IsAffine (cover q).left := isAffine_of_isAffineHom E.X.hom
  have : Flat (cover q).hom := hflat
  have : Surjective (cover q).hom := hsurj
  obtain ⟨β, hβ⟩ := (cocycle q a χ).exists_coboundary
  refine ⟨ofCoord ClosedAdditivePolynomial.ga (-β), fun T g u => ?_⟩
  set g' := g * (u ≫ (kernelι q).hom.hom)
  have hq : g' ≫ q.hom.hom = g ≫ q.hom.hom := mul_kernel_comp_q q g u
  let Z : Over (𝔻).X.left := Over.mk (g.left ≫ q.hom.hom.left)
  let x₀ : Z ⟶ cover q := Over.homMk g.left rfl
  let y₀ : Z ⟶ cover q := Over.homMk g'.left (by
    change g'.left ≫ q.hom.hom.left = g.left ≫ q.hom.hom.left
    rw [← Over.comp_left, hq, Over.comp_left])
  let e : lowerObj Z ⟶ T := Over.homMk (𝟙 _) (by
    simp only [Over.mk_hom, Category.id_comp, Z]
    rw [Category.assoc, Over.w q.hom.hom, Over.w g])
  have hx : lowerPt q x₀ = e ≫ g := Over.OverMorphism.ext (by simp [lowerPt, e, x₀])
  have hy : lowerPt q y₀ = e ≫ g' := Over.OverMorphism.ext (by simp [lowerPt, e, y₀])
  have hval := hβ x₀ y₀
  change pairValue q a χ (lowerPt q x₀) (lowerPt q y₀) (lowerPt_comp_q q x₀ y₀) = _ at hval
  rw [pairValue_congr q a χ hx hy _ (by rw [Category.assoc, Category.assoc, hq]),
    pairValue_comp q a χ e g g' hq.symm] at hval
  have he : e.left.appTop.hom = RingHom.id _ := by
    simp [e]
    rfl
  have hk : kpt q g g' hq.symm = u := by
    symm
    apply eq_kpt
    rw [inv_mul_cancel_left]
  rw [he, RingHom.id_apply, pairValue, hk] at hval
  rw [cd_comp, cd_comp, cd_ofCoord, map_neg, map_neg]
  change -(g'.left.appTop.hom β) = -(g.left.appTop.hom β) + chi q χ g * cd (u ≫ a.hom.hom)
  change _ = g.left.appTop.hom β - g'.left.appTop.hom β at hval
  rw [hval]
  ring

end Cocycle

end Langlands.GroupScheme.LinearAdditiveExtension
