import Langlands.GroupScheme.Reductive.WeilFactorUniquenessReduction
import Langlands.GroupScheme.Reductive.RelativeAlmostSimpleNormalIdempotentStatement
import Langlands.GroupScheme.Reductive.WeilAbelianImageTrivialityStatement

/-! # Rigidity of normal idempotent endomorphisms of a Weil restriction, from two inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.IdempotentPoints

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (K : GroupScheme (Spec (CommRingCat.of R)))
  [IsAffine K.X.left] {C : Type u} [CommRing C] [Algebra R C]

theorem fst_proj_one_sub {e : C} (he : IsIdempotentElem e)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    fst K e (proj K (1 - e) g) = 1 :=
  snd_proj K he.one_sub g

theorem snd_proj_one_sub {e : C} (he : IsIdempotentElem e)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    snd K e (proj K (1 - e) g) = snd K e g := by
  apply ev_injective K
  intro a
  rw [ev_snd, ev_snd, ev_proj K he.one_sub]
  simp only [map_add, map_mul, map_sub, map_one, mk_snd_self]
  ring

theorem proj_mul_proj_one_sub {e : C} (he : IsIdempotentElem e)
    (g : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    proj K e g * proj K (1 - e) g = g :=
  ext_of_idempotent K he
    (by rw [map_mul, fst_proj K he, fst_proj_one_sub K he, mul_one])
    (by rw [map_mul, snd_proj K he, snd_proj_one_sub K he, one_mul])

theorem commute_proj_proj_one_sub {e : C} (he : IsIdempotentElem e)
    (g h : K.affinePoints (CommAlgCat.of (CommRingCat.of R) C)) :
    Commute (proj K e g) (proj K (1 - e) h) := by
  show proj K e g * proj K (1 - e) h = proj K (1 - e) h * proj K e g
  exact ext_of_idempotent K he
    (by rw [map_mul, map_mul, fst_proj K he, fst_proj_one_sub K he, mul_one, one_mul])
    (by rw [map_mul, map_mul, snd_proj K he, snd_proj_one_sub K he, mul_one, one_mul])

end Langlands.GroupScheme.IdempotentPoints

namespace Langlands.GroupScheme.WeilFactor

open IdempotentPoints Langlands.Algebra.GraphIdempotent

section Commutation

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [Module.Projective A B] {G : GroupScheme (Spec (CommRingCat.of B))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] {T : CommAlgCat.{u} (CommRingCat.of A)}

theorem factorProjection_congr {e f : B ⊗[A] T} (h : e = f) (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f) : factorProjection A B G e he = factorProjection A B G f hf := by
  subst h
  rfl

omit [Module.Finite A B] [Module.Projective A B] in
theorem baseIdem_one_sub (X : Under T) (e : B ⊗[A] T) :
    baseIdem X (1 - e) = 1 - baseIdem X e := by
  rw [baseIdem, baseIdem, map_sub, map_one]

theorem pointsEquiv_pt_factorProjection_one_sub {e : B ⊗[A] T} (he : IsIdempotentElem e)
    (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    AffineWeil.pointsEquiv A B G X.right (pt (factorProjection A B G (1 - e) he.one_sub) X x) =
      proj G (1 - baseIdem X e) (AffineWeil.pointsEquiv A B G X.right x) := by
  rw [pointsEquiv_pt_factorProjection he.one_sub, baseIdem_one_sub]

/-- A point is the product of its `e`-component and its `(1 - e)`-component. -/
theorem pt_factorProjection_mul_one_sub {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (factorProjection A B G e he) X x * pt (factorProjection A B G (1 - e) he.one_sub) X x =
      x := by
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [map_mul (AffineWeil.pointsEquiv A B G X.right), pointsEquiv_pt_factorProjection he,
    pointsEquiv_pt_factorProjection_one_sub he,
    proj_mul_proj_one_sub G (baseIdem_isIdempotentElem he X)]

/-- The `e`-component of a point commutes with the `(1 - e)`-component of any point. -/
theorem commute_pt_factorProjection {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T)
    (x y : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)) :
    Commute (pt (factorProjection A B G e he) X x)
      (pt (factorProjection A B G (1 - e) he.one_sub) X y) := by
  show _ * _ = _ * _
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [map_mul (AffineWeil.pointsEquiv A B G X.right),
    map_mul (AffineWeil.pointsEquiv A B G X.right), pointsEquiv_pt_factorProjection he,
    pointsEquiv_pt_factorProjection_one_sub he]
  exact commute_proj_proj_one_sub G (baseIdem_isIdempotentElem he X) _ _

theorem pt_factorProjection_idem {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (factorProjection A B G e he) X (pt (factorProjection A B G e he) X x) =
      pt (factorProjection A B G e he) X x := by
  rw [← pt_comp, factorProjection_idem]

variable [Algebra.Etale A B]

/-- With the abelian-image input, the `e`-component of `ψ` applied to the `(1 - e)`-component
of a point is trivial. -/
theorem pt_cross_eq_one (hW : WeilAbelianImageTrivialityStatement.{u}) (hred : IsReductive G)
    (hss : ∀ s, IsSemisimple (geometricFiber G s)) (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    {e : B ⊗[A] T} (he : IsIdempotentElem e) (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt (factorProjection A B G e he) X
      (pt ψ X (pt (factorProjection A B G (1 - e) he.one_sub) X x)) = 1 := by
  set c : Fun A B G T ⟶ Fun A B G T :=
    factorProjection A B G (1 - e) he.one_sub ≫ ψ ≫ factorProjection A B G e he with hc
  have hpt : ∀ (X : Under T) (x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt c X x = pt (factorProjection A B G e he) X
        (pt ψ X (pt (factorProjection A B G (1 - e) he.one_sub) X x)) := by
    intro X x
    rw [hc, pt_comp, pt_comp]
  have key : ∀ (X : Under T) (x h : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)),
      Commute (pt c X x) (pt (factorProjection A B G e he) X h) := by
    intro X x h
    rw [hpt]
    have hu := commute_pt_factorProjection he X h x
    have hn := hnorm X (pt (factorProjection A B G e he) X h)
      (pt (factorProjection A B G (1 - e) he.one_sub) X x)
    rw [hu.eq, mul_inv_cancel_right] at hn
    have hψ : Commute (pt ψ X (pt (factorProjection A B G (1 - e) he.one_sub) X x))
        (pt (factorProjection A B G e he) X h) :=
      (mul_inv_eq_iff_eq_mul.mp hn.symm).symm
    have h2 := hψ.map (pt (factorProjection A B G e he) X)
    rw [pt_factorProjection_idem] at h2
    exact h2
  have hcomm : ∀ (X : Under T) (x y : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), Commute (pt c X x) (pt c X y) :=
    fun X x y => by
      have hk := key X x (pt ψ X (pt (factorProjection A B G (1 - e) he.one_sub) X y))
      rw [← hpt] at hk
      exact hk
  have h0 : pt c X x = 1 :=
    hW A B G hred hss (AffineWeil.groupScheme A B G) T c (fun X x y => hcomm X x y) X x
  rw [hpt] at h0
  exact h0

/-- With the abelian-image input, every normal endomorphism commutes with every factor
projection. -/
theorem factorProjection_comm (hW : WeilAbelianImageTrivialityStatement.{u})
    (hred : IsReductive G) (hss : ∀ s, IsSemisimple (geometricFiber G s))
    (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    {e : B ⊗[A] T} (he : IsIdempotentElem e) :
    ψ ≫ factorProjection A B G e he = factorProjection A B G e he ≫ ψ := by
  refine ext_pt fun X x => ?_
  rw [pt_comp, pt_comp]
  have h1 := pt_cross_eq_one hW hred hss ψ hnorm he X x
  have h2 := pt_cross_eq_one hW hred hss ψ hnorm he.one_sub X
    (pt (factorProjection A B G e he) X x)
  have hfp : factorProjection A B G (1 - (1 - e)) he.one_sub.one_sub =
      factorProjection A B G e he := factorProjection_congr (sub_sub_cancel 1 e) _ he
  rw [hfp, pt_factorProjection_idem] at h2
  have hx := pt_factorProjection_mul_one_sub he X x
  have h3 := pt_factorProjection_mul_one_sub he X (pt ψ X (pt (factorProjection A B G e he) X x))
  rw [h2, mul_one] at h3
  calc pt (factorProjection A B G e he) X (pt ψ X x)
      = pt (factorProjection A B G e he) X (pt ψ X (pt (factorProjection A B G e he) X x *
          pt (factorProjection A B G (1 - e) he.one_sub) X x)) := by rw [hx]
    _ = pt ψ X (pt (factorProjection A B G e he) X x) := by
      rw [map_mul, map_mul, h1, mul_one, h3]

/-- Pointwise form of `factorProjection_comm` for an idempotent of `B ⊗_A X` over a `T`-algebra
`X`. -/
theorem proj_pt_comm (hW : WeilAbelianImageTrivialityStatement.{u})
    (hred : IsReductive G) (hss : ∀ s, IsSemisimple (geometricFiber G s))
    (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    (X : Under T) {f : B ⊗[A] X.right} (hf : IsIdempotentElem f)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    proj G f (AffineWeil.pointsEquiv A B G X.right (pt ψ X x)) =
      AffineWeil.pointsEquiv A B G X.right (pt ψ X ((AffineWeil.pointsEquiv A B G X.right).symm
        (proj G f (AffineWeil.pointsEquiv A B G X.right x)))) := by
  set ψ₁ : Fun A B G X.right ⟶ Fun A B G X.right := restrict X.hom ψ with hψ₁
  have hn₁ : ∀ (Y : Under X.right) (h y : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) Y.right)), pt ψ₁ Y (h * y * h⁻¹) = h * pt ψ₁ Y y * h⁻¹ :=
    fun Y h y => hnorm ((Under.map X.hom).obj Y) h y
  have hc := factorProjection_comm hW hred hss ψ₁ hn₁ hf
  set Y : Under X.right := Under.mk (𝟙 X.right) with hY
  have hψY : ∀ y, pt ψ₁ Y y = pt ψ X y := fun y => rfl
  have hfY : ∀ y, AffineWeil.pointsEquiv A B G X.right (pt (factorProjection A B G f hf) Y y) =
      proj G f (AffineWeil.pointsEquiv A B G X.right y) := by
    intro y
    refine (pointsEquiv_pt_factorProjection hf Y y).trans ?_
    have hb : baseIdem Y f = f := baseIdem_id f
    erw [hb]
    rfl
  have h1 : pt (ψ₁ ≫ factorProjection A B G f hf) Y x =
      pt (factorProjection A B G f hf ≫ ψ₁) Y x := by rw [hc]
  rw [pt_comp, pt_comp, hψY, hψY] at h1
  have h2 := congrArg (AffineWeil.pointsEquiv A B G X.right) h1
  rw [hfY] at h2
  rw [h2]
  congr 2
  apply (AffineWeil.pointsEquiv A B G X.right).injective
  rw [MulEquiv.apply_symm_apply, hfY]

end Commutation

section Theta

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

variable (B) in
/-- `B ⊗_A T` as a `B`-algebra. -/
abbrev tensorB (T : CommAlgCat.{u} (CommRingCat.of A)) : CommAlgCat.{u} (CommRingCat.of B) :=
  CommAlgCat.of (CommRingCat.of B) (B ⊗[A] T)

variable (B) in
/-- The inclusion `t ↦ 1 ⊗ t` of `T` into `B ⊗_A T`, for the `A`-algebra structure on `B ⊗_A T`
through `B`. -/
def inclAlg (T : CommAlgCat.{u} (CommRingCat.of A)) :
    @AlgHom A T (B ⊗[A] T) _ _ _ _ (Algebra.compHom (B ⊗[A] T) (algebraMap A B)) :=
  @AlgHom.mk A T (B ⊗[A] T) _ _ _ _ (Algebra.compHom (B ⊗[A] T) (algebraMap A B))
    (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T).toRingHom (fun a => by
      change (1 : B) ⊗ₜ[A] algebraMap A T a = algebraMap A B a ⊗ₜ[A] (1 : T)
      rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply])

set_option linter.internalConstructors false in
variable (B) in
/-- The inclusion `T ⟶ B ⊗_A T` of `A`-algebras, with `B ⊗_A T` regarded as an `A`-algebra
through `B`. -/
def incl (T : CommAlgCat.{u} (CommRingCat.of A)) : T ⟶ (resA A B).obj (tensorB B T) :=
  ⟨inclAlg B T⟩

theorem incl_apply (T : CommAlgCat.{u} (CommRingCat.of A)) (t : T) :
    (incl B T).hom t = (1 : B) ⊗ₜ[A] t := rfl

theorem mulMap_lT_tmul {Z : CommAlgCat.{u} (CommRingCat.of A)}
    {W : CommAlgCat.{u} (CommRingCat.of B)} (j : Z ⟶ (resA A B).obj W) (b : B) (t : Z) :
    mulMap A W (lT j (b ⊗ₜ[A] t)) = algebraMap B W b * (j.hom t : W) := by
  change graphMul (structureMap A W) (b ⊗ₜ[A] j.hom t) = algebraMap B W b * (j.hom t : W)
  rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply]
  rfl

/-- The multiplication `B ⊗_A (B ⊗_A Z) → B ⊗_A Z` undoes `1 ⊗ incl`. -/
theorem mulMap_lT_incl (Z : CommAlgCat.{u} (CommRingCat.of A)) (z : B ⊗[A] Z) :
    mulMap A (tensorB B Z) (lT (incl B Z) z) = z := by
  induction z with
  | tmul b t =>
    rw [mulMap_lT_tmul]
    change (b ⊗ₜ[A] (1 : Z)) * ((1 : B) ⊗ₜ[A] t) = b ⊗ₜ[A] t
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable (A) in
/-- A `B ⊗_A T`-algebra `Y` (a `B`-algebra with a map from `B ⊗_A T`), regarded as a
`T`-algebra. -/
abbrev liftU {T : CommAlgCat.{u} (CommRingCat.of A)} (Y : Under (tensorB B T)) : Under T where
  left := ⟨⟨⟩⟩
  right := (resA A B).obj Y.right
  hom := incl B T ≫ (resA A B).map Y.hom

variable (B) in
/-- `B ⊗_A X` as a `B ⊗_A T`-algebra, for a `T`-algebra `X`. -/
abbrev tensorU {T : CommAlgCat.{u} (CommRingCat.of A)} (X : Under T) : Under (tensorB B T) where
  left := ⟨⟨⟩⟩
  right := tensorB B X.right
  hom := (CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := B) B X.hom.hom) :
    tensorB B T ⟶ tensorB B X.right)

/-- The map `X → B ⊗_A X`, `x ↦ 1 ⊗ x`, as a map of `T`-algebras. -/
def kappa {T : CommAlgCat.{u} (CommRingCat.of A)} (X : Under T) :
    X ⟶ liftU A (tensorU B X) :=
  Under.homMk (incl B X.right) (by ext; rfl)

theorem kappa_right {T : CommAlgCat.{u} (CommRingCat.of A)} (X : Under T) :
    (kappa (B := B) X).right = incl B X.right := rfl

end Theta

section Points

open IdempotentPoints

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [Module.Projective A B] [Algebra.Etale A B] (G : GroupScheme (Spec (CommRingCat.of B)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

variable (A) in
/-- `embNat` on points. -/
def embPt (Y : CommAlgCat.{u} (CommRingCat.of B)) :
    G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y) →*
      (AffineWeil.groupScheme A B G).affinePoints
        (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y)) :=
  ((embNat A G).app Y).hom

variable (A) in
/-- `projNat` on points. -/
def prjPt (Y : CommAlgCat.{u} (CommRingCat.of B)) :
    (AffineWeil.groupScheme A B G).affinePoints
        (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y)) →*
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y) :=
  ((projNat A G).app Y).hom

variable {G}

omit [Algebra.Etale A B] in
theorem prjPt_apply (Y : CommAlgCat.{u} (CommRingCat.of B))
    (h : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y))) :
    prjPt A G Y h = G.affinePointMap (CommAlgCat.ofHom (mulMap A Y))
      (AffineWeil.pointsEquiv A B G ((resA A B).obj Y) h) := rfl

theorem prjPt_embPt (Y : CommAlgCat.{u} (CommRingCat.of B))
    (g : G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y)) :
    prjPt A G Y (embPt A G Y g) = g :=
  projNat_embNat_apply G Y g

theorem snd_embPt (Y : CommAlgCat.{u} (CommRingCat.of B))
    (y : G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y)) :
    snd G (graphIdem A Y) (AffineWeil.pointsEquiv A B G ((resA A B).obj Y) (embPt A G Y y)) = 1 := by
  change snd G (graphIdem A Y) (AffineWeil.pointsEquiv A B G ((resA A B).obj Y)
      ((AffineWeil.pointsEquiv A B G ((resA A B).obj Y)).symm ((factorEquivX A G Y).symm y).1)) = 1
  rw [MulEquiv.apply_symm_apply]
  exact ((factorEquivX A G Y).symm y).2

/-- The projection along the multiplication kills the complement of the graph idempotent. -/
theorem prjPt_symm_proj (Y : CommAlgCat.{u} (CommRingCat.of B))
    (h : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y))) :
    prjPt A G Y ((AffineWeil.pointsEquiv A B G ((resA A B).obj Y)).symm
      (proj G (graphIdem A Y) (AffineWeil.pointsEquiv A B G ((resA A B).obj Y) h))) =
        prjPt A G Y h := by
  have hg1 : mulMap A Y (graphIdem A Y) = 1 := by
    rw [mulMap_apply]
    exact (graphIdem_spec (A := A) Y).graphMul_eq_one
  rw [prjPt_apply, prjPt_apply, MulEquiv.apply_symm_apply,
    proj_map G (mulMap A Y) (graphIdem_spec (A := A) Y).isIdempotentElem hg1, proj_one]

omit [Module.Finite A B] [Module.Projective A B] in
theorem graphIdem_isIdempotentElem (Y : CommAlgCat.{u} (CommRingCat.of B)) :
    IsIdempotentElem (graphIdem A Y) :=
  (graphIdem_spec (A := A) Y).isIdempotentElem

theorem embPt_prjPt_of_snd (Y : CommAlgCat.{u} (CommRingCat.of B))
    (h : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y)))
    (hfix : snd G (graphIdem A Y) (AffineWeil.pointsEquiv A B G ((resA A B).obj Y) h) = 1) :
    embPt A G Y (prjPt A G Y h) = h :=
  embNat_projNat_of_snd G Y h hfix

/-- Embedding the projection of a point is the graph-idempotent component of the point. -/
theorem embPt_prjPt (Y : CommAlgCat.{u} (CommRingCat.of B))
    (h : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y))) :
    embPt A G Y (prjPt A G Y h) = (AffineWeil.pointsEquiv A B G ((resA A B).obj Y)).symm
      (proj G (graphIdem A Y) (AffineWeil.pointsEquiv A B G ((resA A B).obj Y) h)) := by
  rw [← prjPt_symm_proj Y h]
  refine embPt_prjPt_of_snd Y _ ?_
  rw [MulEquiv.apply_symm_apply]
  exact snd_proj G (graphIdem_spec (A := A) Y).isIdempotentElem _

omit [Algebra.Etale A B] in
/-- Points equivalence along a map into a `B`-algebra regarded as an `A`-algebra. -/
theorem pointsEquiv_affinePointMap_res {Z : CommAlgCat.{u} (CommRingCat.of A)}
    {W : CommAlgCat.{u} (CommRingCat.of B)} (j : Z ⟶ (resA A B).obj W)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) Z)) :
    AffineWeil.pointsEquiv A B G ((resA A B).obj W)
        ((AffineWeil.groupScheme A B G).affinePointMap j x) =
      G.affinePointMap (CommAlgCat.ofHom (lT j)) (AffineWeil.pointsEquiv A B G Z x) :=
  AffineWeil.pointsEquiv_naturality A B G j.hom x

omit [Algebra.Etale A B] in
/-- Projecting the image of a point along `x ↦ 1 ⊗ x` recovers the point of `G` over
`B ⊗_A Z`. -/
theorem prjPt_incl (Z : CommAlgCat.{u} (CommRingCat.of A))
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) Z)) :
    prjPt A G (tensorB B Z) ((AffineWeil.groupScheme A B G).affinePointMap (incl B Z) x) =
      AffineWeil.pointsEquiv A B G Z x := by
  rw [prjPt_apply, pointsEquiv_affinePointMap_res]
  apply ev_injective G
  intro a
  rw [ev_map, ev_map]
  exact mulMap_lT_incl Z _

end Points

section ThetaDef

open IdempotentPoints

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
  [Module.Projective A B] [Algebra.Etale A B] (G : GroupScheme (Spec (CommRingCat.of B)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] {T : CommAlgCat.{u} (CommRingCat.of A)}

/-- The endomorphism of the group functor of `G` on `B ⊗_A T`-algebras induced by an
endomorphism `ψ` of `R_{B/A}(G)` on `T`-algebras: embed `G(Y)` into `R_{B/A}(G)(Y) = G(B ⊗_A Y)`
as the factor of the graph idempotent, apply `ψ`, and project along the multiplication
`B ⊗_A Y → Y`. -/
def theta (ψ : Fun A B G T ⟶ Fun A B G T) :
    Under.forget (tensorB B T) ⋙ G.affinePointFunctor ⟶
      Under.forget (tensorB B T) ⋙ G.affinePointFunctor :=
  Functor.whiskerLeft (Under.forget (tensorB B T)) (embNat A G) ≫
    Functor.whiskerLeft (Under.post (resA A B)) (restrict (incl B T) ψ) ≫
    Functor.whiskerLeft (Under.forget (tensorB B T)) (projNat A G)

variable {G}

/-- `ψ` over the `T`-algebra underlying a `B ⊗_A T`-algebra `Y`, on points. -/
def ptL (ψ : Fun A B G T ⟶ Fun A B G T) (Y : Under (tensorB B T)) :
    (AffineWeil.groupScheme A B G).affinePoints
        (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y.right)) →*
      (AffineWeil.groupScheme A B G).affinePoints
        (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y.right)) :=
  pt ψ (liftU A Y)

/-- `theta` on points. -/
def thetaPt (ψ : Fun A B G T ⟶ Fun A B G T) (Y : Under (tensorB B T)) :
    G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y.right) →*
      G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y.right) :=
  ((theta G ψ).app Y).hom

set_option maxRecDepth 20000 in
theorem thetaPt_eq (ψ : Fun A B G T ⟶ Fun A B G T) (Y : Under (tensorB B T))
    (y : G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y.right)) :
    thetaPt ψ Y y = prjPt A G Y.right (ptL ψ Y (embPt A G Y.right y)) := rfl

omit [Algebra.Etale A B] in
theorem pt_idem {ψ : Fun A B G T ⟶ Fun A B G T} (hidem : ψ ≫ ψ = ψ) (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt ψ X (pt ψ X x) = pt ψ X x := by
  rw [← pt_comp, hidem]

omit [Algebra.Etale A B] in
theorem pt_naturality (ψ : Fun A B G T ⟶ Fun A B G T) {X Y : Under T} (a : X ⟶ Y)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    pt ψ Y ((AffineWeil.groupScheme A B G).affinePointMap a.right x) =
      (AffineWeil.groupScheme A B G).affinePointMap a.right (pt ψ X x) := by
  have h := ConcreteCategory.congr_hom (ψ.naturality a) x
  change pt ψ Y ((AffineWeil.groupScheme A B G).affinePointMap a.right x) =
    (AffineWeil.groupScheme A B G).affinePointMap a.right (pt ψ X x) at h
  exact h

omit [Algebra.Etale A B] in
theorem ptL_idem {ψ : Fun A B G T ⟶ Fun A B G T} (hidem : ψ ≫ ψ = ψ) (Y : Under (tensorB B T))
    (x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y.right))) :
    ptL ψ Y (ptL ψ Y x) = ptL ψ Y x :=
  pt_idem hidem (liftU A Y) x

omit [Algebra.Etale A B] in
theorem ptL_conj (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    (Y : Under (tensorB B T)) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y.right))) :
    ptL ψ Y (h * x * h⁻¹) = h * ptL ψ Y x * h⁻¹ :=
  hnorm (liftU A Y) h x

set_option maxRecDepth 20000 in
theorem proj_ptL_comm (hW : WeilAbelianImageTrivialityStatement.{u})
    (hred : IsReductive G) (hss : ∀ s, IsSemisimple (geometricFiber G s))
    (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    (Y : Under (tensorB B T)) {f : B ⊗[A] ((resA A B).obj Y.right)} (hf : IsIdempotentElem f)
    (x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y.right))) :
    proj G f (AffineWeil.pointsEquiv A B G ((resA A B).obj Y.right) (ptL ψ Y x)) =
      AffineWeil.pointsEquiv A B G ((resA A B).obj Y.right)
        (ptL ψ Y ((AffineWeil.pointsEquiv A B G ((resA A B).obj Y.right)).symm
          (proj G f (AffineWeil.pointsEquiv A B G ((resA A B).obj Y.right) x)))) :=
  proj_pt_comm hW hred hss ψ hnorm (liftU A Y) hf x

theorem thetaPt_normal (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    (Y : Under (tensorB B T)) (h y : G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y.right)) :
    thetaPt ψ Y (h * y * h⁻¹) = h * thetaPt ψ Y y * h⁻¹ := by
  have e1 : embPt A G Y.right (h * y * h⁻¹) =
      embPt A G Y.right h * embPt A G Y.right y * (embPt A G Y.right h)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  have e2 : ∀ a c : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) ((resA A B).obj Y.right)),
      prjPt A G Y.right (a * c * a⁻¹) = prjPt A G Y.right a * prjPt A G Y.right c *
        (prjPt A G Y.right a)⁻¹ := fun a c => by
    rw [map_mul, map_mul, map_inv]
  rw [thetaPt_eq, thetaPt_eq, e1, ptL_conj ψ hnorm, e2, prjPt_embPt]

/-- `ψ` preserves the factor of the graph idempotent on points coming from `G`. -/
theorem embPt_prjPt_ptL (hW : WeilAbelianImageTrivialityStatement.{u})
    (hred : IsReductive G) (hss : ∀ s, IsSemisimple (geometricFiber G s))
    (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    (Y : Under (tensorB B T)) (y : G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y.right)) :
    embPt A G Y.right (prjPt A G Y.right (ptL ψ Y (embPt A G Y.right y))) =
      ptL ψ Y (embPt A G Y.right y) := by
  refine embPt_prjPt_of_snd Y.right _ ?_
  have hg := (graphIdem_spec (A := A) Y.right).isIdempotentElem
  have hfix : proj G (graphIdem A Y.right) (AffineWeil.pointsEquiv A B G ((resA A B).obj Y.right)
      (embPt A G Y.right y)) = AffineWeil.pointsEquiv A B G ((resA A B).obj Y.right)
      (embPt A G Y.right y) :=
    ((eq_proj_iff G hg).mpr ⟨rfl, snd_embPt Y.right y⟩).symm
  have hc := proj_ptL_comm hW hred hss ψ hnorm Y hg (embPt A G Y.right y)
  rw [hfix, MulEquiv.symm_apply_apply] at hc
  rw [← hc]
  exact snd_proj G hg _

set_option maxRecDepth 20000 in
theorem theta_idem (hW : WeilAbelianImageTrivialityStatement.{u})
    (hred : IsReductive G) (hss : ∀ s, IsSemisimple (geometricFiber G s))
    (ψ : Fun A B G T ⟶ Fun A B G T) (hidem : ψ ≫ ψ = ψ)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹) :
    theta G ψ ≫ theta G ψ = theta G ψ := by
  refine NatTrans.ext (funext fun Y => GrpCat.ext ?_)
  intro (y : G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y.right))
  change thetaPt ψ Y (thetaPt ψ Y y) = thetaPt ψ Y y
  rw [thetaPt_eq, thetaPt_eq, embPt_prjPt_ptL hW hred hss ψ hnorm Y y, ptL_idem hidem]

set_option maxRecDepth 20000 in
/-- The comparison: `ψ` on points over a `T`-algebra `X` is `theta` on the points of `G` over
`B ⊗_A X`. -/
theorem pointsEquiv_pt_eq_thetaPt (hW : WeilAbelianImageTrivialityStatement.{u})
    (hred : IsReductive G) (hss : ∀ s, IsSemisimple (geometricFiber G s))
    (ψ : Fun A B G T ⟶ Fun A B G T)
    (hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹)
    (X : Under T)
    (x : (AffineWeil.groupScheme A B G).affinePoints (CommAlgCat.of (CommRingCat.of A) X.right)) :
    AffineWeil.pointsEquiv A B G X.right (pt ψ X x) =
      thetaPt ψ (tensorU B X) (AffineWeil.pointsEquiv A B G X.right x) := by
  set h := (AffineWeil.groupScheme A B G).affinePointMap (incl B X.right) x with hh
  have hg := graphIdem_isIdempotentElem (A := A) (tensorB B X.right)
  have h1 : AffineWeil.pointsEquiv A B G X.right x = prjPt A G (tensorB B X.right) h :=
    (prjPt_incl X.right x).symm
  have hc := proj_ptL_comm hW hred hss ψ hnorm (tensorU B X) hg h
  have hc' := (MulEquiv.symm_apply_eq _).mpr hc
  have hn : ptL ψ (tensorU B X) h =
      (AffineWeil.groupScheme A B G).affinePointMap (incl B X.right) (pt ψ X x) :=
    pt_naturality ψ (kappa X) x
  rw [thetaPt_eq]
  change _ = prjPt A G (tensorB B X.right) (ptL ψ (tensorU B X)
    (embPt A G (tensorB B X.right) (AffineWeil.pointsEquiv A B G X.right x)))
  rw [h1, embPt_prjPt, ← hc', prjPt_symm_proj, hn, prjPt_incl]

set_option maxRecDepth 20000 in
omit [Module.Finite A B] [Module.Projective A B] [Algebra.Etale A B] in
theorem mulMap_baseIdem_liftU (Y : Under (tensorB B T)) (f : B ⊗[A] T) :
    mulMap A Y.right (baseIdem (liftU A Y) f) = Y.hom.hom f := by
  change mulMap A Y.right (lT (incl B T ≫ (resA A B).map Y.hom) f) = Y.hom.hom f
  induction f with
  | tmul b t =>
    rw [mulMap_lT_tmul]
    change algebraMap B Y.right b * Y.hom.hom ((1 : B) ⊗ₜ[A] t) = Y.hom.hom (b ⊗ₜ[A] t)
    rw [← Y.hom.hom.commutes b, ← map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- `theta` of a factor projection is the corresponding projection of points. -/
theorem thetaPt_factorProjection {f : B ⊗[A] T} (hf : IsIdempotentElem f)
    (Y : Under (tensorB B T)) (y : G.affinePoints (CommAlgCat.of (CommRingCat.of B) Y.right)) :
    thetaPt (factorProjection A B G f hf) Y y = proj G (Y.hom.hom f) y := by
  rw [thetaPt_eq]
  change prjPt A G Y.right (pt (factorProjection A B G f hf) (liftU A Y)
    (embPt A G Y.right y)) = _
  rw [prjPt_apply, pointsEquiv_pt_factorProjection hf (liftU A Y),
    proj_map G (mulMap A Y.right) (baseIdem_isIdempotentElem hf (liftU A Y))
      (mulMap_baseIdem_liftU Y f), ← prjPt_apply, prjPt_embPt]

end ThetaDef

section Main

open IdempotentPoints

set_option maxRecDepth 20000 in
/-- **Rigidity of normal idempotent endomorphisms of a Weil restriction, from two inputs.**
The rigidity statement for `R_{B/A}(G')` follows from the rigidity statement for groups with
almost simple geometric fibres over an arbitrary base and the triviality of homomorphisms with
commutative image from `R_{B/A}(G')`. -/
theorem weilFactorIdempotentRigidity_of_inputs
    (h1 : RelativeAlmostSimpleNormalIdempotentStatement.{u})
    (h2 : WeilAbelianImageTrivialityStatement.{u}) :
    WeilFactorIdempotentRigidityStatement.{u} := by
  intro A B _ _ _ _ _ _ G _ _ hred hsimple T ψ hidem hnorm'
  have hss : ∀ s, IsSemisimple (geometricFiber G s) := fun s => (hsimple s).isSemisimple
  have hnorm : ∀ (X : Under T) (h x : (AffineWeil.groupScheme A B G).affinePoints
      (CommAlgCat.of (CommRingCat.of A) X.right)), pt ψ X (h * x * h⁻¹) = h * pt ψ X x * h⁻¹ :=
    fun X h x => hnorm' X h x
  obtain ⟨e, ⟨he, hspec⟩, huniq⟩ := h1 B G hred hsimple (tensorB B T) (theta G ψ)
    (theta_idem h2 hred hss ψ hidem hnorm) (fun Y h y => thetaPt_normal ψ hnorm Y h y)
  refine ⟨e, ⟨he, fun X x => ?_⟩, fun f hf' => huniq f ⟨hf'.1, fun Y y => ?_⟩⟩
  · show fst G (baseIdem X e) (AffineWeil.pointsEquiv A B G X.right (pt ψ X x)) =
        fst G (baseIdem X e) (AffineWeil.pointsEquiv A B G X.right x) ∧
      snd G (baseIdem X e) (AffineWeil.pointsEquiv A B G X.right (pt ψ X x)) = 1
    rw [pointsEquiv_pt_eq_thetaPt h2 hred hss ψ hnorm X x]
    exact hspec (tensorU B X) (AffineWeil.pointsEquiv A B G X.right x)
  · obtain ⟨hf, hfspec⟩ := hf'
    have hψf := eq_factorProjection hf ψ (fun X x => hfspec X x)
    show fst G (Y.hom.hom f) (thetaPt ψ Y y) = fst G (Y.hom.hom f) y ∧
      snd G (Y.hom.hom f) (thetaPt ψ Y y) = 1
    rw [hψf, thetaPt_factorProjection hf]
    exact ⟨fst_proj G (hf.map Y.hom.hom) y, snd_proj G (hf.map Y.hom.hom) y⟩

end Main

end Langlands.GroupScheme.WeilFactor
