import Langlands.AlgebraicGeometry.FiniteEtale.Pullback

/-! # Pushforward of actual finite étale paths -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S'} {t : Spec (.of Ω') ⟶ S'} {r : Spec (.of Ω'') ⟶ S'}
  {hs : ∀ Y : Cover S', Finite (Fiber s Y)}
  {ht : ∀ Y : Cover S', Finite (Fiber t Y)}
  {hr : ∀ Y : Cover S', Finite (Fiber r Y)}
  (hsb : ∀ Y : Cover S, Finite (Fiber (s ≫ b) Y))
  (htb : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))

/-- Push forward a path by evaluating it on actual pulled-back covers and conjugating
by the canonical geometric-fibre comparisons. -/
def pathPushforward (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    fiberFunctor (s ≫ b) hsb ≅ fiberFunctor (t ≫ b) htb :=
  fiberFunctorPullbackIso b s (s ≫ b) rfl hsb hs ≪≫
    Functor.isoWhiskerLeft (pullbackFunctor b) p ≪≫
      (fiberFunctorPullbackIso b t (t ≫ b) rfl htb ht).symm

/-- Evaluate the pushed path by pulling a lift back, applying the original path,
and projecting to the original cover. -/
theorem pathPushforward_apply (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (Y : Cover S) (x : Fiber (s ≫ b) Y) :
    (pathPushforward b hsb htb p).hom.app Y x =
      (pullbackFiberEquiv b t (t ≫ b) rfl Y).symm
        (p.hom.app ((pullbackFunctor b).obj Y)
          (pullbackFiberEquiv b s (s ≫ b) rfl Y x)) := rfl

theorem pathPushforward_apply_left (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (Y : Cover S) (x : Fiber (s ≫ b) Y) :
    ((pathPushforward b hsb htb p).hom.app Y x).left =
      (p.hom.app ((pullbackFunctor b).obj Y)
        (pullbackFiberEquiv b s (s ≫ b) rfl Y x)).left ≫
          pullback.fst Y.obj.hom b := rfl

/-- The canonical pullback fibre bijections intertwine a path and its pushforward. -/
theorem pullbackFiberEquiv_pathPushforward
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (Y : Cover S) (x : Fiber (s ≫ b) Y) :
    pullbackFiberEquiv b t (t ≫ b) rfl Y
        ((pathPushforward b hsb htb p).hom.app Y x) =
      p.hom.app ((pullbackFunctor b).obj Y)
        (pullbackFiberEquiv b s (s ≫ b) rfl Y x) := by
  rw [pathPushforward_apply, Equiv.apply_symm_apply]

/-- Pushforward respects the constant path. -/
@[simp]
theorem pathPushforward_refl :
    pathPushforward b hsb hsb (Iso.refl (fiberFunctor s hs)) =
      Iso.refl (fiberFunctor (s ≫ b) hsb) := by
  simp [pathPushforward]

/-- Pushforward respects successive paths, in their categorical order. -/
theorem pathPushforward_trans (hrb : ∀ Y : Cover S, Finite (Fiber (r ≫ b) Y))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (q : fiberFunctor t ht ≅ fiberFunctor r hr) :
    pathPushforward b hsb hrb (p ≪≫ q) =
      pathPushforward b hsb htb p ≪≫ pathPushforward b htb hrb q := by
  simp [pathPushforward, Functor.isoWhiskerLeft_trans, Iso.trans_assoc]

/-- Pushforward respects reversal of paths. -/
@[simp]
theorem pathPushforward_symm (p : fiberFunctor s hs ≅ fiberFunctor t ht) :
    pathPushforward b htb hsb p.symm = (pathPushforward b hsb htb p).symm := by
  simp [pathPushforward, Functor.isoWhiskerLeft_symm, Iso.trans_assoc]

/-- On loops the path pushforward is exactly the existing induced fundamental-group map. -/
theorem pathPushforward_aut (g : FundamentalGroup s hs) :
    pathPushforward b hsb hsb g =
      fundamentalGroupMap b s (s ≫ b) rfl hs hsb g :=
  (fundamentalGroupMap_apply b s (s ≫ b) rfl hs hsb g).symm

/-- If a morphism over `b` carries a lift to `x`, it also carries its path transport
to the pushforward path transport of `x`. -/
theorem pathPushforward_apply_left_of_comp
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) {Y : Cover S}
    (x : Fiber (s ≫ b) Y) {Y' : Cover S'} (y : Fiber s Y')
    (φ : Y'.obj.left ⟶ Y.obj.left)
    (hφ : φ ≫ Y.obj.hom = Y'.obj.hom ≫ b) (hy : y.left ≫ φ = x.left) :
    ((pathPushforward b hsb htb p).hom.app Y x).left = (p.hom.app Y' y).left ≫ φ := by
  let ψ : Y' ⟶ (pullbackFunctor b).obj Y :=
    ObjectProperty.homMk
      (Over.homMk (pullback.lift φ Y'.obj.hom hφ) (pullback.lift_snd _ _ _))
  have hx : pullbackFiberEquiv b s (s ≫ b) rfl Y x = y ≫ ψ.hom := by
    apply Over.OverMorphism.ext
    apply pullbackFiberEquiv_apply_left_eq
    · simp [ψ, hy]
    · simp [ψ]
  have hnat : p.hom.app ((pullbackFunctor b).obj Y) (y ≫ ψ.hom) =
      p.hom.app Y' y ≫ ψ.hom :=
    ConcreteCategory.congr_hom (p.hom.naturality ψ) y
  rw [pathPushforward_apply_left, hx, hnat]
  simp [ψ]

/-- Fundamental-group pushforward commutes with change of point by a path and its pushforward. -/
theorem fundamentalGroupMap_path_conjugation
    (p : fiberFunctor s hs ≅ fiberFunctor t ht) (g : FundamentalGroup s hs) :
    fundamentalGroupMap b t (t ≫ b) rfl ht htb (Aut.autMulEquivOfIso p g) =
      Aut.autMulEquivOfIso (pathPushforward b hsb htb p)
        (fundamentalGroupMap b s (s ≫ b) rfl hs hsb g) := by
  simp only [fundamentalGroupMap_apply]
  apply Iso.ext
  simp [pathPushforward, Aut.autMulEquivOfIso, Category.assoc]

end Langlands.AlgebraicGeometry.FiniteEtale
