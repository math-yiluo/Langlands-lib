import Langlands.Geometry.FormalGroup.CentralScalarKernel
import Langlands.Geometry.FormalGroup.PolarizedPrimalHeightTransfer
import Langlands.Geometry.FormalGroup.SplitSpecialPrimalAtlas

/-! # Scalar p-height on the actual split primal atlas -/

noncomputable section

universe u s v

namespace Langlands.FormalGroup.Nilp

open CategoryTheory

variable {W : Type v} [CommRing W] {π : W}

/-- Principal localization of an actual nilpotent coefficient test. -/
def localizationAway (T : Nilp.{v, v} W π) (a : T.obj) : Nilp.{v, v} W π :=
  Nilp.of W π (Localization.Away a) (by
    rw [IsScalarTower.algebraMap_apply W T.obj (Localization.Away a)]
    exact T.property.map (algebraMap T.obj (Localization.Away a)))

/-- The actual Nilp morphism from a test algebra to its principal localization. -/
def toLocalizationAway (T : Nilp.{v, v} W π) (a : T.obj) : T ⟶ T.localizationAway a :=
  ⟨CommAlgCat.ofHom (IsScalarTower.toAlgHom W T.obj (Localization.Away a))⟩

end Langlands.FormalGroup.Nilp

namespace Langlands.FormalGroup.Harris

open ValuativeRel ModuleLaw LocalDivision

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
attribute [local instance] primalDivisionPadicAlgebra

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Algebra ℤ_[prime] 𝒪[K]]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable {ϖ : 𝒪[K]} {frame : SplitPolarizedFrame prime K D W ϖ}
variable {T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}
variable {X : PolarizedFramedAffinePoint prime (algebraMap 𝒪[K] W ϖ) frame T}
variable {σ : Type} [Finite σ]
variable {M : ModuleLaw ℤ_[prime] (ResidueRing W (algebraMap 𝒪[K] W ϖ)) σ}

set_option backward.isDefEq.respectTransparency false in
private theorem primalTarget_hasPiHeight_onLocalization
    (a : T.obj) [algLocal : Algebra ℤ_[prime] (Localization.Away a)]
    (φ : T.obj →ₐ[ℤ_[prime]] Localization.Away a)
    (hφ : φ.toRingHom = algebraMap T.obj (Localization.Away a))
    {τ : Type} [Finite τ] {N : ModuleLaw ℤ_[prime] (Localization.Away a) τ}
    (A : frame.order.DivisionImage M) (B : (X.target.order.map φ).DivisionImage N)
    {H : ℕ} (hM : M.HasPiHeight (prime : ℤ_[prime]) prime H) :
    N.HasPiHeight (prime : ℤ_[prime]) prime H := by
  let j := T.toLocalizationAway a
  have hAlgebra : algLocal = coefficientAlgebra (O := ℤ_[prime]) (T.localizationAway a).obj := by
    apply Algebra.algebra_ext
    intro r
    exact (φ.commutes r).symm.trans ((RingHom.congr_fun hφ _).trans
      ((Nilp.scalarMap ℤ_[prime] j).commutes r))
  subst algLocal
  let : Algebra ℤ_[prime] (Localization.Away a) := coefficientAlgebra (T.localizationAway a).obj
  have hφ' : φ = Nilp.scalarMap ℤ_[prime] j := AlgHom.ext (RingHom.congr_fun hφ)
  subst φ
  exact (X.baseChange j).primalTarget_hasPiHeight A B hM

set_option backward.isDefEq.respectTransparency false in
/-- The scalar p-height of every special primal chart is the scalar p-height of the fixed primal frame. -/
theorem HasSplitSpecialTangent.primalSpecialAtlas_hasPiHeight_p (h : HasSplitSpecialTangent ι X)
    (A : frame.order.DivisionImage M) {H : ℕ} (hM : M.HasPiHeight (prime : ℤ_[prime]) prime H)
    (b : h.primalSpecialAtlas.atlas.opens) :
    (h.primalSpecialAtlas.atlas.chart b).HasPiHeight (prime : 𝒪[K]) prime H := by
  let E := X.target.order
  let C := primalImageCover E h.2.2
  let φ := IsScalarTower.toAlgHom ℤ_[prime] T.obj (Localization.Away b.val)
  let B : (E.map φ).DivisionImage (C.image b).1 := (C.image b).2
  have hPadic := primalTarget_hasPiHeight_onLocalization b.val φ rfl A B hM
  have hs' : (E.map φ).HasStructuralDivisionTangent (algebraMap 𝒪[K] (IntegerRing K D))
      (algebraMap 𝒪[K] (Localization.Away b.val)) := by
    rw [IsScalarTower.algebraMap_eq 𝒪[K] T.obj (Localization.Away b.val)]
    exact h.2.1.map φ
  let hstr := OrderAction.DivisionImage.structuralCentralTangent (E := E.map φ) B hs'
  exact (OrderAction.DivisionImage.order (E := E.map φ) B).centralModule_hasPiHeight_natCast hstr hPadic

end Langlands.FormalGroup.Harris
