import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
import Langlands.AllFieldBZ.Representation.Derivative.RankCastCompat
import Langlands.AllFieldBZ.Representation.Derivative.ZeroRankTensor
import Langlands.Representation.Derivative.LeibnizRankZeroBoundary

/-!
# All-field port of `Langlands.Representation.Derivative.LeibnizRankZeroBoundary`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.LeibnizRankZeroBoundary` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeLeibnizFiltrationStatement HasNonzeroDerivative IsHomogeneous binaryNormalizedProductLeftZeroSwapIso binaryNormalizedProductSwapZeroIso binaryRightZeroDerivativeIso generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCastDerivativeIso generalLinearRankCastRestrictionIso generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestrictionDerivativeIso generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap hasNonzeroDerivative_iff isHomogeneous_of_subsingleton isoRankCastOfEquiv le_level_of_hasNonzeroDerivative leibnizPiece leibnizPiece_obj leibnizSource leibnizSourceLeftZeroIso leibnizSourceLeftZeroPieceIso leibnizSourceRightZeroIso leibnizSourceRightZeroPieceIso level level_eq_iff level_eq_zero_iff level_eq_zero_of_subsingleton level_le mirabolicDerivative mirabolicDerivativeOfOrder mirabolicDerivativeOfOrder_eq mirabolicDerivativeOfOrder_obj mirabolicDerivativeOfOrder_obj_subsingleton mirabolicDerivativeOfOrder_one mirabolicDerivativeOfOrder_top mirabolicDerivative_eq mirabolicDerivative_obj_subsingleton mirabolicDerivative_succ mirabolicDerivative_zero mirabolicRankCast mirabolicRankCastDerivativeIso mirabolicRankCast_obj_subsingleton mirabolicRankCast_refl phiMinusIterate phiMinusIterate_obj_subsingleton phiMinusIterate_succ phiMinusIterate_zero
universe uF uV uC vC

open Langlands.GeneralLinear
open Langlands.BinaryTensor
/-! ### Index sets with a rank-zero factor -/

/-! ### Rank transport from carrier equivalences -/

variable {F : LocalFieldPackage.{uF}}

/-- A natural family of equivariant carrier equivalences from `P` to `Q` composed with the
entry-preserving reindex identifies `P` with `Q` followed by rank transport. -/
def isoRankCastOfEquiv (T : F.TopologicalData) {C : Type uC} [Category.{vC} C]
    {m n : ℕ} (h : m = n)
    (P : letI := T.topology; C ⥤ SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
    (Q : letI := T.topology; C ⥤ SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
    (e : letI := T.topology; ∀ X, (P.obj X).representation.Equiv
      ((Q.obj X).representation.comp (reindex (R := F.Carrier) (finCongr h.symm)).toMonoidHom))
    (he : letI := T.topology; ∀ {X Y : C} (f : X ⟶ Y) (v : P.obj X),
      e Y (SmoothRep.hom (P.map f) v) = SmoothRep.hom (Q.map f) (e X v)) :
    letI := T.topology
    P ≅ Q ⋙ generalLinearRankCast T h := by
  letI := T.topology
  subst h
  refine NatIso.ofComponents (fun X => SmoothRep.mkIso
    (Representation.Equiv.mk (e X).toLinearEquiv fun g => ?_)) fun {X Y} f => ?_
  · ext v
    have h1 := LinearMap.congr_fun ((e X).isIntertwining' g) v
    change (e X) ((P.obj X).representation g v) =
      (Q.obj X).representation g ((e X) v)
    rw [← Langlands.RankinSelberg.reindex_finCongr_self (R := F.Carrier) (rfl : m = m).symm g]
    exact h1
  · ext v
    exact he f v

/-! ### Swapping a rank-zero factor -/

variable (T : F.TopologicalData)

/-- Swapping the factors of the binary product with rank-zero second factor gives the
binary product with rank-zero first factor, after rank transport. -/
def binaryNormalizedProductSwapZeroIso (n : ℕ) :
    letI := T.topology
    CategoryTheory.Prod.swap _ _ ⋙ T.binaryNormalizedProductFunctor.{uF, uV} n 0 ≅
      T.binaryNormalizedProductFunctor 0 n ⋙ generalLinearRankCast T (Nat.zero_add n) := by
  letI := T.topology
  refine isoRankCastOfEquiv T (Nat.zero_add n) _ _
    (fun X => ((T.binaryRightZeroTensorEquiv rfl (X.2, X.1)).trans
      (rankZeroRightSwapEquiv X.2.representation)).trans
      (compEquiv (T.binaryLeftZeroTensorEquiv rfl X).symm _)) ?_
  intro X Y f v
  have key : ∀ u, (T.binaryLeftZeroTensorEquiv rfl Y).symm
      (TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap u) =
      SmoothRep.hom ((T.binaryNormalizedProductFunctor 0 n).map f)
        ((T.binaryLeftZeroTensorEquiv rfl X).symm u) := by
    intro u
    apply EquivLike.injective (T.binaryLeftZeroTensorEquiv rfl Y)
    rw [Representation.Equiv.apply_symm_apply, T.binaryLeftZeroTensorEquiv_naturality,
      Representation.Equiv.apply_symm_apply]
  change (T.binaryLeftZeroTensorEquiv rfl Y).symm (TensorProduct.comm ℂ _ _
      (T.binaryRightZeroTensorEquiv rfl (Y.2, Y.1)
        (SmoothRep.hom ((T.binaryNormalizedProductFunctor n 0).map
          ((CategoryTheory.Prod.swap _ _).map f)) v))) = _
  rw [T.binaryRightZeroTensorEquiv_naturality]
  change (T.binaryLeftZeroTensorEquiv rfl Y).symm (TensorProduct.comm ℂ _ _
      (TensorProduct.map (SmoothRep.hom f.2).toLinearMap (SmoothRep.hom f.1).toLinearMap _)) = _
  rw [← TensorProduct.map_comm, key]
  rfl

/-- The binary product with rank-zero first factor, written through the binary product with
rank-zero second factor. -/
def binaryNormalizedProductLeftZeroSwapIso (n : ℕ) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} 0 n ≅
      CategoryTheory.Prod.swap _ _ ⋙ T.binaryNormalizedProductFunctor n 0 ⋙
        generalLinearRankCast T (Nat.zero_add n).symm := by
  letI := T.topology
  refine eqToIso ?_ ≪≫
    Functor.isoWhiskerRight (binaryNormalizedProductSwapZeroIso T n).symm _
  rw [Functor.assoc, generalLinearRankCast_symm_comp]
  exact (Functor.comp_id _).symm

/-! ### The two rank-zero boundaries from the right-zero commutation -/

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- With rank-zero second factor, a natural commutation of the order-`d` derivative with the
binary product identifies the Leibniz source with its unique piece. -/
def leibnizSourceRightZeroIso {a d : ℕ} (hd : d ≤ a + 0)
    (E : letI := T.topology
      T.binaryNormalizedProductFunctor.{uF, uV} a 0 ⋙ generalLinearDerivative T ψ (a + 0) d hd ≅
        (generalLinearDerivative T ψ a d hd).prod (𝟭 _) ⋙
          T.binaryNormalizedProductFunctor (a - d) 0)
    (x : LeibnizIndex a 0 d) :
    leibnizSource.{uF, uV} T ψ a 0 d hd ≅ leibnizPiece T ψ a 0 d x := by
  letI := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨rfl, rfl⟩ : d = i ∧ j = 0 := by
    simp only [mem_leibnizIndices] at hx
    omega
  exact Functor.isoWhiskerRight E SmoothRep.toRep

/-- With rank-zero first factor, the same commutation at the second factor identifies the
Leibniz source with its unique piece, by swapping the two factors. -/
def leibnizSourceLeftZeroIso {b d : ℕ} (hd : d ≤ 0 + b) (hb : d ≤ b)
    (E : letI := T.topology
      T.binaryNormalizedProductFunctor.{uF, uV} b 0 ⋙ generalLinearDerivative T ψ (b + 0) d hb ≅
        (generalLinearDerivative T ψ b d hb).prod (𝟭 _) ⋙
          T.binaryNormalizedProductFunctor (b - d) 0)
    (x : LeibnizIndex 0 b d) :
    leibnizSource.{uF, uV} T ψ 0 b d hd ≅ leibnizPiece T ψ 0 b d x := by
  letI := T.topology
  obtain ⟨⟨i, j⟩, hx⟩ := x
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ d = j := by
    simp only [mem_leibnizIndices] at hx
    omega
  have h₀ : 0 + b = b := Nat.zero_add b
  -- move the rank-zero factor to the right
  refine Functor.isoWhiskerRight (binaryNormalizedProductLeftZeroSwapIso T b) _ ≪≫ ?_
  -- commute the rank transport with the derivative
  refine Functor.isoWhiskerLeft (CategoryTheory.Prod.swap _ _ ⋙
      T.binaryNormalizedProductFunctor b 0)
    (Functor.isoWhiskerRight
      (generalLinearRankCastDerivativeIso T ψ h₀.symm d hb hd) SmoothRep.toRep) ≪≫ ?_
  -- apply the right-zero commutation
  refine Functor.isoWhiskerLeft (CategoryTheory.Prod.swap _ _)
    (Functor.isoWhiskerRight E
      (generalLinearRankCast T (congrArg (fun r => r - d) h₀.symm) ⋙ SmoothRep.toRep)) ≪≫ ?_
  -- swap back
  refine Functor.isoWhiskerLeft ((𝟭 _).prod (generalLinearDerivative T ψ b d hb))
    (Functor.isoWhiskerRight (binaryNormalizedProductSwapZeroIso T (b - d))
      (generalLinearRankCast T (congrArg (fun r => r - d) h₀.symm) ⋙ SmoothRep.toRep)) ≪≫ ?_
  -- combine the rank transports
  refine eqToIso ?_
  change (𝟭 _).prod (generalLinearDerivative T ψ b d hb) ⋙
      T.binaryNormalizedProductFunctor 0 (b - d) ⋙
        (generalLinearRankCast T (Nat.zero_add (b - d)) ⋙
          generalLinearRankCast T (congrArg (fun r => r - d) h₀.symm)) ⋙ SmoothRep.toRep = _
  rw [generalLinearRankCast_trans]
  rfl

/-! ### The right-zero commutation -/

/-- The order-`d` derivative commutes with the binary product whose second factor has rank
zero: both sides are the derivative of the first factor tensored with the inert factor. -/
def binaryRightZeroDerivativeIso (n d : ℕ) (hd : d ≤ n + 0) :
    letI := T.topology
    T.binaryNormalizedProductFunctor.{uF, uV} n 0 ⋙ generalLinearDerivative T ψ (n + 0) d hd ≅
      (generalLinearDerivative T ψ n d hd).prod (𝟭 _) ⋙
        T.binaryNormalizedProductFunctor (n - d) 0 := by
  letI := T.topology
  exact Functor.isoWhiskerRight (ZeroRankTensor.binaryRightZeroIso T n) _ ≪≫
    Functor.isoWhiskerLeft ((𝟭 _).prod MixedProductTensor.liftFunctor.{uF, uV, uF})
      (ZeroRankTensor.generalLinearDerivativeTensorIso.{uF, uF, uV, max uV uF}
        (GeneralLinear 0 F.Carrier) T ψ n d hd) ≪≫
    Functor.isoWhiskerLeft ((generalLinearDerivative T ψ n d hd).prod (𝟭 _))
      (ZeroRankTensor.binaryRightZeroIso T (n - d)).symm

/-- The Leibniz source with rank-zero second factor is naturally its unique piece. -/
def leibnizSourceRightZeroPieceIso {a d : ℕ} (hd : d ≤ a + 0) (x : LeibnizIndex a 0 d) :
    leibnizSource.{uF, uV} T ψ a 0 d hd ≅ leibnizPiece T ψ a 0 d x :=
  leibnizSourceRightZeroIso T ψ hd (binaryRightZeroDerivativeIso T ψ a d hd) x

/-- The Leibniz source with rank-zero first factor is naturally its unique piece. -/
def leibnizSourceLeftZeroPieceIso {b d : ℕ} (hd : d ≤ 0 + b) (x : LeibnizIndex 0 b d) :
    leibnizSource.{uF, uV} T ψ 0 b d hd ≅ leibnizPiece T ψ 0 b d x :=
  have hb : d ≤ b := by omega
  leibnizSourceLeftZeroIso T ψ hd hb (binaryRightZeroDerivativeIso T ψ b d hb) x

end Langlands.AllFieldBZ.Derivative
