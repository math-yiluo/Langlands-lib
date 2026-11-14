import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem associatedGeometricPieceEquivalence fullRefinedInductionEquiv fullRefinedJacquetEquiv refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full
open Langlands.GeneralLinear
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
open CategoryTheory
universe uF uV uW

section Geometry
variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)

end Geometry
section Normalization
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

theorem refinedModulus_eq_one_of_full (h : refinedLevi F.Carrier B S = ⊤)
    (m : refinedLevi F.Carrier B S) : T.refinedLeviModulus B S m = 1 := by
  rw [T.refinedLeviModulus_apply]
  apply Finset.prod_eq_one
  intro i _
  let := block_indices_subsingleton_of_parabolic_eq_top (S i)
    (innerParabolic_eq_top_of_full B S h i)
  rw [T.leviModulus_apply]
  apply Finset.prod_eq_one
  intro j _
  have hj : Finset.univ.filter (fun k : Fin (S i).length => j < k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k hk
    have he : j = k := Subsingleton.elim _ _
    simp [he] at hk
  rw [hj, Finset.prod_empty]

theorem refinedHalfModulus_eq_one_of_full (h : refinedLevi F.Carrier B S = ⊤)
    (m : refinedLevi F.Carrier B S) : (T.refinedLeviHalfModulus B S m : ℂ) = 1 := by
  simp [T.refinedLeviHalfModulus_apply, refinedModulus_eq_one_of_full T B S h m]

theorem refinedInverseHalfModulus_eq_one_of_full (h : refinedLevi F.Carrier B S = ⊤)
    (m : refinedLevi F.Carrier B S) : (T.refinedLeviInverseHalfModulus B S m : ℂ) = 1 := by
  simp [T.refinedLeviInverseHalfModulus_apply, refinedModulus_eq_one_of_full T B S h m]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

def fullRefinedJacquetEquiv (h : refinedLevi F.Carrier B S = ⊤)
    (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    (T.normalizedRefinedJacquet B S ρ).Equiv (ρ.comp (refinedLevi F.Carrier B S).subtype) := by
  let N := refinedUnipotent F.Carrier B S
  have hN : N = ⊥ := refinedUnipotent_eq_bot_of_full B S h
  let f : RefinedJacquetModule B S ρ →ₗ[ℂ] V := Jacquet.lift ρ N LinearMap.id (by
    intro u
    have hu : (u : B.Levi F.Carrier) = 1 := by
      simpa only [hN, Subgroup.mem_bot] using u.property
    ext v
    simp [hu])
  let e : RefinedJacquetModule B S ρ ≃ₗ[ℂ] V :=
    { f with
      invFun := refinedJacquetMk B S ρ
      left_inv := by
        intro x
        obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
        rfl
      right_inv := fun v => rfl }
  refine Representation.Equiv.mk e ?_
  intro m
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N x
  change f (T.normalizedRefinedJacquet B S ρ m (refinedJacquetMk B S ρ v)) = _
  rw [T.normalizedRefinedJacquet_mk, refinedInverseHalfModulus_eq_one_of_full T B S h,
    one_smul]
  rfl

end Normalization
section FullInduction
variable {G : Type uF} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (P : Subgroup G) {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ P V) (τ : Representation ℂ G W)

end FullInduction
section Relabel
variable {G : Type uF} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Relabel
section TransportComparison
variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w)
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

end TransportComparison
section Assembly
variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- Full normalized refined induction is evaluated at one, with its
normalizing factor and projection reduced by proved full-refinement identities. -/
def fullRefinedInductionEquiv (h : refinedLevi F.Carrier B S = ⊤)
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V)
    (τ : Representation ℂ (B.Levi F.Carrier) W)
    (e : σ.Equiv (τ.comp (refinedLevi F.Carrier B S).subtype)) :
    letI := T.topology
    IsSmooth τ → (T.normalizedRefinedInduced B S σ).Equiv τ := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro hτ
  let χ := T.refinedLeviHalfModulus B S
  let P := refinedParabolic F.Carrier B S
  let σP := refinedInducingRepresentation B S χ σ
  let eP : σP.Equiv (τ.comp P.subtype) := Representation.Equiv.mk e.toLinearEquiv (by
    intro q
    apply LinearMap.ext
    intro v
    change e ((T.refinedLeviHalfModulus B S (refinedLeviProjection F.Carrier B S q) : ℂ) •
      σ (refinedLeviProjection F.Carrier B S q) v) = τ q.val (e v)
    rw [refinedHalfModulus_eq_one_of_full T B S h, one_smul]
    have he := LinearMap.congr_fun (e.isIntertwining'
      (refinedLeviProjection F.Carrier B S q)) v
    change e (σ (refinedLeviProjection F.Carrier B S q) v) =
      τ (refinedLeviProjection F.Carrier B S q).val (e v) at he
    rw [refinedLeviProjection_val_of_full B S h] at he
    exact he)
  exact fullInductionEquiv P σP τ
    (refinedParabolic_eq_top_of_refinedLevi_eq_top B S h) eP hτ
end Assembly
set_option maxHeartbeats 1200000 in
/-- A conjugating geometric piece is the actual whole-Levi transport.
The extra quasicuspidality, association and minimality hypotheses of the
published component are retained, although this identity does not need them. -/
theorem associatedGeometricPieceEquivalence (F : LocalFieldPackage.{uF}) (T : F.TopologicalData) (n : ℕ) :
    AssociatedGeometricPieceEquivalenceTheorem.{uF, uV} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro B C ρ _ _ w S R hS hR hw
  have hfullS : refinedLevi F.Carrier B S = ⊤ :=
    hS.2.1.symm.trans (sourceLevi_eq_top_of_conjugates B C w.val hw)
  have hfullR : refinedLevi F.Carrier C R = ⊤ :=
    hR.2.1.symm.trans (targetLevi_eq_top_of_conjugates B C w.val hw)
  let J := (T.normalizedRefinedJacquetFunctor B S).obj ρ
  let eJ : J.representation.Equiv
      (ρ.representation.comp (refinedLevi F.Carrier B S).subtype) :=
    fullRefinedJacquetEquiv T B S hfullS ρ.representation
  let J' := (subgroupEqualityFunctor _ _ hS.2.1.symm).obj J
  let eJ' : J'.representation.Equiv
      (ρ.representation.comp (sourceLevi F.Carrier B C w.val).subtype) :=
    subgroupEqualityEquiv _ _ hS.2.1.symm J ρ.representation eJ
  let τ := transport B C w.val hw ρ.representation
  let Q := (intersectionTransportFunctor F.Carrier B C w.val).obj J'
  let eQ : Q.representation.Equiv
      (τ.comp (sourceLevi F.Carrier C B w.val⁻¹).subtype) :=
    intersectionTransportFullEquiv B C w.val hw J'.representation ρ.representation eJ'
  let Q' := (subgroupEqualityFunctor _ _ hR.2.1).obj Q
  let eQ' : Q'.representation.Equiv
      (τ.comp (refinedLevi F.Carrier C R).subtype) :=
    subgroupEqualityEquiv _ _ hR.2.1 Q τ eQ
  have hτ : IsSmooth τ := isSmooth_transport B C w.val hw ρ.isSmooth
  change Nonempty ((T.normalizedRefinedInduced C R Q'.representation).Equiv τ)
  exact ⟨fullRefinedInductionEquiv T C R hfullR Q'.representation τ eQ' hτ⟩

end Langlands.AllFieldBZ.CuspidalSupport
