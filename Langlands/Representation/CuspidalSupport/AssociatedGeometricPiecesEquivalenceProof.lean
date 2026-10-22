import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups

/-! Full-refinement identities and the conjugating geometric piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Langlands.CuspidalSupport
open GeneralLinear Geometric CategoryTheory
universe uF uV uW

section Geometry
variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)

theorem sourceLevi_eq_top_of_conjugates (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) : sourceLevi F B C w = ⊤ := by
  apply top_unique
  intro m _
  change conjugatedLeviMap F B w m ∈ C.leviSubgroup F
  rw [← hw]
  exact ⟨B.leviEmbedding F m, ⟨m, rfl⟩, rfl⟩

theorem targetLevi_eq_top_of_conjugates (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F) B C w) : sourceLevi F C B w⁻¹ = ⊤ := by
  apply top_unique
  intro m _
  let x := (leviConjugation B C w hw).symm m
  change conjugatedLeviMap F C w⁻¹ m ∈ B.leviSubgroup F
  refine ⟨x, ?_⟩
  change B.leviEmbedding F x =
    permutation n F w⁻¹ * C.leviEmbedding F m * (permutation n F w⁻¹)⁻¹
  rw [map_inv, inv_inv]
  exact leviConjugation_symm_embedding B C w hw m

theorem refinedParabolic_eq_top_of_refinedLevi_eq_top (S : BlockRefinement B)
    (h : refinedLevi F B S = ⊤) : refinedParabolic F B S = ⊤ := by
  apply top_unique
  intro m _
  exact (refinedLeviSection F B S ⟨m, h ▸ Subgroup.mem_top _⟩).property

theorem refinedLeviProjection_val_of_full (S : BlockRefinement B)
    (h : refinedLevi F B S = ⊤) (q : refinedParabolic F B S) :
    (refinedLeviProjection F B S q).val = q.val := by
  let m : refinedLevi F B S := ⟨q.val, h ▸ Subgroup.mem_top _⟩
  have he : refinedLeviSection F B S m = q := Subtype.ext rfl
  rw [← he, refinedLeviProjection_section]
  rfl

theorem refinedUnipotent_eq_bot_of_full (S : BlockRefinement B)
    (h : refinedLevi F B S = ⊤) : refinedUnipotent F B S = ⊥ := by
  apply bot_unique
  intro g hg
  let q : refinedParabolic F B S := ⟨g, refinedUnipotent_le_parabolic F B S hg⟩
  have hp : refinedLeviProjection F B S q = 1 :=
    (mem_refinedUnipotentRadical F B S q).mpr hg
  have he := congrArg Subtype.val hp
  rw [refinedLeviProjection_val_of_full B S h] at he
  exact he

theorem innerParabolic_eq_top_of_full (S : BlockRefinement B)
    (h : refinedLevi F B S = ⊤) (i : Fin B.length) : (S i).parabolic F = ⊤ := by
  classical
  have hp := refinedParabolic_eq_top_of_refinedLevi_eq_top B S h
  apply top_unique
  intro x _
  have hm : Function.update (1 : B.Levi F) i x ∈ refinedParabolic F B S :=
    hp ▸ Subgroup.mem_top _
  simpa using (mem_refinedParabolic F B S _).mp hm i

end Geometry

section Normalization
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
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

/-- The inverse to evaluation is the orbit function, pulled back by the given
coefficient equivalence. Its uniform stabilizer is that of the original vector. -/
def fullInductionInverse (e : σ.Equiv (τ.comp P.subtype)) (hτ : IsSmooth τ) (v : W) :
    Induction.SmoothFunctions P σ :=
  Induction.smoothFunctionOf P σ (fun x => e.symm (τ x v)) (by
    intro q x
    rw [map_mul, Module.End.mul_apply]
    exact LinearMap.congr_fun (e.symm.isIntertwining' q) (τ x v))
    (hτ v).choose (by
      intro k x
      have hk : τ k.val v = v := (hτ v).choose_spec k
      rw [map_mul, Module.End.mul_apply, hk])

/-- For a full subgroup, evaluation and the orbit function are inverse
intertwiners for the actual smooth induction space. -/
def fullInductionEquiv (hP : P = ⊤) (e : σ.Equiv (τ.comp P.subtype))
    (hτ : IsSmooth τ) : (Induction.smoothInduced P σ).Equiv τ := by
  let f : Induction.SmoothFunctions P σ →ₗ[ℂ] W :=
    { toFun := fun φ => e (Induction.eval P σ φ 1)
      map_add' := fun φ ψ => e.map_add _ _
      map_smul' := fun a φ => e.map_smul a _ }
  let E : Induction.SmoothFunctions P σ ≃ₗ[ℂ] W :=
    { f with
      invFun := fullInductionInverse P σ τ e hτ
      left_inv := by
        intro φ
        apply Subtype.ext
        apply Subtype.ext
        funext x
        change e.symm (τ x (e (Induction.eval P σ φ 1))) = Induction.eval P σ φ x
        let q : P := ⟨x, hP ▸ Subgroup.mem_top _⟩
        have hc := φ.val.property q 1
        have he := LinearMap.congr_fun (e.isIntertwining' q) (Induction.eval P σ φ 1)
        change Induction.eval P σ φ (x * 1) = σ q (Induction.eval P σ φ 1) at hc
        change e (σ q (Induction.eval P σ φ 1)) = τ x (e (Induction.eval P σ φ 1)) at he
        apply e.injective
        change e (e.symm (τ x (e (Induction.eval P σ φ 1)))) = e (Induction.eval P σ φ x)
        rw [Representation.Equiv.apply_symm_apply]
        simpa only [mul_one] using he.symm.trans (congrArg e hc.symm)
      right_inv := by
        intro v
        change e (e.symm (τ 1 v)) = v
        simp }
  refine Representation.Equiv.mk E ?_
  intro g
  apply LinearMap.ext
  intro φ
  change e (Induction.eval P σ φ (1 * g)) = τ g (e (Induction.eval P σ φ 1))
  let q : P := ⟨g, hP ▸ Subgroup.mem_top _⟩
  have hc := φ.val.property q 1
  have he := LinearMap.congr_fun (e.isIntertwining' q) (Induction.eval P σ φ 1)
  change Induction.eval P σ φ (g * 1) = σ q (Induction.eval P σ φ 1) at hc
  change e (σ q (Induction.eval P σ φ 1)) = τ g (e (Induction.eval P σ φ 1)) at he
  simpa only [mul_one, one_mul] using (congrArg e hc).trans he

end FullInduction

section Relabel
variable {G : Type uF} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Equality relabeling preserves an actual equivalence with a restricted
ambient representation. -/
def subgroupEqualityEquiv (H K : Subgroup G) (h : H = K)
    (A : SmoothRep.{0, uF, uW} ℂ H) (τ : Representation ℂ G V)
    (e : A.representation.Equiv (τ.comp H.subtype)) :
    ((subgroupEqualityFunctor H K h).obj A).representation.Equiv (τ.comp K.subtype) := by
  subst K
  exact e
end Relabel

section TransportComparison
variable {F : Type uF} [Field F] {n : ℕ} (B C : BlockShape n)
  (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F) B C w)
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem intersectionLeviConjugation_symm_val (m : sourceLevi F C B w⁻¹) :
    ((intersectionLeviConjugation F B C w).symm m).val =
      (leviConjugation B C w hw).symm m.val := by
  apply B.leviEmbedding_injective F
  rw [intersectionLeviConjugation_symm_embedding, leviConjugation_symm_embedding]

def intersectionTransportFullEquiv
    (σ : Representation ℂ (sourceLevi F B C w) W)
    (ρ : Representation ℂ (B.Levi F) V)
    (e : σ.Equiv (ρ.comp (sourceLevi F B C w).subtype)) :
    (intersectionTransport F B C w σ).Equiv
      ((transport B C w hw ρ).comp (sourceLevi F C B w⁻¹).subtype) := by
  refine Representation.Equiv.mk e.toLinearEquiv ?_
  intro m
  apply LinearMap.ext
  intro v
  have he := LinearMap.congr_fun
    (e.isIntertwining' ((intersectionLeviConjugation F B C w).symm m)) v
  change e (σ ((intersectionLeviConjugation F B C w).symm m) v) =
    ρ ((leviConjugation B C w hw).symm m.val) (e v)
  change e (σ ((intersectionLeviConjugation F B C w).symm m) v) =
    ρ ((intersectionLeviConjugation F B C w).symm m).val (e v) at he
  rw [intersectionLeviConjugation_symm_val B C w hw] at he
  exact he
end TransportComparison
section Assembly
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
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
theorem associatedGeometricPieceEquivalence {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
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

/-- Check the complete unapplied telescope, including both independent universes. -/
example : ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ),
    AssociatedGeometricPieceEquivalenceTheorem.{uF, uV} F T n :=
  @associatedGeometricPieceEquivalence.{uF, uV}

end Langlands.CuspidalSupport
