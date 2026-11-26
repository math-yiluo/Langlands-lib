import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback
import Langlands.AbelianScheme.RationalBaseChange
import Langlands.AbelianScheme.Tate.PrimitiveHom

/-! # Base change of primitive dual-valued homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme.Tate

open Langlands.GroupScheme.Tate (Index)

section Primitive

variable {S : Scheme.{u}} {A B C : AbelianScheme S}

private theorem isPrimitiveHom_iff_no_divisor (f : A ⟶ B) :
    IsPrimitiveHom f ↔ ∀ k : ℕ, 1 < k → ¬ ∃ g : A ⟶ B, k • g = f := by
  constructor
  · rintro hf k hk ⟨g, hg⟩
    exact (Nat.ne_of_gt hk) (hf k g hg)
  · intro hf k g hg
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact (hf 2 (by decide) ⟨0, by simpa only [zero_smul, smul_zero] using hg⟩).elim
    · by_contra h
      exact hf k (by omega) ⟨g, hg⟩

/-- Postcomposition by an actual isomorphism preserves and reflects primitivity. -/
theorem isPrimitiveHom_post_iso_iff (f : A ⟶ B) (e : B ≅ C) :
    IsPrimitiveHom (f ≫ e.hom) ↔ IsPrimitiveHom f := by
  constructor
  · intro hf k g hg
    apply hf k (g ≫ e.hom)
    rw [← Preadditive.nsmul_comp, hg]
  · intro hf k g hg
    apply hf k (g ≫ e.inv)
    rw [← Preadditive.nsmul_comp, hg, Category.assoc, e.hom_inv_id, Category.comp_id]

end Primitive

variable {S T : Scheme.{u}} [IsLocallyNoetherian S] [ConnectedSpace S]
  [IsLocallyNoetherian T] [ConnectedSpace T]
  (b : T ⟶ S) (htor : TorsionFiniteEtaleStatement.{u})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  {K : Type u} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T)
  {A B : AbelianScheme S}

include htor huS huT t in
/-- Divisibility by a positive integer is preserved and reflected by pullback
between these connected bases, using the same geometric point above each. -/
theorem exists_nsmul_eq_baseChange_iff (f : A ⟶ B) {k : ℕ} (hk : 0 < k) :
    (∃ g : (baseChange b).obj A ⟶ (baseChange b).obj B,
      k • g = (baseChange b).map f) ↔ (∃ g : A ⟶ B, k • g = f) := by
  rw [exists_nsmul_eq_iff_levelMap_eq_zero htor huT t _ hk,
    exists_nsmul_eq_iff_levelMap_eq_zero htor huS (t ≫ b) _ hk]
  let eA := GroupScheme.Tate.levelBaseChange b A.toGrp (Over.mk t) k
  let eB := GroupScheme.Tate.levelBaseChange b B.toGrp (Over.mk t) k
  have commute (x : GroupScheme.Tate.Level ((baseChange b).obj A).toGrp (Over.mk t) k) :
      eB (GroupScheme.Tate.levelMap (Over.mk t) (groupHom ((baseChange b).map f)) k x) =
        GroupScheme.Tate.levelMap (Over.mk (t ≫ b)) (groupHom f) k (eA x) :=
    GroupScheme.Tate.levelBaseChange_map b (Over.mk t) (groupHom f) k x
  constructor
  · intro hf x
    obtain ⟨x', rfl⟩ := eA.surjective x
    exact (commute x').symm.trans ((congrArg eB (hf x')).trans eB.map_zero)
  · intro hf x
    apply eB.injective
    exact (commute x).trans ((hf (eA x)).trans eB.map_zero.symm)

include htor huS huT t in
/-- An actual homomorphism is primitive exactly when its indicated base
change is primitive. -/
theorem isPrimitiveHom_baseChange_iff (f : A ⟶ B) :
    IsPrimitiveHom ((baseChange b).map f) ↔ IsPrimitiveHom f := by
  rw [isPrimitiveHom_iff_no_divisor, isPrimitiveHom_iff_no_divisor]
  exact forall_congr' fun k => forall_congr' fun hk =>
    not_congr (exists_nsmul_eq_baseChange_iff b htor huS huT t f (by omega))

end Langlands.AbelianScheme.Tate

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.GroupScheme.Tate (Index)

variable (P : Prerequisites.{u}) {S T : Scheme.{u}} [IsLocallyNoetherian S] [ConnectedSpace S]
  [IsLocallyNoetherian T] [ConnectedSpace T]
  (b : T ⟶ S) (htor : TorsionFiniteEtaleStatement.{u})
  (huS : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
  (huT : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(T, ⊤)))
  {K : Type u} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ T)
  {A : AbelianScheme S} (W : DualWitness A) (V : DualWitness ((baseChange b).obj A))

include htor huS huT t in
/-- The canonical comparison with the chosen changed dual keeps exactly the
primitive homomorphisms. -/
theorem DualWitness.isPrimitiveHom_pullbackMap_iff (f : A ⟶ W.dual P) :
    Tate.IsPrimitiveHom (W.pullbackMap P b V f) ↔ Tate.IsPrimitiveHom f :=
  (Tate.isPrimitiveHom_post_iso_iff _ (W.baseChangeIso P b V)).trans
    (Tate.isPrimitiveHom_baseChange_iff b htor huS huT t f)

include htor huS huT t in
/-- Pull back an actual primitive representative of a polarization ray along
the given map of bases, with any chosen changed dual presentation. -/
def DualWitness.pullbackPrimitiveRepresentative (lam : A ⟶ W.dual P)
    (mu : {f : A ⟶ W.dual P // Tate.IsPrimitiveHom f ∧
      ∃ k : ℕ, 0 < k ∧ k • f = lam}) :
    {f : (baseChange b).obj A ⟶ V.dual P // Tate.IsPrimitiveHom f ∧
      ∃ k : ℕ, 0 < k ∧ k • f = W.pullbackMap P b V lam} := by
  refine ⟨W.pullbackMap P b V mu.val,
    (W.isPrimitiveHom_pullbackMap_iff P b htor huS huT t V mu.val).mpr mu.property.1,
    ?_⟩
  obtain ⟨k, hk, he⟩ := mu.property.2
  refine ⟨k, hk, ?_⟩
  have h := congrArg (W.pullbackMap P b V) he
  unfold DualWitness.pullbackMap at h ⊢
  rwa [Functor.map_nsmul, Preadditive.nsmul_comp] at h

end Langlands.AbelianScheme.PolarizedFiniteLevel
