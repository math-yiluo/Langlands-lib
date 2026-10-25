import Langlands.AbelianScheme.Tate.FixedFrameOrbitComparisons
import Langlands.AbelianScheme.Tate.PointedFrameOrbitPullback

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
universe u v w z
namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Shimura.PEL

private theorem inverse_square {X Y Z W T : Type*}
    (f : Y ≃ X) (g : Z ≃ Y) (d : T ≃ W) (t : W ≃ X) (c : T ≃ Z)
    (h : ∀ z, f (g z) = t (d (c.symm z))) (x : X) :
    c (d.symm (t.symm x)) = g.symm (f.symm x) := by
  apply c.symm.injective
  rw [Equiv.symm_apply_apply]
  apply d.injective
  rw [Equiv.apply_symm_apply]
  apply t.injective
  rw [Equiv.apply_symm_apply, ← h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

section Full
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω : Type u} [Field Ω] {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))
  (htor : TorsionFiniteEtaleStatement.{u})

/-- Transport fixed orbit classes along equality of their geometric points. -/
def adelicFrameOrbitPointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) (U : Subgroup G) :
    AdelicFrameOrbit A h i V s ρ hs htor hu U ≃
      AdelicFrameOrbit A h i V t ρ ht htor hu U := by
  subst t
  exact Equiv.refl _

/-- The equality transport is the actual test-isomorphism map whenever its
underlying map of point schemes is the identity. -/
theorem adelicFrameOrbitPointEq_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) (U : Subgroup G)
    (e : Over.mk s ≅ Over.mk t) (he : e.hom.left = 𝟙 _)
    (q : AdelicFrameOrbit A h i V s ρ hs htor hu U) :
    (adelicFrameOrbitPointEq A h i V ρ htor hst hs ht hu U q).1 =
      adelicFrameRightOrbitTestIso A h i V ρ U e q.1 := by
  subst t
  have heq : e = Iso.refl (Over.mk s) := by
    apply Iso.ext
    apply Over.OverMorphism.ext
    exact he
  subst e
  exact (adelicFrameRightOrbitTestIso_refl A h i V ρ U q.1).symm

/-- Inverse equality transport has the inverse actual test-isomorphism map. -/
theorem adelicFrameOrbitPointEq_symm_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤))) (U : Subgroup G)
    (e : Over.mk s ≅ Over.mk t) (he : e.hom.left = 𝟙 _)
    (q : AdelicFrameOrbit A h i V t ρ ht htor hu U) :
    ((adelicFrameOrbitPointEq A h i V ρ htor hst hs ht hu U).symm q).1 =
      (adelicFrameRightOrbitTestIso A h i V ρ U e).symm q.1 := by
  apply (adelicFrameRightOrbitTestIso A h i V ρ U e).injective
  rw [Equiv.apply_symm_apply]
  rw [← adelicFrameOrbitPointEq_val A h i V ρ htor hst hs ht hu U e he]
  rw [Equiv.apply_symm_apply]

/-- Pullback along the identity agrees with equality transport after the actual
identity abelian-scheme comparison. -/
theorem adelicFrameOrbitPullback_id (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (hs' : ∀ Y : Cover S, Finite (Fiber (s ≫ 𝟙 S) Y))
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (hbc : RationalMonodromyBaseChange.{u}) (U : Subgroup G)
    (q : AdelicFrameOrbit A h i V (s ≫ 𝟙 S) ρ hs' htor hu U) :
    adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U
        (adelicFrameOrbitPullback (𝟙 S) A h i V s ρ hs hs' htor hu hu hbc U q) =
      adelicFrameOrbitPointEq A h i V ρ htor (Category.comp_id s) hs' hs hu U q := by
  apply Subtype.ext
  rw [adelicFrameOrbitBaseChangeId_val, adelicFrameOrbitPullback_val,
    adelicFrameOrbitPointEq_val A h i V ρ htor (Category.comp_id s) hs' hs hu U
      ((Over.mapId S).app (Over.mk s)) rfl]
  have hh := adelicFrameRightOrbitBaseChange_id A h i V ρ U s
    ((adelicFrameRightOrbitBaseChange (𝟙 S) A h i V s ρ U).symm q.1)
  rw [Equiv.apply_symm_apply] at hh
  exact hh.symm

/-- Direct pullback, followed by the actual abelian-scheme comparison, agrees
with successive pointed pullback after the canonical associativity transport. -/
theorem adelicFrameOrbitPullback_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
    (hc : ∀ Y : Cover S', Finite (Fiber (s ≫ c) Y))
    (hb : ∀ Y : Cover S, Finite (Fiber ((s ≫ c) ≫ b) Y))
    (hbcpt : ∀ Y : Cover S, Finite (Fiber (s ≫ (c ≫ b)) Y))
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (hu' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))
    (hu'' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S'', ⊤)))
    (hbc : RationalMonodromyBaseChange.{u}) (U : Subgroup G)
    (q : AdelicFrameOrbit A h i V ((s ≫ c) ≫ b) ρ hb htor hu U) :
    adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu'' U
        (adelicFrameOrbitPullback (c ≫ b) A h i V s ρ hs hbcpt htor hu hu'' hbc U
          ((adelicFrameOrbitPointEq A h i V ρ htor (Category.assoc s c b).symm
            hbcpt hb hu U).symm q)) =
      adelicFrameOrbitPullback c ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ hs hc htor hu' hu'' hbc U
        (adelicFrameOrbitPullback b A h i V (s ≫ c) ρ hc hb htor hu hu' hbc U q) := by
  let := adelicFrameRightAction A h i V ((s ≫ c) ≫ b) ρ
  let := adelicFrameMonodromyAction A h i V ((s ≫ c) ≫ b) hb htor hu
  let := adelicFrameActionsComm A h i V ((s ≫ c) ≫ b) ρ hb htor hu
  apply Subtype.ext
  rw [adelicFrameOrbitBaseChangeComp_val, adelicFrameOrbitPullback_val,
    adelicFrameOrbitPointEq_symm_val A h i V ρ htor (Category.assoc s c b).symm
      hbcpt hb hu U ((Over.mapComp c b).app (Over.mk s)) rfl,
    adelicFrameOrbitPullback_val, adelicFrameOrbitPullback_val]
  exact inverse_square
    (adelicFrameRightOrbitBaseChange b A h i V (s ≫ c) ρ U)
    (adelicFrameRightOrbitBaseChange c ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U)
    (adelicFrameRightOrbitBaseChange (c ≫ b) A h i V s ρ U)
    (adelicFrameRightOrbitTestIso A h i V ρ U ((Over.mapComp c b).app (Over.mk s)))
    (adelicFrameRightOrbitBaseChangeComp A h i V ρ U b c s)
    (adelicFrameRightOrbitBaseChange_base_comp A h i V ρ U b c s) q.1

end Full
section Away
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω : Type u} [Field Ω] {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))
  (htor : TorsionFiniteEtaleStatement.{u})

/-- Transport fixed orbit classes along equality of their geometric points. -/
def primeToAdelicFrameOrbitPointEq {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) (U : Subgroup G) :
    PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U ≃
      PrimeToAdelicFrameOrbit A m hAway i V t ρ ht htor hu U := by
  subst t
  exact Equiv.refl _

/-- The equality transport is the actual test-isomorphism map whenever its
underlying map of point schemes is the identity. -/
theorem primeToAdelicFrameOrbitPointEq_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) (U : Subgroup G)
    (e : Over.mk s ≅ Over.mk t) (he : e.hom.left = 𝟙 _)
    (q : PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) :
    (primeToAdelicFrameOrbitPointEq A m hAway i V ρ htor hst hs ht hu U q).1 =
      primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U e q.1 := by
  subst t
  have heq : e = Iso.refl (Over.mk s) := by
    apply Iso.ext
    apply Over.OverMorphism.ext
    exact he
  subst e
  exact (primeToAdelicFrameRightOrbitTestIso_refl A m hAway i V ρ U q.1).symm

/-- Inverse equality transport has the inverse actual test-isomorphism map. -/
theorem primeToAdelicFrameOrbitPointEq_symm_val {s t : Spec (.of Ω) ⟶ S} (hst : s = t)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (ht : ∀ Y : Cover S, Finite (Fiber t Y))
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤))) (U : Subgroup G)
    (e : Over.mk s ≅ Over.mk t) (he : e.hom.left = 𝟙 _)
    (q : PrimeToAdelicFrameOrbit A m hAway i V t ρ ht htor hu U) :
    ((primeToAdelicFrameOrbitPointEq A m hAway i V ρ htor hst hs ht hu U).symm q).1 =
      (primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U e).symm q.1 := by
  apply (primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U e).injective
  rw [Equiv.apply_symm_apply]
  rw [← primeToAdelicFrameOrbitPointEq_val A m hAway i V ρ htor hst hs ht hu U e he]
  rw [Equiv.apply_symm_apply]

/-- Pullback along the identity agrees with equality transport after the actual
identity abelian-scheme comparison. -/
theorem primeToAdelicFrameOrbitPullback_id (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (hs' : ∀ Y : Cover S, Finite (Fiber (s ≫ 𝟙 S) Y))
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (hbc : RationalMonodromyBaseChange.{u}) (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit A m hAway i V (s ≫ 𝟙 S) ρ hs' htor hu U) :
    primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U
        (primeToAdelicFrameOrbitPullback (𝟙 S) A m hAway i V s ρ hs hs' htor hu hu hbc U q) =
      primeToAdelicFrameOrbitPointEq A m hAway i V ρ htor (Category.comp_id s) hs' hs hu U q := by
  apply Subtype.ext
  rw [primeToAdelicFrameOrbitBaseChangeId_val, primeToAdelicFrameOrbitPullback_val,
    primeToAdelicFrameOrbitPointEq_val A m hAway i V ρ htor (Category.comp_id s) hs' hs hu U
      ((Over.mapId S).app (Over.mk s)) rfl]
  have hh := primeToAdelicFrameRightOrbitBaseChange_id A m hAway i V ρ U s
    ((primeToAdelicFrameRightOrbitBaseChange (𝟙 S) A m hAway i V s ρ U).symm q.1)
  rw [Equiv.apply_symm_apply] at hh
  exact hh.symm

/-- Direct pullback, followed by the actual abelian-scheme comparison, agrees
with successive pointed pullback after the canonical associativity transport. -/
theorem primeToAdelicFrameOrbitPullback_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
    (hc : ∀ Y : Cover S', Finite (Fiber (s ≫ c) Y))
    (hb : ∀ Y : Cover S, Finite (Fiber ((s ≫ c) ≫ b) Y))
    (hbcpt : ∀ Y : Cover S, Finite (Fiber (s ≫ (c ≫ b)) Y))
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
    (hu'' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S'', ⊤)))
    (hbc : RationalMonodromyBaseChange.{u}) (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit A m hAway i V ((s ≫ c) ≫ b) ρ hb htor hu U) :
    primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu'' U
        (primeToAdelicFrameOrbitPullback (c ≫ b) A m hAway i V s ρ hs hbcpt htor hu hu'' hbc U
          ((primeToAdelicFrameOrbitPointEq A m hAway i V ρ htor (Category.assoc s c b).symm
            hbcpt hb hu U).symm q)) =
      primeToAdelicFrameOrbitPullback c ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ hs hc htor hu' hu'' hbc U
        (primeToAdelicFrameOrbitPullback b A m hAway i V (s ≫ c) ρ hc hb htor hu hu' hbc U q) := by
  let := primeToAdelicFrameRightAction A m hAway i V ((s ≫ c) ≫ b) ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V ((s ≫ c) ≫ b) hb htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V ((s ≫ c) ≫ b) ρ hb htor hu
  apply Subtype.ext
  rw [primeToAdelicFrameOrbitBaseChangeComp_val, primeToAdelicFrameOrbitPullback_val,
    primeToAdelicFrameOrbitPointEq_symm_val A m hAway i V ρ htor (Category.assoc s c b).symm
      hbcpt hb hu U ((Over.mapComp c b).app (Over.mk s)) rfl,
    primeToAdelicFrameOrbitPullback_val, primeToAdelicFrameOrbitPullback_val]
  exact inverse_square
    (primeToAdelicFrameRightOrbitBaseChange b A m hAway i V (s ≫ c) ρ U)
    (primeToAdelicFrameRightOrbitBaseChange c ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U)
    (primeToAdelicFrameRightOrbitBaseChange (c ≫ b) A m hAway i V s ρ U)
    (primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U ((Over.mapComp c b).app (Over.mk s)))
    (primeToAdelicFrameRightOrbitBaseChangeComp A m hAway i V ρ U b c s)
    (primeToAdelicFrameRightOrbitBaseChange_base_comp A m hAway i V ρ U b c s) q.1

end Away
end Langlands.AbelianScheme.Tate
