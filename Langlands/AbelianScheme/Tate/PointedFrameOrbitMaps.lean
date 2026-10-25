import Langlands.AbelianScheme.Tate.PointedFrameOrbitCoherence
import Langlands.AbelianScheme.Tate.PointedMonodromyBaseChangeProof

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
universe u v w z
namespace Langlands.AbelianScheme.Tate
open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate (Index)
open Shimura.PEL

section Full
variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (A : AbelianScheme S) (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S')
  {G : Type z} [Group G] (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))


/-- Pointed pullback with equivariance supplied by the proved monodromy theorem. -/
abbrev adelicFrameOrbitPullbackMap (U : Subgroup G) :
    AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U →
      AdelicFrameOrbit ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu' U :=
  adelicFrameOrbitPullback b A h i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 U

@[simp] theorem adelicFrameOrbitPullbackMap_val (U : Subgroup G)
    (q : AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U) :
    (adelicFrameOrbitPullbackMap b A h i V t ρ ht hs htor hu hu' U q).1 =
      (adelicFrameRightOrbitBaseChange b A h i V t ρ U).symm q.1 :=
  adelicFrameOrbitPullback_val b A h i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 U q

theorem adelicFrameOrbitPullbackMap_injective (U : Subgroup G) :
    Function.Injective (adelicFrameOrbitPullbackMap b A h i V t ρ ht hs htor hu hu' U) :=
  adelicFrameOrbitPullback_injective b A h i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 U

theorem adelicFrameOrbitPullbackMap_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U) :
    adelicFrameOrbitPullbackMap b A h i V t ρ ht hs htor hu hu' U'
        (adelicFrameOrbitTranslate A h i V ρ htor hu g hg q) =
      adelicFrameOrbitTranslate ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' g hg
        (adelicFrameOrbitPullbackMap b A h i V t ρ ht hs htor hu hu' U q) :=
  adelicFrameOrbitPullback_translate b A h i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 g hg q

theorem adelicFrameOrbitPullbackMap_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : AdelicFrameOrbit A h i V (t ≫ b) ρ hs htor hu U) :
    adelicFrameOrbitPullbackMap b A h i V t ρ ht hs htor hu hu' U'
        (adelicFrameOrbitForget A h i V ρ htor hu hU q) =
      adelicFrameOrbitForget ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' hU
        (adelicFrameOrbitPullbackMap b A h i V t ρ ht hs htor hu hu' U q) :=
  adelicFrameOrbitPullback_forget b A h i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 hU q

end Full

section FullCoherence
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω : Type u} [Field Ω] {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))
  (htor : TorsionFiniteEtaleStatement.{u})

theorem adelicFrameOrbitPullbackMap_id (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (hs' : ∀ Y : Cover S, Finite (Fiber (s ≫ 𝟙 S) Y))
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (U : Subgroup G)
    (q : AdelicFrameOrbit A h i V (s ≫ 𝟙 S) ρ hs' htor hu U) :
    adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U
        (adelicFrameOrbitPullbackMap (𝟙 S) A h i V s ρ hs hs' htor hu hu U q) =
      adelicFrameOrbitPointEq A h i V ρ htor (Category.comp_id s) hs' hs hu U q :=
  adelicFrameOrbitPullback_id A h i V ρ htor s hs hs' hu pointedMonodromyBaseChange.2.2 U q

theorem adelicFrameOrbitPullbackMap_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
    (hc : ∀ Y : Cover S', Finite (Fiber (s ≫ c) Y))
    (hb : ∀ Y : Cover S, Finite (Fiber ((s ≫ c) ≫ b) Y))
    (hbcpt : ∀ Y : Cover S, Finite (Fiber (s ≫ (c ≫ b)) Y))
    (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))
    (hu' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S', ⊤)))
    (hu'' : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S'', ⊤)))
    (U : Subgroup G)
    (q : AdelicFrameOrbit A h i V ((s ≫ c) ≫ b) ρ hb htor hu U) :
    adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu'' U
        (adelicFrameOrbitPullbackMap (c ≫ b) A h i V s ρ hs hbcpt htor hu hu'' U
          ((adelicFrameOrbitPointEq A h i V ρ htor (Category.assoc s c b).symm
            hbcpt hb hu U).symm q)) =
      adelicFrameOrbitPullbackMap c ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ hs hc htor hu' hu'' U
        (adelicFrameOrbitPullbackMap b A h i V (s ≫ c) ρ hc hb htor hu hu' U q) :=
  adelicFrameOrbitPullback_comp A h i V ρ htor b c s hs hc hb hbcpt hu hu' hu'' pointedMonodromyBaseChange.2.2 U q

end FullCoherence

section Away
variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (A : AbelianScheme S) (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω : Type u} [Field Ω] (t : Spec (.of Ω) ⟶ S')
  {G : Type z} [Group G] (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))
  (ht : ∀ Y : Cover S', Finite (Fiber t Y))
  (hs : ∀ Y : Cover S, Finite (Fiber (t ≫ b) Y))
  (htor : TorsionFiniteEtaleStatement.{u})
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
  (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))


/-- Pointed pullback with equivariance supplied by the proved monodromy theorem. -/
abbrev primeToAdelicFrameOrbitPullbackMap (U : Subgroup G) :
    PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U →
      PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V t ρ ht htor hu' U :=
  primeToAdelicFrameOrbitPullback b A m hAway i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 U

@[simp] theorem primeToAdelicFrameOrbitPullbackMap_val (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U) :
    (primeToAdelicFrameOrbitPullbackMap b A m hAway i V t ρ ht hs htor hu hu' U q).1 =
      (primeToAdelicFrameRightOrbitBaseChange b A m hAway i V t ρ U).symm q.1 :=
  primeToAdelicFrameOrbitPullback_val b A m hAway i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 U q

theorem primeToAdelicFrameOrbitPullbackMap_injective (U : Subgroup G) :
    Function.Injective (primeToAdelicFrameOrbitPullbackMap b A m hAway i V t ρ ht hs htor hu hu' U) :=
  primeToAdelicFrameOrbitPullback_injective b A m hAway i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 U

theorem primeToAdelicFrameOrbitPullbackMap_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U) :
    primeToAdelicFrameOrbitPullbackMap b A m hAway i V t ρ ht hs htor hu hu' U'
        (primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu g hg q) =
      primeToAdelicFrameOrbitTranslate ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' g hg
        (primeToAdelicFrameOrbitPullbackMap b A m hAway i V t ρ ht hs htor hu hu' U q) :=
  primeToAdelicFrameOrbitPullback_translate b A m hAway i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 g hg q

theorem primeToAdelicFrameOrbitPullbackMap_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : PrimeToAdelicFrameOrbit A m hAway i V (t ≫ b) ρ hs htor hu U) :
    primeToAdelicFrameOrbitPullbackMap b A m hAway i V t ρ ht hs htor hu hu' U'
        (primeToAdelicFrameOrbitForget A m hAway i V ρ htor hu hU q) =
      primeToAdelicFrameOrbitForget ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V ρ htor hu' hU
        (primeToAdelicFrameOrbitPullbackMap b A m hAway i V t ρ ht hs htor hu hu' U q) :=
  primeToAdelicFrameOrbitPullback_forget b A m hAway i V t ρ ht hs htor hu hu' pointedMonodromyBaseChange.2.2 hU q

end Away

section AwayCoherence
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω : Type u} [Field Ω] {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))
  (htor : TorsionFiniteEtaleStatement.{u})

theorem primeToAdelicFrameOrbitPullbackMap_id (s : Spec (.of Ω) ⟶ S)
    (hs : ∀ Y : Cover S, Finite (Fiber s Y))
    (hs' : ∀ Y : Cover S, Finite (Fiber (s ≫ 𝟙 S) Y))
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit A m hAway i V (s ≫ 𝟙 S) ρ hs' htor hu U) :
    primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U
        (primeToAdelicFrameOrbitPullbackMap (𝟙 S) A m hAway i V s ρ hs hs' htor hu hu U q) =
      primeToAdelicFrameOrbitPointEq A m hAway i V ρ htor (Category.comp_id s) hs' hs hu U q :=
  primeToAdelicFrameOrbitPullback_id A m hAway i V ρ htor s hs hs' hu pointedMonodromyBaseChange.2.2 U q

theorem primeToAdelicFrameOrbitPullbackMap_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
    (hc : ∀ Y : Cover S', Finite (Fiber (s ≫ c) Y))
    (hb : ∀ Y : Cover S, Finite (Fiber ((s ≫ c) ≫ b) Y))
    (hbcpt : ∀ Y : Cover S, Finite (Fiber (s ≫ (c ≫ b)) Y))
    (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))
    (hu' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S', ⊤)))
    (hu'' : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S'', ⊤)))
    (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit A m hAway i V ((s ≫ c) ≫ b) ρ hb htor hu U) :
    primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu'' U
        (primeToAdelicFrameOrbitPullbackMap (c ≫ b) A m hAway i V s ρ hs hbcpt htor hu hu'' U
          ((primeToAdelicFrameOrbitPointEq A m hAway i V ρ htor (Category.assoc s c b).symm
            hbcpt hb hu U).symm q)) =
      primeToAdelicFrameOrbitPullbackMap c ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ hs hc htor hu' hu'' U
        (primeToAdelicFrameOrbitPullbackMap b A m hAway i V (s ≫ c) ρ hc hb htor hu hu' U q) :=
  primeToAdelicFrameOrbitPullback_comp A m hAway i V ρ htor b c s hs hc hb hbcpt hu hu' hu'' pointedMonodromyBaseChange.2.2 U q

end AwayCoherence

end Langlands.AbelianScheme.Tate
