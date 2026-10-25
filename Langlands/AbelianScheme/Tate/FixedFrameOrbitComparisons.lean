import Langlands.AbelianScheme.Tate.AdelicFrameOrbitCoherence

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

section Full
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω : Type u} [Field Ω]
  {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))
  (htor : TorsionFiniteEtaleStatement.{u})
section Id
variable (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))

/-- The actual identity abelian-scheme comparison on fixed full frame orbits. -/
def adelicFrameOrbitBaseChangeId (U : Subgroup G) :
    AdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U ≃
      AdelicFrameOrbit A h i V s ρ hs htor hu U := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
  let := adelicFrameMonodromyAction ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s hs htor hu
  let := adelicFrameActionsComm ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu
  let := adelicFrameRightAction A h i V s ρ
  let := adelicFrameMonodromyAction A h i V s hs htor hu
  let := adelicFrameActionsComm A h i V s ρ hs htor hu
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (adelicFrameBaseChangeId A h i V s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      change (adelicFrameBaseChangeId A h i V s (γ • eta)) x =
        rationalMonodromy s hs htor A (fun _ => True) hu γ
          ((adelicFrameBaseChangeId A h i V s eta) x)
      simp only [adelicFrameBaseChangeId_apply]
      exact
        (rationalMonodromy_map s hs htor (fun _ => True) hu (AbelianScheme.baseChangeIdIso A).hom γ (eta x)).symm)

@[simp] theorem adelicFrameOrbitBaseChangeId_val (U : Subgroup G)
    (q : AdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U) :
    (adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U q).1 =
      adelicFrameRightOrbitBaseChangeId A h i V ρ U s q.1 := rfl

@[simp] theorem adelicFrameOrbitBaseChangeId_symm_val (U : Subgroup G)
    (q : AdelicFrameOrbit A h i V s ρ hs htor hu U) :
    ((adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U).symm q).1 =
      (adelicFrameRightOrbitBaseChangeId A h i V ρ U s).symm q.1 := rfl

/-- The comparison commutes with transporter-defined change of level. -/
theorem adelicFrameOrbitBaseChangeId_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : AdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U) :
    adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U' (adelicFrameOrbitTranslate ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ρ htor hu g hg q) =
      adelicFrameOrbitTranslate A h i V ρ htor hu g hg (adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U q) := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
  let := adelicFrameRightAction A h i V s ρ
  apply Subtype.ext
  exact RightOrbit.map_translate (adelicFrameBaseChangeId A h i V s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl) g hg q.1

/-- The comparison commutes with forgetting a finer level. -/
theorem adelicFrameOrbitBaseChangeId_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : AdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U) :
    adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U' (adelicFrameOrbitForget ((AbelianScheme.baseChange (𝟙 S)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ρ htor hu hU q) =
      adelicFrameOrbitForget A h i V ρ htor hu hU (adelicFrameOrbitBaseChangeId A h i V ρ htor s hs hu U q) :=
  adelicFrameOrbitBaseChangeId_translate A h i V ρ htor s hs hu 1 _ q

end Id
section Comp
variable (b : S' ⟶ S) (c : S'' ⟶ S') (s : Spec (.of Ω) ⟶ S'')
  (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S'', ⊤)))

/-- The actual direct-to-successive abelian-scheme comparison on fixed full frame orbits. -/
def adelicFrameOrbitBaseChangeComp (U : Subgroup G) :
    AdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U ≃
      AdelicFrameOrbit ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ hs htor hu U := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
  let := adelicFrameMonodromyAction ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s hs htor hu
  let := adelicFrameActionsComm ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu
  let := adelicFrameRightAction ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
  let := adelicFrameMonodromyAction ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s hs htor hu
  let := adelicFrameActionsComm ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ hs htor hu
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (adelicFrameBaseChangeComp A h i V b c s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      change (adelicFrameBaseChangeComp A h i V b c s (γ • eta)) x =
        rationalMonodromy s hs htor ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) (fun _ => True) hu γ
          ((adelicFrameBaseChangeComp A h i V b c s eta) x)
      simp only [adelicFrameBaseChangeComp_apply]
      exact
        (rationalMonodromy_map s hs htor (fun _ => True) hu (AbelianScheme.baseChangeCompIso b c A).hom γ (eta x)).symm)

@[simp] theorem adelicFrameOrbitBaseChangeComp_val (U : Subgroup G)
    (q : AdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U) :
    (adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu U q).1 =
      adelicFrameRightOrbitBaseChangeComp A h i V ρ U b c s q.1 := rfl

@[simp] theorem adelicFrameOrbitBaseChangeComp_symm_val (U : Subgroup G)
    (q : AdelicFrameOrbit ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ hs htor hu U) :
    ((adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu U).symm q).1 =
      (adelicFrameRightOrbitBaseChangeComp A h i V ρ U b c s).symm q.1 := rfl

/-- The comparison commutes with transporter-defined change of level. -/
theorem adelicFrameOrbitBaseChangeComp_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : AdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U) :
    adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu U' (adelicFrameOrbitTranslate ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ρ htor hu g hg q) =
      adelicFrameOrbitTranslate ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ρ htor hu g hg (adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu U q) := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
  let := adelicFrameRightAction ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
  apply Subtype.ext
  exact RightOrbit.map_translate (adelicFrameBaseChangeComp A h i V b c s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl) g hg q.1

/-- The comparison commutes with forgetting a finer level. -/
theorem adelicFrameOrbitBaseChangeComp_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : AdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U) :
    adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu U' (adelicFrameOrbitForget ((AbelianScheme.baseChange (c ≫ b)).obj A) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ρ htor hu hU q) =
      adelicFrameOrbitForget ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ρ htor hu hU (adelicFrameOrbitBaseChangeComp A h i V ρ htor b c s hs hu U q) :=
  adelicFrameOrbitBaseChangeComp_translate A h i V ρ htor b c s hs hu 1 _ q

end Comp
end Full
section Away
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω : Type u} [Field Ω]
  {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))
  (htor : TorsionFiniteEtaleStatement.{u})
section Id
variable (s : Spec (.of Ω) ⟶ S)
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S, ⊤)))

/-- The actual identity abelian-scheme comparison on fixed prime-to-modulus frame orbits. -/
def primeToAdelicFrameOrbitBaseChangeId (U : Subgroup G) :
    PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U ≃
      PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
  let := primeToAdelicFrameMonodromyAction ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s hs htor hu
  let := primeToAdelicFrameActionsComm ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  let := primeToAdelicFrameMonodromyAction A m hAway i V s hs htor hu
  let := primeToAdelicFrameActionsComm A m hAway i V s ρ hs htor hu
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (primeToAdelicFrameBaseChangeId A m hAway i V s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      change (primeToAdelicFrameBaseChangeId A m hAway i V s (γ • eta)) x =
        rationalMonodromy s hs htor A (fun n => Nat.Coprime n m) hu γ
          ((primeToAdelicFrameBaseChangeId A m hAway i V s eta) x)
      simp only [primeToAdelicFrameBaseChangeId_apply]
      exact
        (rationalMonodromy_map s hs htor (fun n => Nat.Coprime n m) hu (AbelianScheme.baseChangeIdIso A).hom γ (eta x)).symm)

@[simp] theorem primeToAdelicFrameOrbitBaseChangeId_val (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U) :
    (primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U q).1 =
      primeToAdelicFrameRightOrbitBaseChangeId A m hAway i V ρ U s q.1 := rfl

@[simp] theorem primeToAdelicFrameOrbitBaseChangeId_symm_val (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit A m hAway i V s ρ hs htor hu U) :
    ((primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U).symm q).1 =
      (primeToAdelicFrameRightOrbitBaseChangeId A m hAway i V ρ U s).symm q.1 := rfl

/-- The comparison commutes with transporter-defined change of level. -/
theorem primeToAdelicFrameOrbitBaseChangeId_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U' (primeToAdelicFrameOrbitTranslate ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ρ htor hu g hg q) =
      primeToAdelicFrameOrbitTranslate A m hAway i V ρ htor hu g hg (primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U q) := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  apply Subtype.ext
  exact RightOrbit.map_translate (primeToAdelicFrameBaseChangeId A m hAway i V s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl) g hg q.1

/-- The comparison commutes with forgetting a finer level. -/
theorem primeToAdelicFrameOrbitBaseChangeId_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U' (primeToAdelicFrameOrbitForget ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V ρ htor hu hU q) =
      primeToAdelicFrameOrbitForget A m hAway i V ρ htor hu hU (primeToAdelicFrameOrbitBaseChangeId A m hAway i V ρ htor s hs hu U q) :=
  primeToAdelicFrameOrbitBaseChangeId_translate A m hAway i V ρ htor s hs hu 1 _ q

end Id
section Comp
variable (b : S' ⟶ S) (c : S'' ⟶ S') (s : Spec (.of Ω) ⟶ S'')
  (hs : ∀ Y : Cover S'', Finite (Fiber s Y))
  (hu : ∀ n : Index (fun n => Nat.Coprime n m), IsUnit (n.val : Γ(S'', ⊤)))

/-- The actual direct-to-successive abelian-scheme comparison on fixed prime-to-modulus frame orbits. -/
def primeToAdelicFrameOrbitBaseChangeComp (U : Subgroup G) :
    PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U ≃
      PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ hs htor hu U := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
  let := primeToAdelicFrameMonodromyAction ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s hs htor hu
  let := primeToAdelicFrameActionsComm ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
  let := primeToAdelicFrameMonodromyAction ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s hs htor hu
  let := primeToAdelicFrameActionsComm ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ hs htor hu
  exact InvariantOrbit.equiv U (MulEquiv.refl (FundamentalGroup s hs))
    (primeToAdelicFrameBaseChangeComp A m hAway i V b c s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)
    (fun γ eta => by
      apply LinearEquiv.ext
      intro x
      change (primeToAdelicFrameBaseChangeComp A m hAway i V b c s (γ • eta)) x =
        rationalMonodromy s hs htor ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) (fun n => Nat.Coprime n m) hu γ
          ((primeToAdelicFrameBaseChangeComp A m hAway i V b c s eta) x)
      simp only [primeToAdelicFrameBaseChangeComp_apply]
      exact
        (rationalMonodromy_map s hs htor (fun n => Nat.Coprime n m) hu (AbelianScheme.baseChangeCompIso b c A).hom γ (eta x)).symm)

@[simp] theorem primeToAdelicFrameOrbitBaseChangeComp_val (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U) :
    (primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu U q).1 =
      primeToAdelicFrameRightOrbitBaseChangeComp A m hAway i V ρ U b c s q.1 := rfl

@[simp] theorem primeToAdelicFrameOrbitBaseChangeComp_symm_val (U : Subgroup G)
    (q : PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ hs htor hu U) :
    ((primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu U).symm q).1 =
      (primeToAdelicFrameRightOrbitBaseChangeComp A m hAway i V ρ U b c s).symm q.1 := rfl

/-- The comparison commutes with transporter-defined change of level. -/
theorem primeToAdelicFrameOrbitBaseChangeComp_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U')
    (q : PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu U' (primeToAdelicFrameOrbitTranslate ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ρ htor hu g hg q) =
      primeToAdelicFrameOrbitTranslate ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ρ htor hu g hg (primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu U q) := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
  apply Subtype.ext
  exact RightOrbit.map_translate (primeToAdelicFrameBaseChangeComp A m hAway i V b c s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl) g hg q.1

/-- The comparison commutes with forgetting a finer level. -/
theorem primeToAdelicFrameOrbitBaseChangeComp_forget {U U' : Subgroup G} (hU : U ≤ U')
    (q : PrimeToAdelicFrameOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ hs htor hu U) :
    primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu U' (primeToAdelicFrameOrbitForget ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V ρ htor hu hU q) =
      primeToAdelicFrameOrbitForget ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V ρ htor hu hU (primeToAdelicFrameOrbitBaseChangeComp A m hAway i V ρ htor b c s hs hu U q) :=
  primeToAdelicFrameOrbitBaseChangeComp_translate A m hAway i V ρ htor b c s hs hu 1 _ q

end Comp
end Away
end Langlands.AbelianScheme.Tate
