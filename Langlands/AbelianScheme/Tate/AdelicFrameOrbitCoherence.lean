import Langlands.AbelianScheme.Tate.AdelicFrameCoherence

/-! # Identity and composition coherence on actual Tate frame right orbits -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u v w z
namespace Langlands.AbelianScheme.Tate
open Shimura.PEL

section Full
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V)) (U : Subgroup G)

/-- Actual test-isomorphism transport on unrestricted full frame right orbits. -/
def adelicFrameRightOrbitTestIso (e : Over.mk s ≅ Over.mk t) :
    AdelicFrameRightOrbit A h i V s ρ U ≃ AdelicFrameRightOrbit A h i V t ρ U := by
  letI := adelicFrameRightAction A h i V s ρ
  letI := adelicFrameRightAction A h i V t ρ
  exact RightOrbit.equiv U (adelicFrameTestIso A h i V e)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)

@[simp] theorem adelicFrameRightOrbitTestIso_mk (e : Over.mk s ≅ Over.mk t) :
    letI := adelicFrameRightAction A h i V s ρ
    letI := adelicFrameRightAction A h i V t ρ
    ∀ eta, adelicFrameRightOrbitTestIso A h i V ρ U e (RightOrbit.mk U eta) =
      RightOrbit.mk U (adelicFrameTestIso A h i V e eta) := by
  intro eta
  rfl

@[simp] theorem adelicFrameRightOrbitTestIso_symm_mk (e : Over.mk s ≅ Over.mk t) :
    letI := adelicFrameRightAction A h i V s ρ
    letI := adelicFrameRightAction A h i V t ρ
    ∀ eta, (adelicFrameRightOrbitTestIso A h i V ρ U e).symm (RightOrbit.mk U eta) =
      RightOrbit.mk U ((adelicFrameTestIso A h i V e).symm eta) := by
  intro eta
  rfl

@[simp] theorem adelicFrameRightOrbitTestIso_refl (q : AdelicFrameRightOrbit A h i V s ρ U) :
    adelicFrameRightOrbitTestIso A h i V ρ U (Iso.refl _) q = q := by
  let := adelicFrameRightAction A h i V s ρ
  induction q using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (adelicFrameTestIso_refl A h i V eta)

theorem adelicFrameRightOrbitTestIso_trans (e : Over.mk s ≅ Over.mk t)
    (f : Over.mk t ≅ Over.mk r) (q : AdelicFrameRightOrbit A h i V s ρ U) :
    adelicFrameRightOrbitTestIso A h i V ρ U (e.trans f) q =
      adelicFrameRightOrbitTestIso A h i V ρ U f
        (adelicFrameRightOrbitTestIso A h i V ρ U e q) := by
  let := adelicFrameRightAction A h i V r ρ
  induction q using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (adelicFrameTestIso_trans A h i V e f eta)

/-- Identity abelian-scheme comparison on unrestricted full frame right orbits. -/
def adelicFrameRightOrbitBaseChangeId (s : Spec (.of Ω) ⟶ S) :
    AdelicFrameRightOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ U ≃
      AdelicFrameRightOrbit A h i V s ρ U := by
  letI := adelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
  letI := adelicFrameRightAction A h i V s ρ
  exact RightOrbit.equiv U (adelicFrameBaseChangeId A h i V s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)

@[simp] theorem adelicFrameRightOrbitBaseChangeId_mk (s : Spec (.of Ω) ⟶ S) :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
    letI := adelicFrameRightAction A h i V s ρ
    ∀ eta, adelicFrameRightOrbitBaseChangeId A h i V ρ U s (RightOrbit.mk U eta) =
      RightOrbit.mk U (adelicFrameBaseChangeId A h i V s eta) := by
  intro eta
  rfl

/-- Direct-to-successive comparison on unrestricted full frame right orbits. -/
def adelicFrameRightOrbitBaseChangeComp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'') :
    AdelicFrameRightOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ U ≃
      AdelicFrameRightOrbit ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
        ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ U := by
  letI := adelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
  letI := adelicFrameRightAction
    ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
    ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
  exact RightOrbit.equiv U (adelicFrameBaseChangeComp A h i V b c s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)

@[simp] theorem adelicFrameRightOrbitBaseChangeComp_mk (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'') :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
    letI := adelicFrameRightAction
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
    ∀ eta, adelicFrameRightOrbitBaseChangeComp A h i V ρ U b c s (RightOrbit.mk U eta) =
      RightOrbit.mk U (adelicFrameBaseChangeComp A h i V b c s eta) := by
  intro eta
  rfl

@[simp] theorem adelicFrameRightOrbitBaseChangeComp_symm_mk (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'') :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
    letI := adelicFrameRightAction
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
    ∀ eta, (adelicFrameRightOrbitBaseChangeComp A h i V ρ U b c s).symm (RightOrbit.mk U eta) =
      RightOrbit.mk U ((adelicFrameBaseChangeComp A h i V b c s).symm eta) := by
  intro eta
  rfl

/-- The identity coherence equation descends to right-orbit classes. -/
theorem adelicFrameRightOrbitBaseChange_id (s : Spec (.of Ω) ⟶ S)
    (q : AdelicFrameRightOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ U) :
    adelicFrameRightOrbitTestIso A h i V ρ U ((Over.mapId S).app (Over.mk s))
        (adelicFrameRightOrbitBaseChange (𝟙 S) A h i V s ρ U q) =
      adelicFrameRightOrbitBaseChangeId A h i V ρ U s q := by
  let := adelicFrameRightAction A h i V s ρ
  induction q using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (adelicFrameBaseChange_id A h i V s eta)

/-- The binary composition coherence equation descends to right-orbit classes. -/
theorem adelicFrameRightOrbitBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (q : AdelicFrameRightOrbit
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ U) :
    adelicFrameRightOrbitBaseChange b A h i V (s ≫ c) ρ U
        (adelicFrameRightOrbitBaseChange c ((AbelianScheme.baseChange b).obj A) h
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U q) =
      adelicFrameRightOrbitTestIso A h i V ρ U ((Over.mapComp c b).app (Over.mk s))
        (adelicFrameRightOrbitBaseChange (c ≫ b) A h i V s ρ U
          ((adelicFrameRightOrbitBaseChangeComp A h i V ρ U b c s).symm q)) := by
  let := adelicFrameRightAction A h i V ((s ≫ c) ≫ b) ρ
  induction q using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U) (adelicFrameBaseChange_base_comp A h i V b c s eta)

end Full
section Away
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}
  {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V)) (U : Subgroup G)

/-- Actual test-isomorphism transport on unrestricted away frame right orbits. -/
def primeToAdelicFrameRightOrbitTestIso (e : Over.mk s ≅ Over.mk t) :
    PrimeToAdelicFrameRightOrbit A m hAway i V s ρ U ≃ PrimeToAdelicFrameRightOrbit A m hAway i V t ρ U := by
  letI := primeToAdelicFrameRightAction A m hAway i V s ρ
  letI := primeToAdelicFrameRightAction A m hAway i V t ρ
  exact RightOrbit.equiv U (primeToAdelicFrameTestIso A m hAway i V e)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)

@[simp] theorem primeToAdelicFrameRightOrbitTestIso_mk (e : Over.mk s ≅ Over.mk t) :
    letI := primeToAdelicFrameRightAction A m hAway i V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V t ρ
    ∀ eta, primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U e (RightOrbit.mk U eta) =
      RightOrbit.mk U (primeToAdelicFrameTestIso A m hAway i V e eta) := by
  intro eta
  rfl

@[simp] theorem primeToAdelicFrameRightOrbitTestIso_symm_mk (e : Over.mk s ≅ Over.mk t) :
    letI := primeToAdelicFrameRightAction A m hAway i V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V t ρ
    ∀ eta, (primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U e).symm (RightOrbit.mk U eta) =
      RightOrbit.mk U ((primeToAdelicFrameTestIso A m hAway i V e).symm eta) := by
  intro eta
  rfl

@[simp] theorem primeToAdelicFrameRightOrbitTestIso_refl (q : PrimeToAdelicFrameRightOrbit A m hAway i V s ρ U) :
    primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U (Iso.refl _) q = q := by
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  induction q using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (primeToAdelicFrameTestIso_refl A m hAway i V eta)

theorem primeToAdelicFrameRightOrbitTestIso_trans (e : Over.mk s ≅ Over.mk t)
    (f : Over.mk t ≅ Over.mk r) (q : PrimeToAdelicFrameRightOrbit A m hAway i V s ρ U) :
    primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U (e.trans f) q =
      primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U f
        (primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U e q) := by
  let := primeToAdelicFrameRightAction A m hAway i V r ρ
  induction q using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (primeToAdelicFrameTestIso_trans A m hAway i V e f eta)

/-- Identity abelian-scheme comparison on unrestricted away frame right orbits. -/
def primeToAdelicFrameRightOrbitBaseChangeId (s : Spec (.of Ω) ⟶ S) :
    PrimeToAdelicFrameRightOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ U ≃
      PrimeToAdelicFrameRightOrbit A m hAway i V s ρ U := by
  letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
  letI := primeToAdelicFrameRightAction A m hAway i V s ρ
  exact RightOrbit.equiv U (primeToAdelicFrameBaseChangeId A m hAway i V s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)

@[simp] theorem primeToAdelicFrameRightOrbitBaseChangeId_mk (s : Spec (.of Ω) ⟶ S) :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V s ρ
    ∀ eta, primeToAdelicFrameRightOrbitBaseChangeId A m hAway i V ρ U s (RightOrbit.mk U eta) =
      RightOrbit.mk U (primeToAdelicFrameBaseChangeId A m hAway i V s eta) := by
  intro eta
  rfl

/-- Direct-to-successive comparison on unrestricted away frame right orbits. -/
def primeToAdelicFrameRightOrbitBaseChangeComp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'') :
    PrimeToAdelicFrameRightOrbit ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ U ≃
      PrimeToAdelicFrameRightOrbit ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
        ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ U := by
  letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
  letI := primeToAdelicFrameRightAction
    ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
    ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
  exact RightOrbit.equiv U (primeToAdelicFrameBaseChangeComp A m hAway i V b c s)
    (fun eta g => by apply LinearEquiv.ext; intro x; rfl)

@[simp] theorem primeToAdelicFrameRightOrbitBaseChangeComp_mk (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'') :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
    ∀ eta, primeToAdelicFrameRightOrbitBaseChangeComp A m hAway i V ρ U b c s (RightOrbit.mk U eta) =
      RightOrbit.mk U (primeToAdelicFrameBaseChangeComp A m hAway i V b c s eta) := by
  intro eta
  rfl

@[simp] theorem primeToAdelicFrameRightOrbitBaseChangeComp_symm_mk (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'') :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ
    ∀ eta, (primeToAdelicFrameRightOrbitBaseChangeComp A m hAway i V ρ U b c s).symm (RightOrbit.mk U eta) =
      RightOrbit.mk U ((primeToAdelicFrameBaseChangeComp A m hAway i V b c s).symm eta) := by
  intro eta
  rfl

/-- The identity coherence equation descends to right-orbit classes. -/
theorem primeToAdelicFrameRightOrbitBaseChange_id (s : Spec (.of Ω) ⟶ S)
    (q : PrimeToAdelicFrameRightOrbit ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ρ U) :
    primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U ((Over.mapId S).app (Over.mk s))
        (primeToAdelicFrameRightOrbitBaseChange (𝟙 S) A m hAway i V s ρ U q) =
      primeToAdelicFrameRightOrbitBaseChangeId A m hAway i V ρ U s q := by
  let := primeToAdelicFrameRightAction A m hAway i V s ρ
  induction q using Quotient.inductionOn with
  | h eta => exact congrArg (RightOrbit.mk U) (primeToAdelicFrameBaseChange_id A m hAway i V s eta)

/-- The binary composition coherence equation descends to right-orbit classes. -/
theorem primeToAdelicFrameRightOrbitBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (q : PrimeToAdelicFrameRightOrbit
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s ρ U) :
    primeToAdelicFrameRightOrbitBaseChange b A m hAway i V (s ≫ c) ρ U
        (primeToAdelicFrameRightOrbitBaseChange c ((AbelianScheme.baseChange b).obj A) m hAway
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U q) =
      primeToAdelicFrameRightOrbitTestIso A m hAway i V ρ U ((Over.mapComp c b).app (Over.mk s))
        (primeToAdelicFrameRightOrbitBaseChange (c ≫ b) A m hAway i V s ρ U
          ((primeToAdelicFrameRightOrbitBaseChangeComp A m hAway i V ρ U b c s).symm q)) := by
  let := primeToAdelicFrameRightAction A m hAway i V ((s ≫ c) ≫ b) ρ
  induction q using Quotient.inductionOn with
  | h eta =>
    exact congrArg (RightOrbit.mk U) (primeToAdelicFrameBaseChange_base_comp A m hAway i V b c s eta)

end Away
end Langlands.AbelianScheme.Tate
