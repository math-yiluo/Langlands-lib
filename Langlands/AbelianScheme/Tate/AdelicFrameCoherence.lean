import Langlands.AbelianScheme.Tate.AdelicFrameBaseChange
import Langlands.AbelianScheme.Tate.AdelicBaseChangeCoherence
import Langlands.AbelianScheme.Tate.AdelicTestScheme

/-! # Identity and composition coherence of actual adelic Tate frames -/

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

/-- Frame transport along an actual isomorphism of the test schemes. -/
def adelicFrameTestIso (e : Over.mk s ≅ Over.mk t) :
    AdelicFrame A h i V s ≃ AdelicFrame A h i V t := by
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  letI := finiteAdeleAlgebraModule A (Over.mk t) (fun _ => True) h i
  exact LinearFrame.postcomp (finiteAdeleAlgebraTestIso A (fun _ => True) i h e)

@[simp] theorem adelicFrameTestIso_apply (e : Over.mk s ≅ Over.mk t)
    (eta : AdelicFrame A h i V s) (x : V) :
    adelicFrameTestIso A h i V e eta x =
      rationalTestRestrict A (fun _ => True) e.inv (eta x) := rfl

@[simp] theorem adelicFrameTestIso_symm_apply (e : Over.mk s ≅ Over.mk t)
    (eta : AdelicFrame A h i V t) (x : V) :
    (adelicFrameTestIso A h i V e).symm eta x =
      rationalTestRestrict A (fun _ => True) e.hom (eta x) := rfl

@[simp] theorem adelicFrameTestIso_refl (eta : AdelicFrame A h i V s) :
    adelicFrameTestIso A h i V (Iso.refl _) eta = eta := by
  apply LinearEquiv.ext
  intro x
  exact finiteAdeleAlgebraTestIso_refl A (fun _ => True) i h (eta x)

theorem adelicFrameTestIso_trans (e : Over.mk s ≅ Over.mk t)
    (f : Over.mk t ≅ Over.mk r) (eta : AdelicFrame A h i V s) :
    adelicFrameTestIso A h i V (e.trans f) eta =
      adelicFrameTestIso A h i V f (adelicFrameTestIso A h i V e eta) := by
  apply LinearEquiv.ext
  intro x
  exact finiteAdeleAlgebraTestIso_trans A (fun _ => True) i h e f (eta x)

/-- The identity abelian-scheme comparison on ambient full frames. -/
def adelicFrameBaseChangeId (s : Spec (.of Ω) ⟶ S) :
    AdelicFrame ((AbelianScheme.baseChange (𝟙 S)).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ≃
      AdelicFrame A h i V s := by
  letI := finiteAdeleAlgebraModule ((AbelianScheme.baseChange (𝟙 S)).obj A)
    (Over.mk s) (fun _ => True) h ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i)
  letI := finiteAdeleAlgebraModule A (Over.mk s) (fun _ => True) h i
  exact LinearFrame.postcomp (finiteAdeleAlgebraBaseChangeId A i h (Over.mk s) (fun _ => True))

@[simp] theorem adelicFrameBaseChangeId_apply (s : Spec (.of Ω) ⟶ S)
    (eta : AdelicFrame ((AbelianScheme.baseChange (𝟙 S)).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s) (x : V) :
    adelicFrameBaseChangeId A h i V s eta x =
      rationalMap (Over.mk s) (fun _ => True) (AbelianScheme.baseChangeIdIso A).hom (eta x) :=
  finiteAdeleAlgebraBaseChangeId_apply A i h (Over.mk s) (fun _ => True) (eta x)

/-- The direct-to-successive abelian-scheme comparison on ambient full frames. -/
def adelicFrameBaseChangeComp (b : S' ⟶ S) (c : S'' ⟶ S') (s : Spec (.of Ω) ⟶ S'') :
    AdelicFrame ((AbelianScheme.baseChange (c ≫ b)).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ≃
      AdelicFrame ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
        ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s := by
  letI := finiteAdeleAlgebraModule ((AbelianScheme.baseChange (c ≫ b)).obj A)
    (Over.mk s) (fun _ => True) h ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i)
  letI := finiteAdeleAlgebraModule
    ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A))
    (Over.mk s) (fun _ => True) h
    ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i))
  exact LinearFrame.postcomp
    (finiteAdeleAlgebraBaseChangeComp A i h b c (Over.mk s) (fun _ => True))

@[simp] theorem adelicFrameBaseChangeComp_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (eta : AdelicFrame ((AbelianScheme.baseChange (c ≫ b)).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s) (x : V) :
    adelicFrameBaseChangeComp A h i V b c s eta x =
      rationalMap (Over.mk s) (fun _ => True) (AbelianScheme.baseChangeCompIso b c A).hom (eta x) :=
  finiteAdeleAlgebraBaseChangeComp_apply A i h b c (Over.mk s) (fun _ => True) (eta x)

@[simp] theorem adelicFrameBaseChangeComp_symm_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (eta : AdelicFrame ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s) (x : V) :
    (adelicFrameBaseChangeComp A h i V b c s).symm eta x =
      rationalMap (Over.mk s) (fun _ => True) (AbelianScheme.baseChangeCompIso b c A).inv (eta x) :=
  finiteAdeleAlgebraBaseChangeComp_symm_apply A i h b c (Over.mk s) (fun _ => True) (eta x)

/-- Identity base change agrees with the identity comparison after canonical test transport. -/
theorem adelicFrameBaseChange_id (s : Spec (.of Ω) ⟶ S)
    (eta : AdelicFrame ((AbelianScheme.baseChange (𝟙 S)).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s) :
    adelicFrameTestIso A h i V ((Over.mapId S).app (Over.mk s))
        (adelicFrameBaseChange (𝟙 S) A h i V s eta) =
      adelicFrameBaseChangeId A h i V s eta := by
  apply LinearEquiv.ext
  intro x
  exact finiteAdeleAlgebraBaseChange_id A i h (Over.mk s) (fun _ => True) (eta x)

/-- Successive frame base change agrees with direct base change and both canonical comparisons. -/
theorem adelicFrameBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (eta : AdelicFrame ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) h
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s) :
    adelicFrameBaseChange b A h i V (s ≫ c)
        (adelicFrameBaseChange c ((AbelianScheme.baseChange b).obj A) h
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s eta) =
      adelicFrameTestIso A h i V ((Over.mapComp c b).app (Over.mk s))
        (adelicFrameBaseChange (c ≫ b) A h i V s
          ((adelicFrameBaseChangeComp A h i V b c s).symm eta)) := by
  apply LinearEquiv.ext
  intro x
  exact finiteAdeleAlgebraBaseChange_base_comp A i h b c (Over.mk s) (fun _ => True) (eta x)

end Full
section Away
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω Ω' Ω'' : Type u} [Field Ω] [Field Ω'] [Field Ω'']
  {s : Spec (.of Ω) ⟶ S} {t : Spec (.of Ω') ⟶ S} {r : Spec (.of Ω'') ⟶ S}

/-- Frame transport along an actual isomorphism of the test schemes. -/
def primeToAdelicFrameTestIso (e : Over.mk s ≅ Over.mk t) :
    PrimeToAdelicFrame A m hAway i V s ≃ PrimeToAdelicFrame A m hAway i V t := by
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk t) hAway i
  exact LinearFrame.postcomp (primeToFiniteAdeleAlgebraTestIso A i hAway e)

@[simp] theorem primeToAdelicFrameTestIso_apply (e : Over.mk s ≅ Over.mk t)
    (eta : PrimeToAdelicFrame A m hAway i V s) (x : V) :
    primeToAdelicFrameTestIso A m hAway i V e eta x =
      rationalTestRestrict A (fun n => Nat.Coprime n m) e.inv (eta x) := rfl

@[simp] theorem primeToAdelicFrameTestIso_symm_apply (e : Over.mk s ≅ Over.mk t)
    (eta : PrimeToAdelicFrame A m hAway i V t) (x : V) :
    (primeToAdelicFrameTestIso A m hAway i V e).symm eta x =
      rationalTestRestrict A (fun n => Nat.Coprime n m) e.hom (eta x) := rfl

@[simp] theorem primeToAdelicFrameTestIso_refl (eta : PrimeToAdelicFrame A m hAway i V s) :
    primeToAdelicFrameTestIso A m hAway i V (Iso.refl _) eta = eta := by
  apply LinearEquiv.ext
  intro x
  exact primeToFiniteAdeleAlgebraTestIso_refl A i hAway (eta x)

theorem primeToAdelicFrameTestIso_trans (e : Over.mk s ≅ Over.mk t)
    (f : Over.mk t ≅ Over.mk r) (eta : PrimeToAdelicFrame A m hAway i V s) :
    primeToAdelicFrameTestIso A m hAway i V (e.trans f) eta =
      primeToAdelicFrameTestIso A m hAway i V f (primeToAdelicFrameTestIso A m hAway i V e eta) := by
  apply LinearEquiv.ext
  intro x
  exact primeToFiniteAdeleAlgebraTestIso_trans A i hAway e f (eta x)

/-- The identity abelian-scheme comparison on ambient away frames. -/
def primeToAdelicFrameBaseChangeId (s : Spec (.of Ω) ⟶ S) :
    PrimeToAdelicFrame ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s ≃
      PrimeToAdelicFrame A m hAway i V s := by
  letI := primeToFiniteAdeleAlgebraModule ((AbelianScheme.baseChange (𝟙 S)).obj A)
    (Over.mk s) hAway ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk s) hAway i
  exact LinearFrame.postcomp (primeToFiniteAdeleAlgebraBaseChangeId A i hAway (Over.mk s))

@[simp] theorem primeToAdelicFrameBaseChangeId_apply (s : Spec (.of Ω) ⟶ S)
    (eta : PrimeToAdelicFrame ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s) (x : V) :
    primeToAdelicFrameBaseChangeId A m hAway i V s eta x =
      rationalMap (Over.mk s) (fun n => Nat.Coprime n m) (AbelianScheme.baseChangeIdIso A).hom (eta x) :=
  primeToFiniteAdeleAlgebraBaseChangeId_apply A i hAway (Over.mk s) (eta x)

/-- The direct-to-successive abelian-scheme comparison on ambient away frames. -/
def primeToAdelicFrameBaseChangeComp (b : S' ⟶ S) (c : S'' ⟶ S') (s : Spec (.of Ω) ⟶ S'') :
    PrimeToAdelicFrame ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s ≃
      PrimeToAdelicFrame ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
        ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s := by
  letI := primeToFiniteAdeleAlgebraModule ((AbelianScheme.baseChange (c ≫ b)).obj A)
    (Over.mk s) hAway ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i)
  letI := primeToFiniteAdeleAlgebraModule
    ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A))
    (Over.mk s) hAway
    ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i))
  exact LinearFrame.postcomp
    (primeToFiniteAdeleAlgebraBaseChangeComp A i hAway b c (Over.mk s))

@[simp] theorem primeToAdelicFrameBaseChangeComp_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (eta : PrimeToAdelicFrame ((AbelianScheme.baseChange (c ≫ b)).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) V s) (x : V) :
    primeToAdelicFrameBaseChangeComp A m hAway i V b c s eta x =
      rationalMap (Over.mk s) (fun n => Nat.Coprime n m) (AbelianScheme.baseChangeCompIso b c A).hom (eta x) :=
  primeToFiniteAdeleAlgebraBaseChangeComp_apply A i hAway b c (Over.mk s) (eta x)

@[simp] theorem primeToAdelicFrameBaseChangeComp_symm_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (eta : PrimeToAdelicFrame ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s) (x : V) :
    (primeToAdelicFrameBaseChangeComp A m hAway i V b c s).symm eta x =
      rationalMap (Over.mk s) (fun n => Nat.Coprime n m) (AbelianScheme.baseChangeCompIso b c A).inv (eta x) :=
  primeToFiniteAdeleAlgebraBaseChangeComp_symm_apply A i hAway b c (Over.mk s) (eta x)

/-- Identity base change agrees with the identity comparison after canonical test transport. -/
theorem primeToAdelicFrameBaseChange_id (s : Spec (.of Ω) ⟶ S)
    (eta : PrimeToAdelicFrame ((AbelianScheme.baseChange (𝟙 S)).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) V s) :
    primeToAdelicFrameTestIso A m hAway i V ((Over.mapId S).app (Over.mk s))
        (primeToAdelicFrameBaseChange (𝟙 S) A m hAway i V s eta) =
      primeToAdelicFrameBaseChangeId A m hAway i V s eta := by
  apply LinearEquiv.ext
  intro x
  exact primeToFiniteAdeleAlgebraBaseChange_id A i hAway (Over.mk s) (eta x)

/-- Successive frame base change agrees with direct base change and both canonical comparisons. -/
theorem primeToAdelicFrameBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (s : Spec (.of Ω) ⟶ S'')
    (eta : PrimeToAdelicFrame ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) m hAway
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) V s) :
    primeToAdelicFrameBaseChange b A m hAway i V (s ≫ c)
        (primeToAdelicFrameBaseChange c ((AbelianScheme.baseChange b).obj A) m hAway
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s eta) =
      primeToAdelicFrameTestIso A m hAway i V ((Over.mapComp c b).app (Over.mk s))
        (primeToAdelicFrameBaseChange (c ≫ b) A m hAway i V s
          ((primeToAdelicFrameBaseChangeComp A m hAway i V b c s).symm eta)) := by
  apply LinearEquiv.ext
  intro x
  exact primeToFiniteAdeleAlgebraBaseChange_base_comp A i hAway b c (Over.mk s) (eta x)

end Away
end Langlands.AbelianScheme.Tate
