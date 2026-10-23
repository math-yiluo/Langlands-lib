import Langlands.AbelianScheme.BaseChangeCoherence
import Langlands.AbelianScheme.Tate.AdelicBaseChange
import Langlands.AbelianScheme.Tate.AwayAdelicTransport

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u
namespace Langlands.AbelianScheme.Tate
variable {S S' S'' : Scheme.{u}} (A : AbelianScheme S)
  {D : Type*} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)

/-- The identity comparison intertwines the actual pulled-back endomorphism action. -/
theorem baseChangeId_intertwines (d : D) :
    Rationalization.comp _ _ _
        (((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i) d)
        (AbelianScheme.rationalBaseChangeIdIso A).hom =
      Rationalization.comp _ _ _ (AbelianScheme.rationalBaseChangeIdIso A).hom (i d) :=
  AbelianScheme.rationalBaseChangeHom_id (i d)

/-- The composition comparison intertwines direct and successive endomorphism pullback. -/
theorem baseChangeComp_intertwines (b : S' ⟶ S) (c : S'' ⟶ S') (d : D) :
    Rationalization.comp _ _ _
        (((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i) d)
        (AbelianScheme.rationalBaseChangeCompIso b c A).hom =
      Rationalization.comp _ _ _ (AbelianScheme.rationalBaseChangeCompIso b c A).hom
        (((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i)) d) := by
  simp only [AlgHom.comp_apply, AbelianScheme.rationalBaseChangeEnd_apply]
  exact AbelianScheme.rationalBaseChangeHom_base_comp b c (A := A) (B := A) (i d)

variable (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- The identity group comparison on Tate modules is linear over the full tensor algebra. -/
def finiteAdeleAlgebraBaseChangeId (T : Over S) (P : ℕ → Prop) :
    let := finiteAdeleAlgebraModule ((AbelianScheme.baseChange (𝟙 S)).obj A) T P h
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i)
    let := finiteAdeleAlgebraModule A T P h i
    Rational ((AbelianScheme.baseChange (𝟙 S)).obj A) T P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ]
      Rational A T P :=
  finiteAdeleAlgebraIso T P h _ i (AbelianScheme.rationalBaseChangeIdIso A)
    (baseChangeId_intertwines A i)

@[simp] theorem finiteAdeleAlgebraBaseChangeId_apply (T : Over S) (P : ℕ → Prop)
    (x : Rational ((AbelianScheme.baseChange (𝟙 S)).obj A) T P) :
    finiteAdeleAlgebraBaseChangeId A i h T P x =
      rationalMap T P (AbelianScheme.baseChangeIdIso A).hom x := by
  change rationalHomMap T P (Rationalization.ofHom (AbelianScheme.baseChangeIdIso A).hom) x = _
  rw [rationalHomMap_ofHom]

/-- Direct-to-successive group pullback is linear over the full tensor algebra. -/
def finiteAdeleAlgebraBaseChangeComp (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (P : ℕ → Prop) :
    let := finiteAdeleAlgebraModule ((AbelianScheme.baseChange (c ≫ b)).obj A) T P h
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i)
    let := finiteAdeleAlgebraModule
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T P h
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i))
    Rational ((AbelianScheme.baseChange (c ≫ b)).obj A) T P ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ]
      Rational ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T P :=
  finiteAdeleAlgebraIso T P h _ _ (AbelianScheme.rationalBaseChangeCompIso b c A)
    (baseChangeComp_intertwines A i b c)

@[simp] theorem finiteAdeleAlgebraBaseChangeComp_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (P : ℕ → Prop)
    (x : Rational ((AbelianScheme.baseChange (c ≫ b)).obj A) T P) :
    finiteAdeleAlgebraBaseChangeComp A i h b c T P x =
      rationalMap T P (AbelianScheme.baseChangeCompIso b c A).hom x := by
  change rationalHomMap T P
    (Rationalization.ofHom (AbelianScheme.baseChangeCompIso b c A).hom) x = _
  rw [rationalHomMap_ofHom]

@[simp] theorem finiteAdeleAlgebraBaseChangeComp_symm_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (P : ℕ → Prop)
    (x : Rational ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T P) :
    (finiteAdeleAlgebraBaseChangeComp A i h b c T P).symm x =
      rationalMap T P (AbelianScheme.baseChangeCompIso b c A).inv x := by
  change rationalHomMap T P
    (Rationalization.ofHom (AbelianScheme.baseChangeCompIso b c A).inv) x = _
  rw [rationalHomMap_ofHom]

/-- Identity coherence for the tensor-linear actual Tate base-change comparison. -/
theorem finiteAdeleAlgebraBaseChange_id (T : Over S) (P : ℕ → Prop)
    (x : Rational ((AbelianScheme.baseChange (𝟙 S)).obj A) T P) :
    rationalTestRestrict A P ((Over.mapId S).inv.app T)
        (finiteAdeleAlgebraBaseChange (𝟙 S) T P A i h x) =
      finiteAdeleAlgebraBaseChangeId A i h T P x := by
  rw [finiteAdeleAlgebraBaseChange_apply, finiteAdeleAlgebraBaseChangeId_apply]
  exact GroupScheme.Tate.rationalBaseChange_id A.toGrp T P x

/-- Composition coherence, including the canonical test-scheme transport. -/
theorem finiteAdeleAlgebraBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (P : ℕ → Prop)
    (x : Rational ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T P) :
    finiteAdeleAlgebraBaseChange b ((Over.map c).obj T) P A i h
        (finiteAdeleAlgebraBaseChange c T P ((AbelianScheme.baseChange b).obj A)
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) h x) =
      rationalTestRestrict A P ((Over.mapComp c b).inv.app T)
        (finiteAdeleAlgebraBaseChange (c ≫ b) T P A i h
          ((finiteAdeleAlgebraBaseChangeComp A i h b c T P).symm x)) := by
  simp only [finiteAdeleAlgebraBaseChange_apply, finiteAdeleAlgebraBaseChangeComp_symm_apply]
  exact GroupScheme.Tate.rationalBaseChange_base_comp A.toGrp b c T P x

variable {h} {m : ℕ}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)

/-- The identity comparison is linear over the away tensor algebra. -/
def primeToFiniteAdeleAlgebraBaseChangeId (T : Over S) :
    let := primeToFiniteAdeleAlgebraModule ((AbelianScheme.baseChange (𝟙 S)).obj A) T hAway
      ((AbelianScheme.rationalBaseChangeEnd (𝟙 S) A).comp i)
    let := primeToFiniteAdeleAlgebraModule A T hAway i
    RationalAway ((AbelianScheme.baseChange (𝟙 S)).obj A) T m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m]
      RationalAway A T m :=
  primeToFiniteAdeleAlgebraIso T hAway _ i (AbelianScheme.rationalBaseChangeIdIso A)
    (baseChangeId_intertwines A i)

@[simp] theorem primeToFiniteAdeleAlgebraBaseChangeId_apply (T : Over S)
    (x : RationalAway ((AbelianScheme.baseChange (𝟙 S)).obj A) T m) :
    primeToFiniteAdeleAlgebraBaseChangeId A i hAway T x =
      rationalMap T (fun n => Nat.Coprime n m) (AbelianScheme.baseChangeIdIso A).hom x := by
  change rationalHomMap T _ (Rationalization.ofHom (AbelianScheme.baseChangeIdIso A).hom) x = _
  rw [rationalHomMap_ofHom]

/-- The direct-to-successive comparison is linear over the away tensor algebra. -/
def primeToFiniteAdeleAlgebraBaseChangeComp (b : S' ⟶ S) (c : S'' ⟶ S') (T : Over S'') :
    let := primeToFiniteAdeleAlgebraModule ((AbelianScheme.baseChange (c ≫ b)).obj A) T hAway
      ((AbelianScheme.rationalBaseChangeEnd (c ≫ b) A).comp i)
    let := primeToFiniteAdeleAlgebraModule
      ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T hAway
      ((AbelianScheme.rationalBaseChangeEnd c ((AbelianScheme.baseChange b).obj A)).comp
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i))
    RationalAway ((AbelianScheme.baseChange (c ≫ b)).obj A) T m ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m]
      RationalAway ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T m :=
  primeToFiniteAdeleAlgebraIso T hAway _ _ (AbelianScheme.rationalBaseChangeCompIso b c A)
    (baseChangeComp_intertwines A i b c)

@[simp] theorem primeToFiniteAdeleAlgebraBaseChangeComp_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'') (x : RationalAway ((AbelianScheme.baseChange (c ≫ b)).obj A) T m) :
    primeToFiniteAdeleAlgebraBaseChangeComp A i hAway b c T x =
      rationalMap T (fun n => Nat.Coprime n m) (AbelianScheme.baseChangeCompIso b c A).hom x := by
  change rationalHomMap T _
    (Rationalization.ofHom (AbelianScheme.baseChangeCompIso b c A).hom) x = _
  rw [rationalHomMap_ofHom]

@[simp] theorem primeToFiniteAdeleAlgebraBaseChangeComp_symm_apply (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'')
    (x : RationalAway ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T m) :
    (primeToFiniteAdeleAlgebraBaseChangeComp A i hAway b c T).symm x =
      rationalMap T (fun n => Nat.Coprime n m) (AbelianScheme.baseChangeCompIso b c A).inv x := by
  change rationalHomMap T _
    (Rationalization.ofHom (AbelianScheme.baseChangeCompIso b c A).inv) x = _
  rw [rationalHomMap_ofHom]

/-- Identity coherence for away tensor-linear base change. -/
theorem primeToFiniteAdeleAlgebraBaseChange_id (T : Over S)
    (x : RationalAway ((AbelianScheme.baseChange (𝟙 S)).obj A) T m) :
    rationalTestRestrict A (fun n => Nat.Coprime n m) ((Over.mapId S).inv.app T)
        (primeToFiniteAdeleAlgebraBaseChange (𝟙 S) T A i hAway x) =
      primeToFiniteAdeleAlgebraBaseChangeId A i hAway T x := by
  rw [primeToFiniteAdeleAlgebraBaseChange_apply, primeToFiniteAdeleAlgebraBaseChangeId_apply]
  exact GroupScheme.Tate.rationalBaseChange_id A.toGrp T _ x

/-- Composition coherence for away tensor-linear base change. -/
theorem primeToFiniteAdeleAlgebraBaseChange_base_comp (b : S' ⟶ S) (c : S'' ⟶ S')
    (T : Over S'')
    (x : RationalAway ((AbelianScheme.baseChange c).obj ((AbelianScheme.baseChange b).obj A)) T m) :
    primeToFiniteAdeleAlgebraBaseChange b ((Over.map c).obj T) A i hAway
        (primeToFiniteAdeleAlgebraBaseChange c T ((AbelianScheme.baseChange b).obj A)
          ((AbelianScheme.rationalBaseChangeEnd b A).comp i) hAway x) =
      rationalTestRestrict A (fun n => Nat.Coprime n m) ((Over.mapComp c b).inv.app T)
        (primeToFiniteAdeleAlgebraBaseChange (c ≫ b) T A i hAway
          ((primeToFiniteAdeleAlgebraBaseChangeComp A i hAway b c T).symm x)) := by
  simp only [primeToFiniteAdeleAlgebraBaseChange_apply,
    primeToFiniteAdeleAlgebraBaseChangeComp_symm_apply]
  exact GroupScheme.Tate.rationalBaseChange_base_comp A.toGrp b c T _ x

end Langlands.AbelianScheme.Tate
