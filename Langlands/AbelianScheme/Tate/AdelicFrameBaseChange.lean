import Langlands.AbelianScheme.Tate.AdelicBaseChange
import Langlands.AbelianScheme.Tate.AdelicFrameIsogeny
import Langlands.AbelianScheme.Tate.PrimeToAdelicFrameIsogeny
import Langlands.Shimura.PEL.OrbitEquiv

/-! # Pointed base change of ambient adelic Tate frame orbits -/

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
variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (A : AbelianScheme S) (h : Global.RationalProfiniteIntegerAdeleComparison)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S')

/-- The actual pointed comparison on ambient full adelic Tate frames. -/
def adelicFrameBaseChange :
    AdelicFrame ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ≃
      AdelicFrame A h i V (s ≫ b) := by
  letI := finiteAdeleAlgebraModule ((AbelianScheme.baseChange b).obj A)
    (Over.mk s) (fun _ => True) h ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
  letI := finiteAdeleAlgebraModule A (Over.mk (s ≫ b)) (fun _ => True) h i
  exact LinearFrame.postcomp (finiteAdeleAlgebraBaseChange b (Over.mk s) (fun _ => True) A i h)

@[simp] theorem adelicFrameBaseChange_apply
    (eta : AdelicFrame ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s) (x : V) :
    adelicFrameBaseChange b A h i V s eta x =
      rationalBaseChange b A (Over.mk s) (fun _ => True) (eta x) := rfl

@[simp] theorem adelicFrameBaseChange_symm_apply
    (eta : AdelicFrame A h i V (s ≫ b)) (x : V) :
    (adelicFrameBaseChange b A h i V s).symm eta x =
      (rationalBaseChange b A (Over.mk s) (fun _ => True)).symm (eta x) := rfl

variable {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V))

/-- Right orbits of ambient full frames, before imposing geometric invariance. -/
abbrev AdelicFrameRightOrbit {S : Scheme.{u}} (A : AbelianScheme S)
    (h : Global.RationalProfiniteIntegerAdeleComparison) (i : D →ₐ[ℚ] End0 A)
    (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.FiniteAdeles ℚ) V]
    (s : Spec (.of Ω) ⟶ S)
    (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.FiniteAdeles ℚ] V)) (U : Subgroup G) :=
  letI := adelicFrameRightAction A h i V s ρ
  RightOrbit (AdelicFrame A h i V s) U

/-- Actual pointed base change commutes with source precomposition. -/
theorem adelicFrameBaseChange_right :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := adelicFrameRightAction A h i V (s ≫ b) ρ
    ∀ eta (g : G), adelicFrameBaseChange b A h i V s (right eta g) =
      right (adelicFrameBaseChange b A h i V s eta) g := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
  let := adelicFrameRightAction A h i V (s ≫ b) ρ
  intro eta g
  apply LinearEquiv.ext
  intro x
  rfl

/-- The comparison on underlying frame orbits; its inverse pulls frames back. -/
def adelicFrameRightOrbitBaseChange (U : Subgroup G) :
    AdelicFrameRightOrbit ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U ≃
      AdelicFrameRightOrbit A h i V (s ≫ b) ρ U := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
  letI := adelicFrameRightAction A h i V (s ≫ b) ρ
  exact RightOrbit.equiv U (adelicFrameBaseChange b A h i V s)
    (adelicFrameBaseChange_right b A h i V s ρ)

/-- Comparison commutes with the level translation associated to a transporter. -/
theorem adelicFrameRightOrbitBaseChange_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := adelicFrameRightAction A h i V (s ≫ b) ρ
    ∀ q : AdelicFrameRightOrbit ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U,
      adelicFrameRightOrbitBaseChange b A h i V s ρ U' (RightOrbit.translate g hg q) =
        RightOrbit.translate g hg (adelicFrameRightOrbitBaseChange b A h i V s ρ U q) := by
  let := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
  let := adelicFrameRightAction A h i V (s ≫ b) ρ
  intro q
  exact RightOrbit.map_translate (adelicFrameBaseChange b A h i V s)
    (adelicFrameBaseChange_right b A h i V s ρ) g hg q

@[simp] theorem adelicFrameRightOrbitBaseChange_mk (U : Subgroup G) :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := adelicFrameRightAction A h i V (s ≫ b) ρ
    ∀ eta, adelicFrameRightOrbitBaseChange b A h i V s ρ U (RightOrbit.mk U eta) =
      RightOrbit.mk U (adelicFrameBaseChange b A h i V s eta) := by
  intro eta
  rfl

@[simp] theorem adelicFrameRightOrbitBaseChange_symm_mk (U : Subgroup G) :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := adelicFrameRightAction A h i V (s ≫ b) ρ
    ∀ eta, (adelicFrameRightOrbitBaseChange b A h i V s ρ U).symm
        (RightOrbit.mk U eta) =
      RightOrbit.mk U ((adelicFrameBaseChange b A h i V s).symm eta) := by
  intro eta
  rfl

/-- Level forgetting is the identity-transporter case of the same square. -/
theorem adelicFrameRightOrbitBaseChange_forget {U U' : Subgroup G} (hU : U ≤ U') :
    letI := adelicFrameRightAction ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := adelicFrameRightAction A h i V (s ≫ b) ρ
    ∀ q : AdelicFrameRightOrbit ((AbelianScheme.baseChange b).obj A) h
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U,
      adelicFrameRightOrbitBaseChange b A h i V s ρ U'
          (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu)
          (adelicFrameRightOrbitBaseChange b A h i V s ρ U q) := by
  intro q
  exact adelicFrameRightOrbitBaseChange_translate b A h i V s ρ 1 _ q

variable {A} {B : AbelianScheme S}
/-- Intertwining of actual rational actions is preserved by actual pullback. -/
theorem rationalBaseChange_intertwines (iB : D →ₐ[ℚ] End0 B)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (i d) e.hom =
      Rationalization.comp A B B e.hom (iB d)) (d : D) :
    Rationalization.comp _ _ _
        (((AbelianScheme.rationalBaseChangeEnd b A).comp i) d)
        (AbelianScheme.rationalBaseChangeIso b e).hom =
      Rationalization.comp _ _ _ (AbelianScheme.rationalBaseChangeIso b e).hom
        (((AbelianScheme.rationalBaseChangeEnd b B).comp iB) d) := by
  simp only [AlgHom.comp_apply, AbelianScheme.rationalBaseChangeEnd_apply,
    AbelianScheme.rationalBaseChangeIso_hom]
  have hh := congrArg (AbelianScheme.rationalBaseChangeHom b (A := A) (B := B)) (he d)
  simpa only [AbelianScheme.rationalBaseChangeHom_comp] using hh

/-- The actual isogeny square on full frames. -/
theorem adelicFrameBaseChange_isogeny (iB : D →ₐ[ℚ] End0 B)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (i d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (eta : AdelicFrame ((AbelianScheme.baseChange b).obj A) h
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s) :
    adelicFrameBaseChange b B h iB V s
        (adelicFrameIsogeny h ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
          ((AbelianScheme.rationalBaseChangeEnd b B).comp iB) V s
          (AbelianScheme.rationalBaseChangeIso b e)
          (rationalBaseChange_intertwines b i iB e he) eta) =
      adelicFrameIsogeny h i iB V (s ≫ b) e he
        (adelicFrameBaseChange b A h i V s eta) := by
  apply LinearEquiv.ext
  intro x
  exact rationalBaseChange_homMap b (Over.mk s) (fun _ => True) e.hom (eta x)

end Full

section Away
variable {S S' : Scheme.{u}} (b : S' ⟶ S)
  (A : AbelianScheme S) (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
  (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m)
  {D : Type v} [Ring D] [Algebra ℚ D] (i : D →ₐ[ℚ] End0 A)
  (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
  {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ S')

/-- The actual pointed comparison on ambient prime-to-modulus adelic Tate frames. -/
def primeToAdelicFrameBaseChange :
    PrimeToAdelicFrame ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ≃
      PrimeToAdelicFrame A m hAway i V (s ≫ b) := by
  letI := primeToFiniteAdeleAlgebraModule ((AbelianScheme.baseChange b).obj A)
    (Over.mk s) hAway ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
  letI := primeToFiniteAdeleAlgebraModule A (Over.mk (s ≫ b)) hAway i
  exact LinearFrame.postcomp (primeToFiniteAdeleAlgebraBaseChange b (Over.mk s) A i hAway)

@[simp] theorem primeToAdelicFrameBaseChange_apply
    (eta : PrimeToAdelicFrame ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s) (x : V) :
    primeToAdelicFrameBaseChange b A m hAway i V s eta x =
      rationalBaseChange b A (Over.mk s) (fun n => Nat.Coprime n m) (eta x) := rfl

@[simp] theorem primeToAdelicFrameBaseChange_symm_apply
    (eta : PrimeToAdelicFrame A m hAway i V (s ≫ b)) (x : V) :
    (primeToAdelicFrameBaseChange b A m hAway i V s).symm eta x =
      (rationalBaseChange b A (Over.mk s) (fun n => Nat.Coprime n m)).symm (eta x) := rfl

variable {G : Type z} [Group G]
  (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V))

/-- Right orbits of ambient prime-to-modulus frames, before imposing geometric invariance. -/
abbrev PrimeToAdelicFrameRightOrbit {S : Scheme.{u}} (A : AbelianScheme S)
    (m : ℕ) {h : Global.RationalProfiniteIntegerAdeleComparison}
    (hAway : Global.PrimeToRationalProfiniteIntegerAdeleComparison h m) (i : D →ₐ[ℚ] End0 A)
    (V : Type w) [AddCommGroup V] [Module (D ⊗[ℚ] Global.PrimeToFiniteAdeles m) V]
    (s : Spec (.of Ω) ⟶ S)
    (ρ : G →* (V ≃ₗ[D ⊗[ℚ] Global.PrimeToFiniteAdeles m] V)) (U : Subgroup G) :=
  letI := primeToAdelicFrameRightAction A m hAway i V s ρ
  RightOrbit (PrimeToAdelicFrame A m hAway i V s) U

/-- Actual pointed base change commutes with source precomposition. -/
theorem primeToAdelicFrameBaseChange_right :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
    ∀ eta (g : G), primeToAdelicFrameBaseChange b A m hAway i V s (right eta g) =
      right (primeToAdelicFrameBaseChange b A m hAway i V s eta) g := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
  let := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
  intro eta g
  apply LinearEquiv.ext
  intro x
  rfl

/-- The comparison on underlying frame orbits; its inverse pulls frames back. -/
def primeToAdelicFrameRightOrbitBaseChange (U : Subgroup G) :
    PrimeToAdelicFrameRightOrbit ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U ≃
      PrimeToAdelicFrameRightOrbit A m hAway i V (s ≫ b) ρ U := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
  letI := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
  exact RightOrbit.equiv U (primeToAdelicFrameBaseChange b A m hAway i V s)
    (primeToAdelicFrameBaseChange_right b A m hAway i V s ρ)

/-- Comparison commutes with the level translation associated to a transporter. -/
theorem primeToAdelicFrameRightOrbitBaseChange_translate {U U' : Subgroup G}
    (g : G) (hg : ∀ u ∈ U, g⁻¹ * u * g ∈ U') :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
    ∀ q : PrimeToAdelicFrameRightOrbit ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U,
      primeToAdelicFrameRightOrbitBaseChange b A m hAway i V s ρ U' (RightOrbit.translate g hg q) =
        RightOrbit.translate g hg (primeToAdelicFrameRightOrbitBaseChange b A m hAway i V s ρ U q) := by
  let := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
    ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
  let := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
  intro q
  exact RightOrbit.map_translate (primeToAdelicFrameBaseChange b A m hAway i V s)
    (primeToAdelicFrameBaseChange_right b A m hAway i V s ρ) g hg q

@[simp] theorem primeToAdelicFrameRightOrbitBaseChange_mk (U : Subgroup G) :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
    ∀ eta, primeToAdelicFrameRightOrbitBaseChange b A m hAway i V s ρ U (RightOrbit.mk U eta) =
      RightOrbit.mk U (primeToAdelicFrameBaseChange b A m hAway i V s eta) := by
  intro eta
  rfl

@[simp] theorem primeToAdelicFrameRightOrbitBaseChange_symm_mk (U : Subgroup G) :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
    ∀ eta, (primeToAdelicFrameRightOrbitBaseChange b A m hAway i V s ρ U).symm
        (RightOrbit.mk U eta) =
      RightOrbit.mk U ((primeToAdelicFrameBaseChange b A m hAway i V s).symm eta) := by
  intro eta
  rfl

/-- Level forgetting is the identity-transporter case of the same square. -/
theorem primeToAdelicFrameRightOrbitBaseChange_forget {U U' : Subgroup G} (hU : U ≤ U') :
    letI := primeToAdelicFrameRightAction ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ
    letI := primeToAdelicFrameRightAction A m hAway i V (s ≫ b) ρ
    ∀ q : PrimeToAdelicFrameRightOrbit ((AbelianScheme.baseChange b).obj A) m hAway
        ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s ρ U,
      primeToAdelicFrameRightOrbitBaseChange b A m hAway i V s ρ U'
          (RightOrbit.translate 1 (by intro u hu; simpa using hU hu) q) =
        RightOrbit.translate 1 (by intro u hu; simpa using hU hu)
          (primeToAdelicFrameRightOrbitBaseChange b A m hAway i V s ρ U q) := by
  intro q
  exact primeToAdelicFrameRightOrbitBaseChange_translate b A m hAway i V s ρ 1 _ q

variable {A} {B : AbelianScheme S}
/-- The actual isogeny square on prime-to-modulus frames. -/
theorem primeToAdelicFrameBaseChange_isogeny (iB : D →ₐ[ℚ] End0 B)
    (e : Rationalization.of A ≅ Rationalization.of B)
    (he : ∀ d, Rationalization.comp A A B (i d) e.hom =
      Rationalization.comp A B B e.hom (iB d))
    (eta : PrimeToAdelicFrame ((AbelianScheme.baseChange b).obj A) m hAway
      ((AbelianScheme.rationalBaseChangeEnd b A).comp i) V s) :
    primeToAdelicFrameBaseChange b B m hAway iB V s
        (primeToAdelicFrameIsogeny m hAway ((AbelianScheme.rationalBaseChangeEnd b A).comp i)
          ((AbelianScheme.rationalBaseChangeEnd b B).comp iB) V s
          (AbelianScheme.rationalBaseChangeIso b e)
          (rationalBaseChange_intertwines b i iB e he) eta) =
      primeToAdelicFrameIsogeny m hAway i iB V (s ≫ b) e he
        (primeToAdelicFrameBaseChange b A m hAway i V s eta) := by
  apply LinearEquiv.ext
  intro x
  exact rationalBaseChange_homMap b (Over.mk s) (fun n => Nat.Coprime n m) e.hom (eta x)

end Away
end Langlands.AbelianScheme.Tate
