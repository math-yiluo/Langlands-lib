/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AffineAssociatedModuleFlatOver
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat

/-! # Relative flatness of the explicit finite Čech model

Source: Stacks Project, Tags 02KE and 01U4, finite affine section calculation.
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/- The section-flatness calculations are inlined below. -/

/-- The section complex associated to an affine base is flat over that base termwise.
No cohomology comparison, cover condition, or existence of a complex is asserted.
Source: Stacks Project, Tag 02KE, proof of flat base change, and Tag 01U4.
(blueprint: lem-pc-finite-affine-cech-model-flat-over).

Proof: Since T is affine and f is separated, X is separated and each nonempty finite
intersection of the affine V_i is affine. Apply hF to that intersection and the top
affine open of T. Transport scalars through GammaSpecIso to obtain precisely the
flat global-section module in affineAlternatingCechModel. There are only finitely many
increasing tuples in each degree; finite products of flat modules are flat, including
the empty product. For a flat A-module M, its associated sheaf has sections on every
affine open W of Spec A equal to Gamma(W,O) tensor_A M. These are flat over Gamma(W,O).
If W lies in an affine open Z, Gamma(W,O) is flat over Gamma(Z,O), since Z contains W
by an open immersion. Transitivity therefore gives the IsFlatOver identity condition.
Finally pull back along the isomorphism T -> Spec Gamma(T,O). Its affine section ring
isomorphisms preserve the condition just proved. Extension in negative degrees has
zero terms, whose sections are zero and flat. This proves every integer degree.
The argument includes zero rings, empty intersections and r=0. -/
theorem finiteAffineCechModel_flatOver {X T : Scheme.{u}} (f : X ⟶ T)
    [IsAffine T] [IsSeparated f] (F : X.Modules) (hF : F.IsFlatOver f)
    {r : ℕ} (V : Fin r → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) :
    ∀ n : ℤ, ((finiteAffineCechModel f F V).X n).IsFlatOver (𝟙 T) := by
  intro n
  let A := Γ(T, ⊤)
  let p := f ≫ T.toSpecΓ
  have hp : F.IsFlatOver p := by
    intro W U e
    let W1 : T.affineOpens := ⟨T.toSpecΓ ⁻¹ᵁ W.1, W.2.preimage_of_isIso T.toSpecΓ⟩
    have e1 : U.1 ≤ f ⁻¹ᵁ W1.1 := by
      change U.1 ≤ f ⁻¹ᵁ (T.toSpecΓ ⁻¹ᵁ W.1)
      simpa [p, Scheme.Hom.comp_preimage] using e
    let φ := T.toSpecΓ.app W.1
    let ψ := f.appLE W1.1 U.1 e1
    let : Module Γ(T, W1.1) Γ(F, U.1) := Module.compHom _ ψ.hom
    have : Module.Flat Γ(T, W1.1) Γ(F, U.1) := hF W1 U e1
    let : Algebra Γ(Spec Γ(T, ⊤), W.1) Γ(T, W1.1) := φ.hom.toAlgebra
    have : Module.Flat Γ(Spec Γ(T, ⊤), W.1) Γ(T, W1.1) :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso φ)
    let : Module Γ(Spec Γ(T, ⊤), W.1) Γ(F, U.1) := Module.compHom _ φ.hom
    let : IsScalarTower Γ(Spec Γ(T, ⊤), W.1) Γ(T, W1.1) Γ(F, U.1) :=
      ⟨fun a b m ↦ mul_smul _ _ _⟩
    have hh := Module.Flat.trans Γ(Spec Γ(T, ⊤), W.1) Γ(T, W1.1) Γ(F, U.1)
    simpa only [Scheme.Hom.comp_appLE] using hh
  let C := alternatingCechComplex V F.presheafModuleCat
  let M := (ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ p.appTop).hom)).obj
    ((C.extend ComplexShape.embeddingUpNat).X n)
  have hM : Module.Flat A M := by
    by_cases hn : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = n
    · obtain ⟨k, hk⟩ := hn
      have hsep : IsSeparated p := inferInstance
      have ht (t : Fin (k + 1) ↪o Fin r) :
          IsAffineOpen (alternatingCechIntersection V t) := by
        have : IsSeparated (p ≫ terminal.from (Spec A)) := inferInstance
        have : X.IsSeparated := ⟨by rwa [terminal.comp_from] at this⟩
        exact IsAffineOpen.iInf fun j ↦ hV (t j)
      let MM := fun t : Fin (k + 1) ↪o Fin r ↦
        ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ p.appTop).hom)).obj
          (F.presheafModuleCat.obj (Opposite.op
            (alternatingCechIntersection V t))))
      have hterm (t : Fin (k + 1) ↪o Fin r) : Module.Flat A
          (((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ p.appTop).hom)).obj
            (F.presheafModuleCat.obj (Opposite.op
              (alternatingCechIntersection V t))))) := by
        let S := Γ(Spec A, ⊤)
        let N := Γ(F, alternatingCechIntersection V t)
        let : Module S N := Module.compHom N (p.appLE ⊤
          (alternatingCechIntersection V t) (by simp)).hom
        have hN : Module.Flat S N := hp ⟨⊤, isAffineOpen_top _⟩
          ⟨_, ht t⟩ (by simp)
        let : Algebra A S := (Scheme.ΓSpecIso A).inv.hom.toAlgebra
        let : Module A S := Module.compHom S (Scheme.ΓSpecIso A).inv.hom
        have : Module.Flat A S := RingHom.Flat.of_bijective
          (Scheme.ΓSpecIso A).symm.commRingCatIsoToRingEquiv.bijective
        let : Module A N := Module.compHom N
          (((Scheme.ΓSpecIso A).inv ≫ p.appLE ⊤
            (alternatingCechIntersection V t) (by simp)).hom)
        let : IsScalarTower A S N :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        have hh := Module.Flat.trans A S N
        convert hh using 1
        · rfl
        · congr 1
      have : ∀ t, Module.Flat A (MM t) := hterm
      have hprod : Module.Flat A (Π₀ t, MM t) := inferInstance
      have halt : Module.Flat A
          ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ p.appTop).hom)).obj
            (C.X k)) := Module.Flat.of_linearEquiv
        (DFinsupp.linearEquivFunOnFintype (R := A) (M := fun t ↦ MM t)).symm
      exact Module.Flat.of_linearEquiv
        (((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ p.appTop).hom)).mapIso
          (C.extendXIso ComplexShape.embeddingUpNat hk)).toLinearEquiv)
    · have hz := C.isZero_extend_X ComplexShape.embeddingUpNat n (by simpa using hn)
      have hz' := Functor.map_isZero
        (ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ p.appTop).hom)) hz
      have := ModuleCat.subsingleton_of_isZero hz'
      exact Module.Flat.of_free
  exact flatOver_affineAssociatedModule T M hM

end AlgebraicGeometry.Scheme.Modules
