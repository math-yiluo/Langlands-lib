/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import WeilConjectures.AlgebraicGeometry.AffineConormalSections

/-! # Algebraic conormal wedges after extension of scalars

Source: Stacks Project, Tag 01R3(2), lemma-affine-conormal.
(blueprint: new-v2-self-tor-conormal-exterior-tensor). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry

open Function

private theorem exterior_quotient_tensor
    (A Q B C D : Type u) [CommRing A] [CommRing Q] [CommRing B]
    [Algebra A Q] [Algebra A B] [AddCommGroup C] [AddCommGroup D]
    [Module Q C] [Module A C] [IsScalarTower A Q C]
    [Module B D] [Module A D] [IsScalarTower A B D]
    (q : Q ≃ₐ[A] B) (hs : Function.Surjective (algebraMap A Q))
    (e : C ≃ₗ[A] D) (n : ℕ) :
    ∃ F : (⋀[B]^n D) ≃ₗ[B] (B ⊗[A] (⋀[Q]^n C)),
      ∀ v : Fin n → D,
        F (exteriorPower.ιMulti B n v) =
          1 ⊗ₜ[A] exteriorPower.ιMulti Q n (fun j ↦ e.symm (v j)) := by
  classical
  let H := ⋀[Q]^n C
  let E := ⋀[B]^n D
  let : Module A E := Module.compHom E (algebraMap A B)
  let : IsScalarTower A B E := IsScalarTower.of_compHom _ _ _
  have hsurj : Function.Surjective (algebraMap A B) := by
    intro b
    obtain ⟨a, ha⟩ := hs (q.symm b)
    refine ⟨a, ?_⟩
    rw [← q.commutes, ha, q.apply_symm_apply]
  let w := exteriorPower.ιMulti Q n (M := C)
  let α : D [⋀^Fin n]→ₗ[B] (B ⊗[A] H) :=
    { toFun := fun v ↦ 1 ⊗ₜ[A] w (fun j ↦ e.symm (v j))
      map_update_add' := by
        intro _ v k x y
        have hu (z : D) : (fun j ↦ e.symm (update v k z j)) =
            update (fun j ↦ e.symm (v j)) k (e.symm z) := by
          funext j
          by_cases hj : j = k <;> simp [hj]
        simp only [hu, map_add, w.map_update_add, TensorProduct.tmul_add]
      map_update_smul' := by
        intro _ v k b x
        obtain ⟨a, rfl⟩ := hsurj b
        have hsm : e.symm ((algebraMap A B a) • x) =
            (algebraMap A Q a) • e.symm x := by
          rw [IsScalarTower.algebraMap_smul B a x, e.symm.map_smul]
          exact (IsScalarTower.algebraMap_smul Q a _).symm
        have hu (z : D) : (fun j ↦ e.symm (update v k z j)) =
            update (fun j ↦ e.symm (v j)) k (e.symm z) := by
          funext j
          by_cases hj : j = k <;> simp [hj]
        rw [hu, hsm, w.map_update_smul, hu]
        change (1 : B) ⊗ₜ[A] (a • w _) = (algebraMap A B a) • (1 ⊗ₜ[A] w _)
        rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
      map_eq_zero_of_eq' := by
        intro v k l h hkl
        rw [w.map_eq_zero_of_eq _ (congrArg e.symm h) hkl, TensorProduct.tmul_zero] }
  let F := exteriorPower.alternatingMapLinearEquiv α
  have hF (v : Fin n → D) : F (exteriorPower.ιMulti B n v) =
      1 ⊗ₜ[A] w (fun j ↦ e.symm (v j)) :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti α v
  let : Algebra Q B := q.toRingHom.toAlgebra
  let : Module Q E := Module.compHom E q.toRingHom
  let : IsScalarTower Q B E := IsScalarTower.of_compHom _ _ _
  let : IsScalarTower A Q B := IsScalarTower.of_algebraMap_eq' (by ext a; exact (q.commutes a).symm)
  let : IsScalarTower A Q E := IsScalarTower.of_algebraMap_smul fun a x ↦ by
    change q (algebraMap A Q a) • x = (algebraMap A B a) • x
    rw [q.commutes]
  let z := exteriorPower.ιMulti B n (M := D)
  let β : C [⋀^Fin n]→ₗ[Q] E :=
    { toFun := fun v ↦ z (fun j ↦ e (v j))
      map_update_add' := by
        intro _ v k x y
        have hu (c : C) : (fun j ↦ e (update v k c j)) =
            update (fun j ↦ e (v j)) k (e c) := by
          funext j
          by_cases hj : j = k <;> simp [hj]
        simp only [hu, map_add, z.map_update_add]
      map_update_smul' := by
        intro _ v k r x
        obtain ⟨a, rfl⟩ := hs r
        have hsm : e ((algebraMap A Q a) • x) = (algebraMap A B a) • e x := by
          rw [IsScalarTower.algebraMap_smul Q a x, e.map_smul]
          exact (IsScalarTower.algebraMap_smul B a _).symm
        have hu (c : C) : (fun j ↦ e (update v k c j)) =
            update (fun j ↦ e (v j)) k (e c) := by
          funext j
          by_cases hj : j = k <;> simp [hj]
        rw [hu, hsm, z.map_update_smul, hu]
        change (algebraMap A B a) • z _ = q (algebraMap A Q a) • z _
        rw [q.commutes]
      map_eq_zero_of_eq' := by
        intro v k l h hkl
        exact z.map_eq_zero_of_eq _ (congrArg e h) hkl }
  let L := exteriorPower.alternatingMapLinearEquiv β
  have hL (v : Fin n → C) : L (w v) = z (fun j ↦ e (v j)) :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti β v
  let G : (B ⊗[A] H) →ₗ[B] E := TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b ↦
        { toFun := fun h ↦ b • L h
          map_add' := by intros; rw [map_add, smul_add]
          map_smul' := by
            intro a h
            rw [L.map_smul_of_tower]
            exact smul_comm _ _ _ }
      map_add' := by
        intro b c
        apply LinearMap.ext
        intro h
        exact add_smul b c (L h)
      map_smul' := by
        intro b c
        apply LinearMap.ext
        intro h
        exact mul_smul b c (L h) }
  have hG (b : B) (h : H) : G (b ⊗ₜ[A] h) = b • L h := rfl
  have hGF : G.comp F = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      hF, hG, hL, one_smul]
    change z (fun j ↦ e (e.symm (v j))) = z v
    congr 1
    funext j
    exact e.apply_symm_apply (v j)
  have hFG : F.comp G = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b h
    change F (G (b ⊗ₜ[A] h)) = b ⊗ₜ[A] h
    have hh : h ∈ Submodule.span Q (Set.range w) := by
      rw [exteriorPower.ιMulti_span]
      exact Submodule.mem_top
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨v, rfl⟩ := hh
      rw [hG, F.map_smul, hL, hF]
      simp only [e.symm_apply_apply]
      change b • (1 ⊗ₜ[A] w v) = b ⊗ₜ[A] w v
      rw [TensorProduct.smul_tmul']
      simp only [smul_eq_mul, mul_one]
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add x y hx hy ihx ihy =>
      simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) ihx ihy
    | smul r x hx ih =>
      obtain ⟨a, rfl⟩ := hs r
      rw [IsScalarTower.algebraMap_smul Q a x, TensorProduct.tmul_smul]
      rw [G.map_smul_of_tower, F.map_smul_of_tower, ih]
  refine ⟨LinearEquiv.ofLinearMap F G hFG hGF, hF⟩

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- The conormal exterior section calculation before passing to associated sheaves.
Source: Stacks Project, Tag 01R3(2), lemma-affine-conormal.
(blueprint: new-v2-self-tor-conormal-exterior-tensor).
Proof: Write A = Gamma(Y,U), I = ker(i)(U), B = Gamma(Z,i inverse-image U).
The map A to B is surjective with kernel I; hence its quotient map q : A/I to B
is an isomorphism. Apply affine_conormal_sections with R=A and r=id, obtaining
an A-linear equivalence I/I squared to N(V), taking each ideal class to its
pullback-unit image. Scalar lifting along A to B shows that this equivalence
is semilinear along q. Apply the universal property of exterior powers to it
and its inverse. Multilinearity and alternation are preserved by q, and the
composites are identities because they are identities on pure wedges. This
identifies the exterior over B with the exterior over A/I transported along q.
For M the latter exterior regarded over A, the map B tensor_A M to that
transported module sends b tensor m to q inverse(b) times m. It is well-defined
by balancing and has inverse m to 1 tensor m: lift b to a in A and use
b tensor m = 1 tensor a*m. Compose with the inverse exterior equivalence.
The formula follows from the degree-one formula and the value of the tensor
inverse. For n=0 both exterior modules are their scalar rings and the formula
sends the empty wedge to 1 tensor 1. For I=A, B is the zero ring and all the
modules are zero. No flatness or finite-generation assumption is used. -/
theorem exists_selfTor_conormal_exterior_tensor
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (n : ℕ) (U : Y.affineOpens) :
    letI : Algebra Γ(Y, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom.toAlgebra
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let M := conormalExteriorModule (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    ∃ e : (⋀[Γ(Z, i ⁻¹ᵁ U.1)]^n (N.val.obj (op (i ⁻¹ᵁ U.1))))
        ≃ₗ[Γ(Z, i ⁻¹ᵁ U.1)] (Γ(Z, i ⁻¹ᵁ U.1) ⊗[Γ(Y, U.1)] M),
      ∀ b : Fin n → i.ker.toModules.val.obj (op U.1),
        e (exteriorPower.ιMulti (Γ(Z, i ⁻¹ᵁ U.1)) n
          (fun j ↦ ((Classical.choose
            (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
              i.ker.toModules).val.app (op U.1) (b j))) =
          1 ⊗ₜ[Γ(Y, U.1)] selfTorIdealWedge i U n b := by
  classical
  let A := Γ(Y, U.1)
  let B := Γ(Z, i ⁻¹ᵁ U.1)
  let I := i.ker.ideal U
  let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let : Algebra A B := (i.app U.1).hom.toAlgebra
  let : Module A Γ(N, i ⁻¹ᵁ U.1) := Module.compHom _ (i.app U.1).hom
  let : IsScalarTower A B Γ(N, i ⁻¹ᵁ U.1) := IsScalarTower.of_compHom _ _ _
  obtain ⟨E, hE⟩ := (Scheme.Modules.affine_conormal_sections.{u, u} i).2
    U A (RingEquiv.refl A) I (by simp [I])
  let e : I.Cotangent ≃ₗ[A] Γ(N, i ⁻¹ᵁ U.1) := E
  let qring := (Ideal.quotEquivOfEq (i.ker_apply U)).trans
    ((i.app U.1).hom.quotientKerEquivOfSurjective (i.app_surjective U.1 U.2))
  let q : (A ⧸ I) ≃ₐ[A] B :=
    { qring with
      commutes' := by
        intro a
        change qring (Ideal.Quotient.mk I a) = (i.app U.1).hom a
        dsimp only [qring, RingEquiv.trans_apply]
        rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk] }
  obtain ⟨F, hF⟩ := exterior_quotient_tensor A (A ⧸ I) B I.Cotangent
    Γ(N, i ⁻¹ᵁ U.1) q Ideal.Quotient.mk_surjective e n
  refine ⟨F, ?_⟩
  intro b
  refine (hF _).trans ?_
  apply congrArg (fun t ↦ (1 : B) ⊗ₜ[A] t)
  apply congrArg (exteriorPower.ιMulti (A ⧸ I) n)
  funext j
  apply e.symm_apply_eq.mpr
  exact (hE (selfTorIdealSection i U (b j)) (b j) rfl).symm

end AlgebraicGeometry
