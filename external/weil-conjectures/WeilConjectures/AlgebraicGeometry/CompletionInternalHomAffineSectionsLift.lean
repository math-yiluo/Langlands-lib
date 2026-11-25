/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomAffineTensorDictionary
import all WeilConjectures.AlgebraicGeometry.FinitePushforwardCoherent
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.Algebra.Module.FinitePresentation

/-! # Affine comparison for completed internal Hom

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, affine-local argument.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A compatible quotient morphism family has a unique compatible lift on each affine open.

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, affine-local proof;
Lemma 087W; Algebra, Lemmas 00MA and 00MB; More on Algebra, Lemma 087R.
(blueprint: lem-weil-pbc-completion-internal-hom-affine-sections-lift).

Proof:
1. For the affine open U put A = O_X(U), J = I(U), N = G(U), M = F(U),
   H = Hom_A(N,M). The ring A is Noetherian and N, M, H are finite. The affine
   tilde-sections adjunction, coherence of internal Hom, and the affine ideal-product
   and quotient comparison identify the source at level n with H/J^(n+1)H.
   The quotient projections on affine sections are surjective. The factorization
   equation he therefore identifies e_n(U) with canonical evaluation of quotient
   linear maps, using unique factorization through the quotient of G.
2. The affine formal-module equivalence identifies compatible quotient morphisms
   with Hom over the completed ring A^ from N^ to M^. Compatible sections of the
   source identify with H^. Their evaluation is the A^-linear componentwise map
   beta : H^ -> Hom_{A^}(N^,M^).
3. Completion of each finite module P is A^ tensor_A P. Flatness of A^ over A and
   finite presentation of N identify A^ tensor_A H with
   Hom_{A^}(A^ tensor_A N, A^ tensor_A M). Conjugate by the natural completion-tensor
   equivalences. The resulting bijection agrees with beta: both are A^-linear and
   on 1 tensor h both are the completed map h^, by completion-tensor naturality.
   Apply this bijection to the family t restricted to U. Its inverse gives the
   local section family, including transition compatibility. Injectivity gives
   uniqueness of the entire compatible family; no finite-level e_n is asserted
   to be an isomorphism. -/
theorem completion_internal_hom_affine_sections_lift {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F G : CoherentModules X)
    (e : ∀ n : ℕᵒᵖ,
      formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) G.obj F.obj) ⟶
        SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj))
    (he : ∀ n : ℕᵒᵖ,
        formalModuleQuotientπ I (n.unop + 1) (SheafOfModules.homObj
          (R := X.toRingedSpace.sheaf) G.obj F.obj) ≫
          e n ≫ SheafOfModules.homObjMap
            (R := X.toRingedSpace.sheaf) (formalModuleQuotientπ I (n.unop + 1) G.obj)
            (𝟙 (formalModuleQuotient I (n.unop + 1) F.obj)) =
        SheafOfModules.homObjMap
          (R := X.toRingedSpace.sheaf) (𝟙 G.obj) (formalModuleQuotientπ I (n.unop + 1) F.obj))
    (t : ∀ n : ℕᵒᵖ, formalModuleQuotient I (n.unop + 1) G.obj ⟶
      formalModuleQuotient I (n.unop + 1) F.obj)
    (ht : ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
      t a ≫ (formalCompletionSystem I F.obj).map f =
        (formalCompletionSystem I G.obj).map f ≫ t b)
    (U : X.affineOpens) :
    ∃! s : {s : ∀ n : ℕᵒᵖ,
          (formalModuleQuotient I (n.unop + 1) (SheafOfModules.homObj
            (R := X.toRingedSpace.sheaf) G.obj F.obj)).val.obj (op U.val) //
          ∀ (a b : ℕᵒᵖ) (f : a ⟶ b),
            ((formalCompletionSystem I (SheafOfModules.homObj
              (R := X.toRingedSpace.sheaf) G.obj F.obj)).map f).val.app (op U.val)
              (s a) = s b}, ∀ n : ℕᵒᵖ,
      (e n).val.app (op U.val) (s.val n) =
        ((SheafOfModules.homObjSectionsEquiv (R := X.toRingedSpace.sheaf)
          (formalModuleQuotient I (n.unop + 1) G.obj)
          (formalModuleQuotient I (n.unop + 1) F.obj)).symm (t n)).val (op U.val) := by
  let A := Γ(X, U.val)
  let B := AdicCompletion (I.ideal U) A
  let N := Γ(G.obj, U.val)
  let M := Γ(F.obj, U.val)
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  have hG := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    X G.obj).mp G.property
  have : G.obj.IsQuasicoherent := hG.1
  have : G.obj.IsFiniteType := hG.2
  obtain ⟨ρ, β, hβ, hd⟩ :=
    completion_internal_hom_affine_tensor_dictionary I F G e he U
  have : (G.obj.over U.val).IsFiniteType :=
    Scheme.Modules.isFiniteType_over X G.obj U.val
  have : Module.Finite A N :=
    (((Scheme.Modules.quasicoherent_finite_type_affine.{u, u} X).2 G.obj hG.1).1
      U.val U.property).1.mp inferInstance
  have : Module.FinitePresentation A N := Module.finitePresentation_of_finite A N
  let θ := (Module.FinitePresentation.isBaseChange_map A N M B).equiv
  have hβθ : β = θ.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b h
    calc
      β (TensorProduct.tmul A b h) = β (b • (TensorProduct.tmul A 1 h)) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = b • β (TensorProduct.tmul A 1 h) := β.map_smul b _
      _ = b • LinearMap.baseChangeHom A B N M h := by rw [hβ]
      _ = θ (TensorProduct.tmul A b h) := (IsBaseChange.equiv_tmul _ _ _).symm
  have hbij : Function.Bijective β := by
    rw [hβθ]
    exact θ.bijective
  obtain ⟨v, hv⟩ := hd t ht
  obtain ⟨w, hw⟩ := hbij.2 v
  let s := ρ.symm w
  refine ⟨s, ?_, ?_⟩
  · have hsβ : β (ρ s) = v := by
      simpa [s] using hw
    exact (hv s).2 hsβ
  · intro s' hs'
    have hsβ : β (ρ s) = v := by
      simpa [s] using hw
    have hs'β : β (ρ s') = v := (hv s').1 hs'
    apply ρ.injective
    apply hbij.1
    exact hs'β.trans hsβ.symm

end AlgebraicGeometry
