import Langlands.GroupScheme.Torus.ExponentCharacters
import Langlands.GroupScheme.Torus.WeightBaseChange
import Langlands.GroupScheme.Lie.SmoothScalarExtension
import Mathlib.LinearAlgebra.TensorProduct.Decomposition

/-! # Arbitrary base change of actual relative adjoint weight modules -/

noncomputable section

universe u

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

variable {r K : Type u} [CommRing r] [CommRing K] [Algebra r K]
  (G : GroupScheme (Spec (CommRingCat.of r))) [IsAffineHom G.X.hom]
  [Smooth G.X.hom]

local notation "b" => algebraBaseMap r K
local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap r K)) G

local instance smooth_baseChange : Smooth (G_K).X.hom :=
  inferInstanceAs (Smooth (pullback.snd G.X.hom b))

local instance affine_baseChange : IsAffineHom (G_K).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace Lie

attribute [local instance] coordinateOriginAlgebra

/-- Arbitrary scalar extension into the actual Lie module of the scheme pullback. -/
def smoothSchemeScalarExtension :
    K ⊗[r] Additive (lieKernel G r) ≃ₗ[K] Additive (lieKernel G_K K) :=
  (smoothKernelScalarExtension G K).trans (kernelBaseChangeLinearEquiv r K G K).symm

theorem smoothSchemeScalarExtension_tmul (a : K) (X : Additive (lieKernel G r)) :
    smoothSchemeScalarExtension (K := K) G (a ⊗ₜ X) =
      a • (kernelBaseChangeLinearEquiv r K G K).symm
        (lieKernelMapLinear G (Algebra.ofId r K) X) := by
  change (kernelBaseChangeLinearEquiv r K G K).symm
    (smoothKernelScalarExtension G K (a ⊗ₜ X)) = _
  have h := smoothKernelScalarExtension_tmul (R := CommRingCat.of r) G K a X
  exact (congrArg (kernelBaseChangeLinearEquiv r K G K).symm h).trans
    ((kernelBaseChangeLinearEquiv r K G K).symm.map_smul a _)

variable {A B : Type u} [CommRing A] [Algebra r A] [CommRing B] [Algebra r B]

omit [Smooth G.X.hom] in
/-- Two successive coefficient inclusions agree with the direct inclusion. -/
theorem smooth_lieKernelMapLinear_base (f : A →ₐ[r] B) (X : Additive (lieKernel G r)) :
    lieKernelMapLinear G f (lieKernelMapLinear G (Algebra.ofId r A) X) =
      lieKernelMapLinear G (Algebra.ofId r B) X := by
  apply (kernelDerivationLinearEquiv G).injective
  apply Derivation.ext
  intro c
  change kernelDerivationEquiv G
      (lieKernelMap G f (lieKernelMap G (Algebra.ofId r A) X.toMul)) c =
    kernelDerivationEquiv G (lieKernelMap G (Algebra.ofId r B) X.toMul) c
  rw [kernelDerivationEquiv_naturality, kernelDerivationEquiv_naturality,
    kernelDerivationEquiv_naturality]
  exact f.commutes _

variable [Algebra K A] [IsScalarTower r K A]

/-- A pure extended vector has the prescribed actual image over every test algebra. -/
theorem smoothSchemeScalarExtension_base_naturality (X : Additive (lieKernel G r)) :
    kernelBaseChangeLinearEquiv r K G A
        (lieKernelMapLinear G_K (Algebra.ofId K A)
          (smoothSchemeScalarExtension (K := K) G (1 ⊗ₜ X))) =
      lieKernelMapLinear G (Algebra.ofId r A) X := by
  rw [kernelBaseChangeLinearEquiv_naturality, smoothSchemeScalarExtension_tmul,
    one_smul, LinearEquiv.apply_symm_apply, smooth_lieKernelMapLinear_base]

end Lie

/-- Scalar extension preserves each actual character weight vector for
smooth affine groups over arbitrary base rings. -/
theorem smooth_weightSpace_baseChange_mem
    {T : CommGroupScheme (Spec (CommRingCat.of r))}
    (i : T.toGrp ⟶ G) (χ : characterLattice T)
    {X : Additive (lieKernel G r)} (hX : X ∈ weightSpace i χ) :
    Lie.smoothSchemeScalarExtension (K := K) G (1 ⊗ₜ X) ∈
      weightSpace ((baseChange b).map i) (characterLattice.baseChange b T χ) := by
  rw [mem_weightSpace]
  intro A _ _ t
  let : Algebra r A := ((algebraMap K A).comp (algebraMap r K)).toAlgebra
  let : IsScalarTower r K A := IsScalarTower.of_algebraMap_eq' rfl
  apply (Lie.kernelBaseChangeLinearEquiv r K G A).injective
  rw [Lie.kernelBaseChangeLinearEquiv_adjoint,
    Lie.smoothSchemeScalarExtension_base_naturality, LinearEquiv.map_smul,
    Lie.smoothSchemeScalarExtension_base_naturality, Lie.characterValue_baseChange,
    Lie.affineBaseChangeEquiv_target]
  exact hX A (Lie.affineBaseChangeEquiv r K T.toGrp A t)

namespace splitTorus

variable (I : Type u) [Fintype I] [DecidableEq I]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

/-- The actual torus homomorphism after base change, using the canonical
coordinate split torus on the new base. -/
def baseChangeHom : splitTorus (Spec (CommRingCat.of K)) I ⟶ G_K :=
  (baseChangeIso b I).inv ≫ (baseChange b).map i

omit [DecidableEq I] in
/-- A pure extended exponent weight vector lies in the same exponent
weight space of the actual scheme pullback. -/
theorem exponentWeightSpace_baseChange_mem (m : I → ℤ)
    {X : Additive (lieKernel G r)} (hX : X ∈ exponentWeightSpace I G i m) :
    Lie.smoothSchemeScalarExtension (K := K) G (1 ⊗ₜ X) ∈
      exponentWeightSpace I G_K (baseChangeHom (K := K) G I i) m := by
  rw [exponentWeightSpace_eq_weightSpace_exponentCharacter I G i m] at hX
  rw [exponentWeightSpace_eq_weightSpace_exponentCharacter I G_K
    (baseChangeHom (K := K) G I i) m]
  have h := smooth_weightSpace_baseChange_mem (K := K)
    (T := commGroupScheme (Spec (CommRingCat.of r)) I) G i
    (exponentCharacter (Spec (CommRingCat.of r)) I m) hX
  have he := weightSpace_comapIso
    (T := (CommGroupScheme.baseChange b).obj
      (commGroupScheme (Spec (CommRingCat.of r)) I))
    (T' := commGroupScheme (Spec (CommRingCat.of K)) I)
    (baseChangeIso b I) ((baseChange b).map i)
    (exponentCharacter (Spec (CommRingCat.of K)) I m)
  change weightSpace ((baseChange b).map i)
      ((commBaseChangeIso b I).hom ≫
        exponentCharacter (Spec (CommRingCat.of K)) I m) =
    weightSpace (baseChangeHom (K := K) G I i)
      (exponentCharacter (Spec (CommRingCat.of K)) I m) at he
  rw [exponentCharacter_baseChange (Spec (CommRingCat.of r)) I b m] at he
  rwa [he] at h

/-- The image of an extended actual exponent weight submodule is exactly
the corresponding actual exponent weight space after scheme base change. -/
theorem map_exponentWeightSpace_baseChange (m : I → ℤ) :
    ((exponentWeightSpace I G i m).baseChange K).map
        (Lie.smoothSchemeScalarExtension (K := K) G).toLinearMap =
      exponentWeightSpace I G_K (baseChangeHom (K := K) G I i) m := by
  classical
  let E := Lie.smoothSchemeScalarExtension (K := K) G
  let W := exponentWeightSpace I G i
  let W' := exponentWeightSpace I G_K (baseChangeHom (K := K) G I i)
  have hle (n : I → ℤ) : ((W n).baseChange K).map E.toLinearMap ≤ W' n := by
    rw [Submodule.map_le_iff_le_comap, Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨X, hX, rfl⟩
    exact exponentWeightSpace_baseChange_mem G I i n hX
  have hsum : (⨆ n, ((W n).baseChange K).map E.toLinearMap) = ⊤ := by
    have hb : DirectSum.IsInternal (fun n => (W n).baseChange K) :=
      DirectSum.IsInternal.baseChange W (isInternal_exponentWeightSpace I G i)
    rw [← Submodule.map_iSup, hb.submodule_iSup_eq_top,
      Submodule.map_top, LinearEquiv.range]
  have hfamily : (fun n => ((W n).baseChange K).map E.toLinearMap) = W' :=
    ((isInternal_exponentWeightSpace I G_K
      (baseChangeHom (K := K) G I i)).submodule_iSupIndep.le_iff_eq_of_iSup_eq_top hsum).mp hle
  exact congrFun hfamily m

/-- Scalar extension of an actual exponent weight summand is canonically
the actual exponent weight summand in the scheme pullback. -/
def exponentWeightBaseChangeEquiv (m : I → ℤ) :
    K ⊗[r] exponentWeightSpace I G i m ≃ₗ[K]
      exponentWeightSpace I G_K (baseChangeHom (K := K) G I i) m :=
  (LinearEquiv.ofBijective ((exponentWeightSpace I G i m).toBaseChange K)
    (DirectSum.IsInternal.toBaseChange_bijective (S := K)
      (exponentWeightSpace I G i) (isInternal_exponentWeightSpace I G i) m)).trans
    ((Submodule.equivMapOfInjective
      (Lie.smoothSchemeScalarExtension (K := K) G).toLinearMap
      (Lie.smoothSchemeScalarExtension (K := K) G).injective
      ((exponentWeightSpace I G i m).baseChange K)).trans
        (LinearEquiv.ofEq _ _ (map_exponentWeightSpace_baseChange G I i m)))

@[simp]
theorem exponentWeightBaseChangeEquiv_tmul (m : I → ℤ)
    (a : K) (X : exponentWeightSpace I G i m) :
    (exponentWeightBaseChangeEquiv (K := K) G I i m (a ⊗ₜ X) :
      Additive (lieKernel G_K K)) =
      Lie.smoothSchemeScalarExtension (K := K) G
        (a ⊗ₜ (X : Additive (lieKernel G r))) := by
  simp only [exponentWeightBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, Submodule.coe_equivMapOfInjective_apply,
    LinearEquiv.ofBijective_apply, Submodule.coe_toBaseChange_tmul]
  rfl

end splitTorus

end Langlands.GroupScheme
