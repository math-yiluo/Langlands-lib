import Langlands.Automorphic.BlockShapePositiveEnveloping
import Langlands.Automorphic.BlockShapeComplexLieCoordinates
import Langlands.Representation.Archimedean.BlockEnvelopingCenterFiniteness

/-! # A common infinitesimal centre bound for the block Levi slices -/

noncomputable section

universe u v w x y

open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open NumberField Langlands.Algebra Langlands.Archimedean.Kostant Langlands.GeneralLinear
  Langlands.Global Langlands.Global.ArchimedeanGL

section Algebra

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
  {U : Type w} [Ring U] [Algebra k U]
  {V : Type x} [AddCommGroup V] [Module k V] {W : Type y} [AddCommGroup W] [Module k W]

private def relativeCenterOrbitMap (j : A →ₐ[k] U) (ρ : U →ₐ[k] Module.End k V)
    (s : V →ₗ[k] W) (v : V) : Subalgebra.center k A →ₗ[k] W :=
  s ∘ₗ (LinearMap.applyₗ (R := k) v) ∘ₗ ρ.toLinearMap ∘ₗ j.toLinearMap ∘ₗ
    (Subalgebra.center k A).val.toLinearMap

private theorem relativeCenterOrbitMap_finite (j : A →ₐ[k] U) (D : RelativeEnvelopingDecomposition j)
    (ρ : U →ₐ[k] Module.End k V) (s : V →ₗ[k] W) (v : V)
    (hkill : ∀ u ∈ D.ideal, ∀ f, s (ρ u f) = 0)
    (hfin : letI := D.centerProjection.toRingHom.toAlgebra
            Module.Finite (Subalgebra.center k U) (Subalgebra.center k A))
    (hv : Module.Finite k (Submodule.span k (Set.range fun z : Subalgebra.center k U => ρ z.val v))) :
    Module.Finite k (LinearMap.range (relativeCenterOrbitMap j ρ s v)) := by
  let Z := Subalgebra.center k U
  let C := Subalgebra.center k A
  let : Algebra Z C := D.centerProjection.toRingHom.toAlgebra
  let ψ := relativeCenterOrbitMap j ρ s v
  let V₀ : Submodule k V := Submodule.span k (Set.range fun z : Z => ρ z.val v)
  have : Module.Finite k V₀ := hv
  obtain ⟨t, ht⟩ := hfin.1
  let W₀ : Submodule k W := ⨆ a : t, V₀.map (s.comp (ρ (j a.val.val)))
  have : Module.Finite k W₀ := by
    rw [show W₀ = ⨆ a : t, V₀.map (s.comp (ρ (j a.val.val))) from rfl]
    exact Submodule.finite_iSup _
  have heq (z : Z) (a : C) : ψ (z • a) = s (ρ (j a.val) (ρ z.val v)) := by
    let c := D.centerProjection z
    change s (ρ (j (c.val * a.val)) v) = s (ρ (j a.val) (ρ z.val v))
    rw [← Module.End.mul_apply, ← map_mul]
    apply sub_eq_zero.mp
    rw [← map_sub, ← LinearMap.sub_apply, ← map_sub]
    have hc : c.val * a.val = a.val * c.val := congrArg Subtype.val (mul_comm c a)
    rw [hc, map_mul, show j a.val * j c.val - j a.val * z.val = -(j a.val * (z.val - j c.val)) by
      rw [mul_sub, neg_sub]]
    exact hkill _ (D.ideal.neg_mem (D.levi_mul_mem a.val _ (D.sub_centerProjection_mem z))) v
  have hmem (a : C) (ha : a ∈ Submodule.span Z (t : Set C)) : ∀ z : Z, ψ (z • a) ∈ W₀ := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
      intro z
      rw [heq]
      exact Submodule.mem_iSup_of_mem (⟨a, ha⟩ : t)
        (Submodule.mem_map_of_mem (Submodule.subset_span ⟨z, rfl⟩))
    | zero =>
      intro z
      rw [smul_zero, map_zero]
      exact W₀.zero_mem
    | add a b _ _ ha hb =>
      intro z
      rw [smul_add, map_add]
      exact W₀.add_mem (ha z) (hb z)
    | smul z a _ ha =>
      intro z'
      rw [smul_smul]
      exact ha (z' * z)
  apply Submodule.finiteDimensional_of_le (S₂ := W₀)
  rintro _ ⟨a, rfl⟩
  have ha := hmem a (by rw [ht]; exact Submodule.mem_top) 1
  simpa only [one_smul] using ha

end Algebra

section MatrixLevi

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

local instance leviSliceCenterRationalAddCommGroup (d : ℕ) : AddCommGroup (RationalInvariantFunctions F d) :=
  Submodule.addCommGroup _
local instance leviSliceCenterContinuousAddCommGroup (d : ℕ) : AddCommGroup (ContinuousRationalFunctions F d) :=
  Submodule.addCommGroup _
local instance leviSliceCenterFiniteSmoothAddCommGroup (d : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F d) :=
  Submodule.addCommGroup _

local notation "Λ" => ComplexLieMatrixPlace F
local notation "Levi" => AdelicBlockParabolic.FullLevi F B
local notation "W" => (AdelicBlockParabolic.FullLevi F B → ℂ)
local notation "Zg" => Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ (fun _ : Λ => n)))
local notation "Zm" => Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ (GLProd ℂ (blockRanks B Λ)))
local notation "J" => LieEnvelopingEquiv.map (AlgHom.toLieHom (blockMatrixInclusion B (ι := Λ)))
local notation "A" => finiteSmoothMatrixEnvelopingAction F (n := n)

/-- Restrict the full Levi enveloping-centre orbit to functions on the Levi. -/
def blockLeviCenterOrbitMap (f : FiniteSmoothRationalFunctions F n) : Zm →ₗ[ℂ] W :=
  relativeCenterOrbitMap J A (blockLeviTermRestriction F B) f

/-- The full Levi orbit has finite complex dimension for an ambient centre-finite function. -/
theorem blockLeviCenterOrbitMap_finite (f : FiniteSmoothRationalFunctions F n)
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) :
    Module.Finite ℂ (LinearMap.range (blockLeviCenterOrbitMap F B f)) := by
  let D := blockEnvelopingDecomposition B (ι := Λ)
  refine relativeCenterOrbitMap_finite J D A (blockLeviTermRestriction F B) f ?_
    (blockCenter_moduleFinite B (ι := Λ)) ?_
  · intro u hu x
    change u ∈ (blockEnvelopingDecomposition B (ι := Λ)).ideal at hu
    rw [blockEnvelopingDecomposition_ideal] at hu
    exact blockLeviTermRestriction_positiveIdeal_eq_zero F B x hu
  · let T := LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F n)
    let E := LieEnvelopingEquiv.center T
    have hr : Set.range (fun z : Zg => A z.val f) =
        Set.range (fun z : EnvelopingCenter F n => finiteSmoothCenterRepresentation F n z f) := by
      ext u
      constructor
      · rintro ⟨z, rfl⟩
        refine ⟨E.symm z, ?_⟩
        change finiteSmoothEnvelopingAction F n (E.symm z).val f =
          finiteSmoothEnvelopingAction F n (T.symm z.val) f
        have hz : (E.symm z).val = T.symm z.val := by
          apply T.injective
          rw [← LieEnvelopingEquiv.center_apply, show (LieEnvelopingEquiv.center T) (E.symm z) = z from
            E.apply_symm_apply z, AlgEquiv.apply_symm_apply]
        rw [hz]
      · rintro ⟨z, rfl⟩
        refine ⟨E z, ?_⟩
        change finiteSmoothEnvelopingAction F n
          ((LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F n)).symm (E z).val) f = _
        rw [LieEnvelopingEquiv.center_apply, AlgEquiv.symm_apply_apply]
        rfl
    rw [hr]
    exact (isCenterFinite_iff_finiteSmoothCenterVector F n f).mp hf

variable (i : Fin B.length)

/-- Include the actual centre of one block into the matrix Levi enveloping centre. -/
def singleBlockCenterToMatrixLevi : EnvelopingCenter F (B.size i) →ₐ[ℂ] Zm :=
  (blockMatrixFactorCenterInclusion B i Λ).comp
    (LieEnvelopingEquiv.center
      (LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F (B.size i)))).toAlgHom

/-- The common orbit map on the entire Levi evaluates a single block's enveloping centre. -/
def blockShapeLeviSliceCenterOrbitMap (f : FiniteSmoothRationalFunctions F n) :
    EnvelopingCenter F (B.size i) →ₗ[ℂ] W :=
  (blockLeviCenterOrbitMap F B f).comp (singleBlockCenterToMatrixLevi F B i).toLinearMap

private theorem blockShapeLeviSliceCenterOrbitMap_apply (f : FiniteSmoothRationalFunctions F n)
    (z : EnvelopingCenter F (B.size i)) (m : Levi) :
    blockShapeLeviSliceCenterOrbitMap F B i f z m =
      blockShapeLeviSlice F B (finiteSmoothEnvelopingAction F n
        (blockShapeEnvelopingInclusion F B i z.val) f) 1 m := by
  let E := LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F n)
  let E' := LieEnvelopingEquiv.enveloping (complexLieProductMatrixCoordinates F (B.size i))
  let K := LieEnvelopingEquiv.map (blockMatrixFactorInclusion B i Λ)
  have h : E (blockShapeEnvelopingInclusion F B i z.val) = J (K (E' z.val)) :=
    DFunLike.congr_fun (enveloping_complexLieMatrixCoordinates_blockShapeInclusion B i F) z.val
  change (blockLeviTermRestriction F B) (finiteSmoothEnvelopingAction F n
    (E.symm (J (K (E' z.val)))) f) m = _
  rw [← h, AlgEquiv.symm_apply_apply]
  rfl

theorem blockShapeLeviSliceCenterOrbitMap_update (f : FiniteSmoothRationalFunctions F n)
    (z : EnvelopingCenter F (B.size i)) (m : Levi) (x : AdelicGL F (B.size i)) :
    blockShapeLeviSliceCenterOrbitMap F B i f z (Function.update m i x) =
      ContinuousRationalFunctions.evaluate F (B.size i)
        (finiteSmoothCenterAction F (B.size i) z (blockShapeLeviSliceFactorLinearMap F B i m f)).val x := by
  rw [blockShapeLeviSliceCenterOrbitMap_apply]
  exact congrArg (fun h : FiniteSmoothRationalFunctions F (B.size i) =>
    ContinuousRationalFunctions.evaluate F (B.size i) h.val x)
    (blockShapeLeviSliceFactor_enveloping F B i m z.val f)

private theorem blockShapeLeviSliceCenterOrbitMap_eq_zero_iff (f : FiniteSmoothRationalFunctions F n)
    (z : EnvelopingCenter F (B.size i)) :
    blockShapeLeviSliceCenterOrbitMap F B i f z = 0 ↔
      ∀ m : Levi, finiteSmoothCenterAction F (B.size i) z
        (blockShapeLeviSliceFactorLinearMap F B i m f) = 0 := by
  constructor
  · intro hz m
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change ContinuousRationalFunctions.evaluate F (B.size i)
      (finiteSmoothCenterAction F (B.size i) z (blockShapeLeviSliceFactorLinearMap F B i m f)).val x = 0
    rw [← blockShapeLeviSliceCenterOrbitMap_update, hz, Pi.zero_apply]
  · intro hz
    funext m
    have he := blockShapeLeviSliceCenterOrbitMap_update F B i f z m (m i)
    rw [Function.update_eq_self, hz m] at he
    exact he

/-- The common ideal killing every single-block section of the original Levi slice. -/
def blockShapeLeviSliceCenterAnnihilator (f : FiniteSmoothRationalFunctions F n) :
    Ideal (EnvelopingCenter F (B.size i)) where
  carrier := {z | blockShapeLeviSliceCenterOrbitMap F B i f z = 0}
  zero_mem' := map_zero _
  add_mem' := by simp only [Set.mem_ofPred_eq, map_add]; intro z w hz hw; rw [hz, hw, add_zero]
  smul_mem' a z hz := by
    apply (blockShapeLeviSliceCenterOrbitMap_eq_zero_iff F B i f (a * z)).2
    intro m
    rw [map_mul, Module.End.mul_apply, (blockShapeLeviSliceCenterOrbitMap_eq_zero_iff F B i f z).1 hz m,
      map_zero]

theorem blockShapeLeviSliceCenterAnnihilator_kills (f : FiniteSmoothRationalFunctions F n)
    {z : EnvelopingCenter F (B.size i)} (hz : z ∈ blockShapeLeviSliceCenterAnnihilator F B i f)
    (m : Levi) : finiteSmoothCenterAction F (B.size i) z
      (blockShapeLeviSliceFactorLinearMap F B i m f) = 0 :=
  (blockShapeLeviSliceCenterOrbitMap_eq_zero_iff F B i f z).1 hz m

/-- The one common annihilator has finite complex codimension. -/
theorem blockShapeLeviSliceCenterAnnihilator_finiteQuotient (f : FiniteSmoothRationalFunctions F n)
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) :
    Module.Finite ℂ (EnvelopingCenter F (B.size i) ⧸
      (blockShapeLeviSliceCenterAnnihilator F B i f).restrictScalars ℂ) := by
  let ψ := blockShapeLeviSliceCenterOrbitMap F B i f
  change Module.Finite ℂ (EnvelopingCenter F (B.size i) ⧸ LinearMap.ker ψ)
  apply (Module.Finite.equiv_iff ψ.quotKerEquivRange).2
  have : Module.Finite ℂ (LinearMap.range (blockLeviCenterOrbitMap F B f)) :=
    blockLeviCenterOrbitMap_finite F B f hf
  exact Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)

/-- Every individual Levi block section satisfies the actual simultaneous centre condition. -/
theorem blockShapeLeviSliceFactor_isCenterFinite (f : FiniteSmoothRationalFunctions F n)
    (hf : IsCenterFinite F n (finiteSmoothInclusion F n f)) (m : Levi) :
    IsCenterFinite F (B.size i) (finiteSmoothInclusion F (B.size i)
      (blockShapeLeviSliceFactorLinearMap F B i m f)) := by
  refine (isCenterFinite_iff_exists_ideal F (B.size i) _).2
    ⟨blockShapeLeviSliceCenterAnnihilator F B i f,
      blockShapeLeviSliceCenterAnnihilator_finiteQuotient F B i f hf, ?_⟩
  intro z hz b
  change centerAction F (B.size i) z
    (finiteSmoothSlice F (B.size i) b (blockShapeLeviSliceFactorLinearMap F B i m f)) = 0
  rw [← finiteSmoothSlice_centerAction, blockShapeLeviSliceCenterAnnihilator_kills F B i f hz m, map_zero]

end MatrixLevi

end Langlands.Automorphic
