import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Twist
import Langlands.AlgebraicGeometry.Modules.CoherentGraphSupport

/-! # Smaller support for multiplication by an ample section -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}}

/-- Tensoring a map that becomes invertible on an open remains invertible there. -/
lemma isIso_restrict_tensorMap {M M' N N' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') (U : X.Opens)
    (ha : IsIso ((Scheme.Modules.restrictFunctor U.ι).map a))
    (hb : IsIso ((Scheme.Modules.restrictFunctor U.ι).map b)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (tensorMap a b)) := by
  let P := Scheme.Modules.pullback U.ι
  have : IsIso (P.map a) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) a).mp ha
  have : IsIso (P.map b) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) b).mp hb
  have := pullbackTensorComparisonIsIso U.ι
  have hc (A B : X.Modules) : IsIso (pullbackTensorComparisonApp U.ι A B) :=
    inferInstanceAs (IsIso ((pullbackTensorComparison U.ι).app (A, B)))
  have hp : IsIso (CategoryTheory.Prod.mkHom (P.map a) (P.map b)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  have ht : IsIso (tensorMap (P.map a) (P.map b)) :=
    inferInstanceAs (IsIso ((tensorFunctor U.toScheme).map
      (CategoryTheory.Prod.mkHom (P.map a) (P.map b))))
  have h : IsIso (P.map (tensorMap a b)) := by
    apply (isIso_comp_right_iff _ (pullbackTensorComparisonApp U.ι M' N')).mp
    rw [pullbackTensorComparisonApp_naturality]
    infer_instance
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι)
    (tensorMap a b)).mpr h

/-- Multiplication by a section is invertible on its trivialization open. -/
lemma isIso_restrict_twistMul (N : X.Modules) (s : GlobalSections N) (G : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor (trivializationOpen N s).ι).map
      (twistMul N s G)) := by
  have := isIso_restrict_tensorMap (𝟙 G) (sectionHom N s) (trivializationOpen N s)
    (by infer_instance) (trivializesOn_trivializationOpen N s)
  unfold twistMul
  rw [Functor.map_comp]
  infer_instance

/-- Both error modules of section multiplication have the smaller support bound. -/
def SectionErrorsLT (N : X.Modules) (s : GlobalSections N) (G : X.Modules)
    (e : ℕ) : Prop :=
  HasSupportDimensionLT (kernel (twistMul N s G)) e ∧
    HasSupportDimensionLT (cokernel (twistMul N s G)) e

/-- Meeting an irreducible support drops the height bound of both errors. -/
lemma sectionErrorsLT (N : X.Modules) (hN : IsLocallyFreeRankOne N)
    (s : GlobalSections N) (G : X.Modules)
    (T : IrreducibleCloseds X) (e : ℕ) (hT : height T ≤ e)
    (hGT : QuasicoherentLocal.VanishesOn G
      ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩)
    (hs : ((T : Set X) ∩ trivializationOpen N s).Nonempty) :
    SectionErrorsLT N s G e := by
  have hGN : QuasicoherentLocal.VanishesOn (tensorObj G N)
      ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩ := by
    apply QuasicoherentLocal.VanishesOn.of_stalkSupport_subset_compl
    rw [stalkSupport_tensor_lineBundle G N hN]
    exact hGT.stalkSupport_subset_compl
  exact ⟨.kernel_of_irreducible_isIso _ T hT _ hs hGT
      (isIso_restrict_twistMul N s G),
    .cokernel_of_irreducible_isIso _ T hT _ hs hGN
      (isIso_restrict_twistMul N s G)⟩

/-- Ampleness supplies a positive power section with affine locus and smaller errors. -/
theorem exists_ampleSection_errorsLT (L : LineBundle X) (hL : L.IsAmple)
    (G : X.Modules) (T : IrreducibleCloseds X) (e : ℕ) (hT : height T ≤ e)
    (hGT : QuasicoherentLocal.VanishesOn G
      ⟨(T : Set X)ᶜ, T.isClosed.isOpen_compl⟩) :
    ∃ d : ℕ, 0 < d ∧ ∃ s : GlobalSections (tensorPow L.obj d),
      IsAffineOpen (trivializationOpen (tensorPow L.obj d) s) ∧
        SectionErrorsLT (tensorPow L.obj d) s G e := by
  obtain ⟨x, hx⟩ := T.isIrreducible.nonempty
  obtain ⟨d, hd, s, hs, hsa⟩ := hL.exists_section x
  exact ⟨d, hd, s, hsa, sectionErrorsLT _ (tensorPow_isLocallyFreeRankOne X L d) s G T e hT
    hGT ⟨x, hx, hs⟩⟩

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
