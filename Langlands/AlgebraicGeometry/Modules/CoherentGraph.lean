import Langlands.AlgebraicGeometry.Modules.CoherentLineBundle
import Langlands.AlgebraicGeometry.Modules.SupportDimension
import Langlands.AlgebraicGeometry.Modules.OpenCohomologyVanishing
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-! # Coherent graphs of isomorphisms on affine opens -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Order

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

namespace QuasicoherentLocal.VanishesOn

variable {M N : X.Modules} {O : X.Opens}

/-- Excluding an open from stalk support implies vanishing on that open. -/
lemma of_stalkSupport_subset_compl (h : stalkSupport M ⊆ (O : Set X)ᶜ) :
    QuasicoherentLocal.VanishesOn M O := by
  apply of_isZero_restrict
  apply isZero_iff_forall_isZero_stalk.2
  intro x
  have hzero : IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val).obj
      M.presheaf) := by
    by_contra hn
    exact h hn x.property
  exact hzero.of_iso ((Scheme.Modules.restrictStalkNatIso O.ι x).app M)

/-- Vanishing passes to submodules. -/
lemma of_mono (φ : M ⟶ N) [Mono φ] (h : QuasicoherentLocal.VanishesOn N O) :
    QuasicoherentLocal.VanishesOn M O := by
  apply of_isZero_restrict
  exact IsZero.of_mono ((Scheme.Modules.restrictFunctor O.ι).map φ) h.isZero_restrict

/-- A binary direct sum vanishes wherever both its summands do. -/
lemma biprod (hM : QuasicoherentLocal.VanishesOn M O)
    (hN : QuasicoherentLocal.VanishesOn N O) :
    QuasicoherentLocal.VanishesOn (M ⊞ N) O := by
  apply of_isZero_restrict
  let F := Scheme.Modules.restrictFunctor O.ι
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  exact ((biprod_isZero_iff _ _).2 ⟨hM.isZero_restrict, hN.isZero_restrict⟩).of_iso
    (F.mapBiprod M N)

/-- A map that is an isomorphism on an open has zero kernel there. -/
lemma kernel_of_isIso (φ : M ⟶ N)
    (h : IsIso ((Scheme.Modules.restrictFunctor O.ι).map φ)) :
    QuasicoherentLocal.VanishesOn (Limits.kernel φ) O := by
  apply of_isZero_restrict
  exact (isZero_kernel_of_mono _).of_iso
    (PreservesKernel.iso (Scheme.Modules.restrictFunctor O.ι) φ)

end QuasicoherentLocal.VanishesOn

open Langlands.Scheme.Modules QuasicoherentLocal

/-- Tensoring with a line bundle preserves the actual stalk support. -/
lemma stalkSupport_tensor_lineBundle (M N : X.Modules) (hN : Picard.IsLocallyFreeRankOne N) :
    stalkSupport (tensorObj M N) = stalkSupport M := by
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hN x
  let y : U.toScheme := ⟨x, hxU⟩
  let F := Scheme.Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
  let i : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj (tensorObj M N).presheaf ≅
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M.presheaf :=
    ((Scheme.Modules.restrictStalkNatIso U.ι y).app (tensorObj M N)).symm ≪≫
      F.mapIso (tensorRestrictionTrivialization M N U e) ≪≫
        (Scheme.Modules.restrictStalkNatIso U.ι y).app M
  exact not_congr i.isZero_iff

/-- A line-bundle tensor preserves any given closed support bound. -/
lemma HasSupportDimensionLT.tensor_lineBundle {M N : X.Modules} {e : ℕ}
    (hM : HasSupportDimensionLT M e) (hN : Picard.IsLocallyFreeRankOne N) :
    HasSupportDimensionLT (tensorObj M N) e := by
  obtain ⟨Z, hMZ, hZ⟩ := hM
  refine ⟨Z, VanishesOn.of_stalkSupport_subset_compl ?_, hZ⟩
  rw [stalkSupport_tensor_lineBundle M N hN]
  exact hMZ.stalkSupport_subset_compl

/-- A coherent pullback is a kernel inside the binary direct sum. -/
lemma QuasicoherentLocal.isQuasicoherent_pullback {M N J : X.Modules}
    (a : M ⟶ J) (b : N ⟶ J) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [J.IsQuasicoherent] : (pullback a b).IsQuasicoherent := by
  have := isQuasicoherent_biprod M N
  have := isQuasicoherent_kernel (biprod.desc a (-b))
  let e : pullback a b ≅ kernel (biprod.desc a (-b)) :=
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct a b).conePointUniqueUpToIso
      (limit.isLimit _)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm this

/-- The pullback of two modules with finite affine sections is finite on affine opens
on a locally noetherian scheme; the common target need not be finite. -/
lemma HasFiniteAffineSections.pullback [IsLocallyNoetherian X] {M N J : X.Modules}
    (a : M ⟶ J) (b : N ⟶ J) (hM : HasFiniteAffineSections M)
    (hN : HasFiniteAffineSections N) : HasFiniteAffineSections (pullback a b) := by
  have : Mono (Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct a b) :=
    Fork.IsLimit.mono (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct a b)
  exact (hM.biprod hN).of_mono (Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct a b)

namespace CoherentGraph

variable (M N : X.Modules) (U : X.Opens)
    (e : N.restrict U.ι ≅ M.restrict U.ι)

/-- Extend the local identification into the pushforward of the first restriction. -/
abbrev comparisonMap : N ⟶ (Scheme.Modules.pushforward U.ι).obj (M.restrict U.ι) :=
  unitMap U.ι N ≫ (Scheme.Modules.pushforward U.ι).map e.hom

/-- The actual pullback graph of an isomorphism on an open. -/
abbrev graph : X.Modules := pullback (unitMap U.ι M) (comparisonMap M N U e)

/-- The graph projects to its first module. -/
abbrev fst : graph M N U e ⟶ M := pullback.fst _ _

/-- The graph projects to its second module. -/
abbrev snd : graph M N U e ⟶ N := pullback.snd _ _

lemma isIso_restrict_comparisonMap :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (comparisonMap M N U e)) := by
  have := isIso_restrict_unitMap U.ι N (Scheme.Opens.opensRange_ι U).ge
  dsimp [comparisonMap]
  rw [Functor.map_comp]
  infer_instance

lemma isIso_restrict_fst :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (fst M N U e)) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  have := isIso_restrict_comparisonMap M N U e
  rw [← pullbackComparison_comp_fst F]
  infer_instance

lemma isIso_restrict_snd :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (snd M N U e)) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  have := isIso_restrict_unitMap U.ι M (Scheme.Opens.opensRange_ι U).ge
  rw [← pullbackComparison_comp_snd F]
  infer_instance

end CoherentGraph

end Langlands.AlgebraicGeometry.Modules
