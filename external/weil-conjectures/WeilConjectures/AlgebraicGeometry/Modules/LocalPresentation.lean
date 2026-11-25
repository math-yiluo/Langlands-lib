/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Local presentations from generators with finitely generated relations

Let `M` be an `𝒪_X`-module and `p : 𝒪_X^{⊕ I} ⟶ M` an epimorphism whose kernel is of finite
type. Then `M` has a global presentation on a neighbourhood of every point, and in particular
`M` is quasi-coherent.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.generatingSectionsRestrictOfOver`: generating sections of
  `M.over U` give generating sections of `M.restrict U.ι`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_presentation_restrict_of_epi`: if `p : free I ⟶ M`
  is an epimorphism with kernel of finite type, every point has an open neighbourhood `W` with a
  presentation of `M.restrict W.ι`.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_epi_free`: such an `M` is
  quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_free`: a free module of finite rank is
  of finite presentation.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Generating sections of `M.over U` give generating sections of `M.restrict U.ι`, transported
along `AlgebraicGeometry.Scheme.Modules.overEquiv`. -/
noncomputable def generatingSectionsRestrictOfOver {M : X.Modules} (U : X.Opens)
    (G : (M.over U).GeneratingSections) : (M.restrict U.ι).GeneratingSections :=
  haveI : PreservesColimitsOfSize.{u, u} (overEquiv U).functor :=
    (overEquiv U).toAdjunction.leftAdjoint_preservesColimits
  (G.map (overEquiv U).functor (overEquivFunctorObjUnitIso U)).ofEpi
    ((overFunctorEquiv U).app M).hom

instance {M : X.Modules} (U : X.Opens) (G : (M.over U).GeneratingSections) [G.IsFiniteType] :
    (generatingSectionsRestrictOfOver U G).IsFiniteType :=
  ⟨inferInstanceAs (Finite G.I)⟩

/-- **Local presentations.** Let `p : 𝒪_X^{⊕ I} ⟶ M` be an epimorphism whose kernel is of finite
type. Then every point `x` has an open neighbourhood `W` such that `M.restrict W.ι` has a
presentation: its generators are the images of the basis of `𝒪_W^{⊕ I}`, and its relations are
local generators of the kernel of `p`. -/
theorem exists_presentation_restrict_of_epi {M : X.Modules} {I : Type u}
    (p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M) [Epi p]
    [SheafOfModules.IsFiniteType.{u} (R := X.ringCatSheaf) (kernel p)] (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ Nonempty (M.restrict W.ι).Presentation := by
  obtain ⟨τ, _⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u}
    (R := X.ringCatSheaf) (kernel p)
  obtain ⟨j, hj⟩ := ((Opens.coversTop_iff _ τ.X).mp τ.coversTop).exists_mem x
  let W : X.Opens := τ.X j
  let σ := generatingSectionsRestrictOfOver W (τ.generators j)
  let F := restrictFunctor W.ι
  let q : SheafOfModules.free I ⟶ M.restrict W.ι := (restrictFreeIso W.ι I).inv ≫ F.map p
  have : Epi (F.map p) := F.map_epi p
  have : Epi q := epi_comp _ _
  let e : restrict (kernel p) W.ι ≅ kernel (SheafOfModules.GeneratingSections.ofEpiFree q).π :=
    PreservesKernel.iso F p ≪≫ (kernelIsIsoComp (restrictFreeIso W.ι I).inv (F.map p)).symm ≪≫
      kernelIsoOfEq (SheafOfModules.GeneratingSections.ofEpiFree_π q).symm
  exact ⟨W, hj, ⟨{ generators := .ofEpiFree q, relations := σ.ofEpi e.hom }⟩⟩

/-- **Quasi-coherence from generators with finitely generated relations.** If
`p : 𝒪_X^{⊕ I} ⟶ M` is an epimorphism whose kernel is of finite type, then `M` is
quasi-coherent. -/
theorem isQuasicoherent_of_epi_free {M : X.Modules} {I : Type u}
    (p : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M) [Epi p]
    [SheafOfModules.IsFiniteType.{u} (R := X.ringCatSheaf) (kernel p)] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M := by
  choose W hW P using exists_presentation_restrict_of_epi p
  exact isQuasicoherent_of_isOpenCover M (U := W)
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hW x⟩) fun x ↦ (P x).some

/-- A free module of finite rank is of finite presentation. -/
theorem isFinitePresentation_free (I : Type u) [Finite I] :
    SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) (SheafOfModules.free I) := by
  let P := SheafOfModules.presentationOfIsCokernelFree (ι := PEmpty.{u + 1})
    (0 : SheafOfModules.free _ ⟶ SheafOfModules.free (R := X.ringCatSheaf) I) (𝟙 _) (by simp)
    (CokernelCofork.IsColimit.ofId _ rfl)
  have : P.IsFinite := ⟨⟨inferInstanceAs (Finite I)⟩, ⟨inferInstanceAs (Finite PEmpty)⟩⟩
  exact P.isFinitePresentation

end AlgebraicGeometry.Scheme.Modules
