/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.ClosedImmersionCoherentEquivalenceCompletion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Reflection of zero for supported coherent submodules

Source: Stacks Project, Tags 087T, 0880 and 088A.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Completion on a closed thickening detects a zero coherent submodule of a
module annihilated by the thickening's defining ideal.
Source: Stacks Project, Tag 088A, second application of Remark 0888, using
Tag 087T and the natural completion comparison (equation 0880).
(blueprint: lem-weil-pbc-supported-coherent-completion-reflects-zero).

Proof:
1. The inclusion H to F is monic, so K^q annihilates H: ideal multiplication
commutes with this inclusion, and multiplication on F is zero. The affine
ideal-power formula identifies this annihilation with annihilation by the
ideal sheaf defining Z = V(K^q).
2. The coherent closed-pushforward equivalence of Tag 087T descends H to a
coherent module H_Z on Z, with pushforward isomorphic to H. The natural
completion comparison identifies the pushforward of the I O_Z completion
of H_Z with the I completion of H.
3. Every component of the latter is zero by hypothesis. Closed pushforward
is fully faithful and reflects zero, so every component of the former is
zero. A diagram with zero components is zero, and the full inclusion of
coherent formal modules reflects zero. Thus completion(H_Z) is zero.
4. Install the Noetherian instance on Z induced by its closed immersion.
The assumed completion equivalence for this instance reflects zero, so
H_Z is zero. Pushforward preserves zero; its comparison with H proves H
zero. No local faithfulness of completion is assumed. The argument also
covers the empty thickening and the zero module.
-/
theorem supportedCoherent_completion_reflects_zero
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (q : ℕ) (_hq : 1 ≤ q)
    (hcompletion : ∀ (hZ : IsNoetherian (K ^ q).subscheme),
      Functor.IsEquivalence
        (@completion ((K ^ q).subscheme) hZ (I.comap (K ^ q).subschemeι)))
    (F H : CoherentModules X) (j : H.obj ⟶ F.obj) [Mono j]
    (hF : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι q).2 F.obj))
    (hH : ∀ n : ℕ, IsZero (formalModuleQuotient I (n + 1) H.obj)) :
    IsZero H.obj  := by
  classical
  let Z := (K ^ q).subscheme
  let i : Z ⟶ X := (K ^ q).subschemeι
  have : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType i
  have hqc (M : CoherentModules X) : M.obj.IsQuasicoherent :=
    ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X M.obj).mp
      M.property).1
  let := hqc F
  let := hqc H
  have hcover : ∀ x : X, ∃ U ∈ (Set.univ : Set X.affineOpens), x ∈ U.1 := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (⊤ : X.Opens) from trivial) (⊤ : X.Opens).2
    exact ⟨⟨U, hU⟩, Set.mem_univ _, hx⟩
  have hann := (Scheme.idealPowerProduct_isZero_iff_affine_cover X F.obj K
    Set.univ hcover q).mp hF
  have hsupp : CoherentModuleSupportedOn H i := by
    change IsZero (Scheme.idealModuleProduct i.ker.toModulesι H.obj)
    have hk : i.ker = K ^ q := (K ^ q).ker_subschemeι
    rw [hk]
    have hz := (Scheme.idealPowerProduct_isZero_iff_affine_cover X H.obj (K ^ q)
      Set.univ hcover 1).mpr (by
        intro U _ a ha
        apply Module.mem_annihilator.mpr
        intro x
        have hinj : Function.Injective (j.app U.1) :=
          (ModuleCat.mono_iff_injective _).mp
            ((SheafOfModules.evaluation X.ringCatSheaf (op U.1)).map_mono j)
        apply hinj
        change (j.val.app (op U.1)).hom (a • x) = (j.val.app (op U.1)).hom 0
        rw [map_smul, map_zero]
        apply Module.mem_annihilator.mp (hann U (Set.mem_univ U) _)
        simpa using ha)
    exact hz
  obtain ⟨E, ⟨e⟩⟩ := closedImmersion_coherent_equivalence i
  let Hs : ObjectProperty.FullSubcategory (fun M : CoherentModules X ↦
      CoherentModuleSupportedOn M i) := ⟨H, hsupp⟩
  let L := E.inverse.obj Hs
  let C := ObjectProperty.ι (fun M : CoherentModules X ↦ CoherentModuleSupportedOn M i) ⋙
    ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace)
  let η : H.obj ≅ (Scheme.Modules.pushforward i).obj L.obj :=
    (C.mapIso (E.counitIso.app Hs)).symm ≪≫ e.app L
  obtain ⟨θ, _⟩ := closedImmersion_coherentFormal_equivalence_completion i I
  have hz : IsZero (formalCompletionSystem I H.obj) :=
    Functor.isZero _ (fun n ↦ hH n.unop)
  have hpush : IsZero ((formalCompletionSystem (I.comap i) L.obj) ⋙
      Scheme.Modules.pushforward i) :=
    hz.of_iso ((formalCompletionFunctor I).mapIso η ≪≫ θ.app L).symm
  let P := Scheme.Modules.pushforward i
  have hbij := (closedImmersion_pushforward_fullyFaithful i).2
  have : P.Full := ⟨fun {M N} ↦ (hbij M N).2⟩
  have : P.Faithful := ⟨fun {M N} ↦ (hbij M N).1⟩
  have hL (n : ℕᵒᵖ) : IsZero ((formalCompletionSystem (I.comap i) L.obj).obj n) := by
    apply IsZero.of_full_of_faithful_of_isZero P
    exact ((evaluation ℕᵒᵖ X.Modules).obj n).map_isZero hpush
  have hformal : IsZero ((completion Z (I.comap i)).obj L) := by
    apply IsZero.of_full_of_faithful_of_isZero (IsCoherentFormalModule (I.comap i)).ι
    exact Functor.isZero _ hL
  have : (completion Z (I.comap i)).IsEquivalence := hcompletion inferInstance
  have hLzero : IsZero L :=
    IsZero.of_full_of_faithful_of_isZero (completion Z (I.comap i)) L hformal
  have hLobj : IsZero L.obj :=
    (ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace)).map_isZero hLzero
  exact (P.map_isZero hLobj).of_iso η


end AlgebraicGeometry
