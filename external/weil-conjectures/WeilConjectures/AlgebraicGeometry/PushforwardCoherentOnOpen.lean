/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Topology.Sets.Closeds
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum

/-! # Coherent pushforward from an open with closed ambient support

Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.11 (Tag 0CYJ)
(blueprint: lem-weil-pbc-pushforward-coherent-on-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- If a coherent module on an open subscheme has support contained in a closed subset
of the ambient scheme lying inside that open, its direct image is coherent. Its restriction
back to the open is isomorphic to the original module, and its restriction to the complement
of the closed subset is zero. Support is the nonzero-stalk locus, as in
`def-weil-pbc-closed-subset-proper-over-base`; no properness assumption is needed here.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.9.11 (Tag 0CYJ)
(blueprint: lem-weil-pbc-pushforward-coherent-on-open).

Proof:
1. Mathlib's `restrictFunctorAdjCounitIso` identifies the restriction back to `U` with `F`.
2. On an open `V` of `T.compl`, the restricted pushforward has the sections of `F` on
   `U.ι ⁻¹ᵁ (T.compl.ι ''ᵁ V)`. Every point of this preimage lies outside `T`, so the support
   hypothesis makes its stalk subsingleton. By Mathlib's `TopCat.Presheaf.section_ext`,
   every section equals zero. Extensionality gives `𝟙 = 0`, hence this restriction is zero.
3. The opens `U` and `T.compl` cover `X` because `T ⊆ U`. Coherence is invariant under
   isomorphism, and the zero module is coherent, by
   `lem-weil-pbc-coherent-modules-kernel-cokernel-sum`. Thus both restrictions are coherent.
   Apply `lemma-coherent-base-change-invertible-sheaves--1` to this two-element cover. -/
theorem pushforward_coherent_on_open (X : Scheme.{u}) (U : X.Opens) (T : Closeds X)
    (hT : (T : Set X) ⊆ (U : Set X)) (F : U.toScheme.Modules)
    (hF : RingedSpace.IsCoherent U.toScheme.toRingedSpace F)
    (hSupp : {x : U.toScheme | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
      U.ι.base ⁻¹' (T : Set X)) :
    RingedSpace.IsCoherent X.toRingedSpace ((pushforward U.ι).obj F) ∧
      Nonempty ((restrictFunctor U.ι).obj ((pushforward U.ι).obj F) ≅ F) ∧
      IsZero ((restrictFunctor (Scheme.Opens.ι T.compl)).obj ((pushforward U.ι).obj F)) := by
  classical
  let G := (pushforward U.ι).obj F
  let H := (restrictFunctor (Scheme.Opens.ι T.compl)).obj G
  have e : (restrictFunctor U.ι).obj G ≅ F :=
    (restrictFunctorAdjCounitIso U.ι).app F
  have hzero : IsZero H := by
    apply (IsZero.iff_id_eq_zero H).2
    ext V s
    change s = 0
    apply TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩
    intro x hx
    have hxT : U.ι.base x ∉ (T : Set X) := by
      exact Scheme.Opens.ι_image_le T.compl V hx
    have hxzero : Subsingleton (F.presheaf.stalk x) := by
      by_contra hn
      exact hxT (hSupp hn)
    exact hxzero.elim _ _
  have hU : U ⊔ T.compl = ⊤ := by
    apply le_antisymm le_top
    intro x _
    by_cases hx : x ∈ (T : Set X)
    · exact Or.inl (hT hx)
    · exact Or.inr hx
  let W : ULift.{u} Bool → X.Opens := fun i => if i.down then U else T.compl
  have hW : ⨆ i, W i = ⊤ := by
    apply le_antisymm le_top
    rw [← hU]
    apply sup_le
    · exact le_iSup_of_le (ULift.up true) (by simp [W])
    · exact le_iSup_of_le (ULift.up false) (by simp [W])
  have hcoh : RingedSpace.IsCoherent X.toRingedSpace G := by
    apply (coherent_module_local_on_open_cover X G (ULift.{u} Bool) W hW).2
    intro i
    cases i with
    | up b =>
      cases b
      · change RingedSpace.IsCoherent (Scheme.Opens.toScheme T.compl).toRingedSpace H
        exact (RingedSpace.coherent_kernel_cokernel_sum _).2.2.2.2 _ _
          hzero.isoZero.symm (RingedSpace.coherent_kernel_cokernel_sum _).2.2.2.1
      · change RingedSpace.IsCoherent U.toScheme.toRingedSpace _
        exact (RingedSpace.coherent_kernel_cokernel_sum _).2.2.2.2 _ _ e.symm hF
  exact ⟨hcoh, ⟨e⟩, hzero⟩

end AlgebraicGeometry.Scheme.Modules
