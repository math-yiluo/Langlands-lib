/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationAffineReplacement
import WeilConjectures.AlgebraicGeometry.ModuleFinitePresentationBinaryGluing
import WeilConjectures.AlgebraicGeometry.QuasiCoherentExtensionQcOpen
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Extension of finitely presented modules and their morphisms

Source: Stacks Project, Properties of Schemes, Lemma 28.23.4, Tag 01PI
(blueprint: lem-weil-pbc-module-finite-presentation-extension).

Restriction to an open is expressed on the localized site with `SheafOfModules.over`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem finitePresentation_of_top (X : Scheme.{u}) (M : X.Modules)
    [(M.over (⊤ : X.Opens)).IsFinitePresentation] : M.IsFinitePresentation := by
  apply SheafOfModules.IsFinitePresentation.of_coversTop M
    (fun _ : ULift.{u} Unit ↦ (⊤ : X.Opens))
    ((Opens.coversTop_iff _ _).mpr (by
      change (⨆ _ : ULift.{u} Unit, (⊤ : X.Opens)) = ⊤
      exact iSup_const))

private theorem finitePresentation_affine_enlargement
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W : X.Opens) (hW : IsCompact (W : Set X)) (V : X.affineOpens)
    (H : X.Modules) [H.IsQuasicoherent] [(H.over W).IsFinitePresentation] :
    ∃ (K : X.Modules), K.IsQuasicoherent ∧
      (K.over (W ⊔ V.1)).IsFinitePresentation ∧ ∃ (ψ : K ⟶ H), IsIso (ψ.over W) := by
  obtain ⟨E, hE, j, hj⟩ := exists_finitePresentation_affine_replacement X W hW V H
  have : E.IsFinitePresentation := hE
  have := hj
  obtain ⟨G, hG, φ, hφ⟩ := exists_finitePresentation_binary_gluing X W V.1 H E j
  have : G.IsFinitePresentation := hG
  let Z := W ⊔ V.1
  have hZ : IsCompact (Z : Set X) := hW.union V.2.isCompact
  have : CompactSpace Z.toScheme := isCompact_iff_compactSpace.mp hZ
  obtain ⟨K, hK, ψ, α, hψ⟩ :=
    exists_quasiCoherent_extension_of_quasiCompact_open X Z inferInstance H G φ
  have hKfp : (K.over Z).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over Z)).prop_of_iso α.symm hG
  let Q := SheafOfModules.overFunctor X.ringCatSheaf Z
  let P := SheafOfModules.overFunctor X.ringCatSheaf W
  let T := SheafOfModules.overMap X.ringCatSheaf
    (homOfLE (show W ≤ Z from le_sup_left))
  let η := SheafOfModules.overFunctorMap X.ringCatSheaf
    (homOfLE (show W ≤ Z from le_sup_left))
  have : IsIso (T.map φ) := hφ
  have hψW : IsIso (P.map ψ) := by
    have heq : P.map ψ = (η.app K).inv ≫ T.map (Q.map ψ) ≫ (η.app H).hom := by
      have hn := η.hom.naturality ψ
      change T.map (Q.map ψ) ≫ (η.app H).hom = (η.app K).hom ≫ P.map ψ at hn
      rw [hn]
      simp
    rw [heq, hψ, Functor.map_comp]
    infer_instance
  exact ⟨K, hK, hKfp, ψ, hψW⟩

/-- A morphism from a finitely presented module on a quasi-compact open of a qcqs scheme
into a quasi-coherent module extends to a finitely presented module on the whole scheme.
Source: Stacks Project, Properties of Schemes, Lemma 28.23.4, Tag 01PI
(blueprint: lem-weil-pbc-module-finite-presentation-extension).

Proof:
1. Extend G and its map quasi-coherently across U using
   lem-weil-pbc-quasi-coherent-extension-qc-open. This gives a global H with a map
   to F, an identification H restricted to U with G, and the required map equation.
2. Induct on finite sets of affine opens. Maintain a global quasi-coherent E,
   finite presentation on U union those opens, with a map E to H which is an
   isomorphism on U. The empty case uses H and its identity map. Each intermediate
   open is compact because U and the affine opens are compact.
3. To insert V, apply lem-weil-pbc-module-finite-presentation-affine-replacement
   to E and the previous compact open W. It produces a finitely presented module
   on V with a map to E restricted to V, isomorphic on W intersect V. Apply
   lem-weil-pbc-module-finite-presentation-binary-gluing to obtain a finitely
   presented module on W union V mapping to E there, isomorphic on W.
4. Extend the glued pair quasi-coherently to X, using the same extension theorem.
   Transport finite presentation along its restriction identification. Naturality
   of overFunctorMap shows the extended map remains an isomorphism on W and hence
   on U. Compose it with the previous map to H to close the induction step.
5. Compactness of X provides a finite affine subcover, so the growing open is top.
   Finite presentation on top implies global finite presentation by locality on
   the singleton top cover. Compose the map to H with its map to F; composing
   the restriction isomorphism with H restricted to U identified with G gives
   the asserted identification and morphism equation. -/
theorem exists_finitePresentation_extension
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) [F.IsQuasicoherent]
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    [G.IsFinitePresentation] (φ : G ⟶ F.over U) :
    ∃ (G' : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      G'.IsFinitePresentation ∧
        ∃ (φ' : G' ⟶ F) (e : G'.over U ≅ G),
          (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map φ' = e.hom ≫ φ := by
  classical
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨H, hH, ψ, α, hψ⟩ :=
    exists_quasiCoherent_extension_of_quasiCompact_open X U inferInstance F G φ
  have : H.IsQuasicoherent := hH
  have : (H.over U).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over U)).prop_of_iso
      α.symm inferInstance
  have key : ∀ t : Finset X.affineOpens,
      ∃ (E : X.Modules), E.IsQuasicoherent ∧
        (E.over (U ⊔ t.sup fun V ↦ V.1)).IsFinitePresentation ∧
        ∃ (j : E ⟶ H), IsIso (j.over U) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨H, inferInstance, ?_, 𝟙 H, ?_⟩
      · rw [Finset.sup_empty, sup_bot_eq]
        infer_instance
      · change IsIso ((SheafOfModules.overFunctor _ U).map (𝟙 H))
        rw [CategoryTheory.Functor.map_id]
        infer_instance
    | insert V t hV ih =>
      obtain ⟨E, hE, hEfp, j, hj⟩ := ih
      have : E.IsQuasicoherent := hE
      have : (E.over (U ⊔ t.sup fun V ↦ V.1)).IsFinitePresentation := hEfp
      have hW : IsCompact ((U ⊔ t.sup fun V ↦ V.1 : X.Opens) : Set X) := by
        rw [Opens.coe_sup, Opens.coe_finset_sup, Finset.sup_eq_iSup]
        exact hU.union (t.isCompact_biUnion fun V _ ↦ V.2.isCompact)
      obtain ⟨E', hE', hE'fp, j', hj'⟩ :=
        finitePresentation_affine_enlargement X _ hW V E
      have he : U ⊔ (insert V t).sup (fun V ↦ V.1) =
          (U ⊔ t.sup fun V ↦ V.1) ⊔ V.1 := by
        rw [Finset.sup_insert, sup_comm V.1 (t.sup fun V ↦ V.1), ← sup_assoc]
      have : IsIso (j.over U) := hj
      have : IsIso (j'.over (U ⊔ t.sup fun V ↦ V.1)) := hj'
      have : IsIso (j'.over U) := by
        apply (NatIso.isIso_map_iff
          (SheafOfModules.overFunctorMap X.ringCatSheaf
            (homOfLE (show U ≤ U ⊔ t.sup fun V ↦ V.1 from le_sup_left))) j').mp
        change IsIso ((SheafOfModules.overMap X.ringCatSheaf
          (homOfLE (show U ≤ U ⊔ t.sup fun V ↦ V.1 from le_sup_left))).map
            (j'.over (U ⊔ t.sup fun V ↦ V.1)))
        infer_instance
      refine ⟨E', hE', by rwa [he], j' ≫ j, ?_⟩
      change IsIso ((SheafOfModules.overFunctor _ U).map (j' ≫ j))
      rw [Functor.map_comp]
      infer_instance
  have hcov : (Set.univ : Set X) ⊆ ⋃ V : X.affineOpens, (V.1 : Set X) := by
    intro x _
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hx
    obtain ⟨V, hV⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨V, hV⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) hcov
  have he : U ⊔ t.sup (fun V ↦ V.1) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact (le_sup_right : t.sup (fun V ↦ V.1) ≤ U ⊔ t.sup (fun V ↦ V.1))
      ((Finset.le_sup (f := fun V ↦ V.1) hVt) hxV)
  obtain ⟨E, hE, hEfp, j, hj⟩ := key t
  have : (E.over (⊤ : X.Opens)).IsFinitePresentation := by rwa [he] at hEfp
  have : IsIso (j.over U) := hj
  refine ⟨E, finitePresentation_of_top X E, j ≫ ψ, asIso (j.over U) ≪≫ α, ?_⟩
  rw [Functor.map_comp, hψ]
  rfl

end AlgebraicGeometry.Scheme.Modules
