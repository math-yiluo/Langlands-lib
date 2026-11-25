/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PerfectSupportedMapLift
import WeilConjectures.AlgebraicGeometry.OpenDerivedRestrictionComparison
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh

/-! # The detector on the localized smaller open

Source: Stacks Project, Tag 0A9A, induction paragraphs.
(blueprint: lem-pc-supported-detector-open-lift-core).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
/-- A supported perfect global object whose derived restriction detects the supported
quasi-coherent objects on the smaller open. No assertion of global detection is made.
Source: Stacks Project, Tag 0A9A, induction paragraphs and retract argument.
(blueprint: lem-pc-supported-detector-open-lift-core).

Proof:
1. Choose V in s and let U be the union of s.erase V. Each remaining chart lies in U,
   so its inverse image under U.toScheme.ι is affine, and these give a cover of U with
   at most s.card - 1 members. The finite union U is compact. Quasi-separatedness of X
   makes U intersect T-complement compact. U.toScheme is quasi-separated and compact.
2. Transport the derived localizations through Modules.overEquiv U, and similarly on
   every open of U. The homology comparison identifies quasi-coherence and zero stalks.
   Apply ih to this smaller cover and the inverse image of T, which is closed with
   compact complement. This supplies a perfect supported detector P on U.toScheme.
3. Apply exists_perfect_supported_map_lift to P, the zero quasi-coherent object on X,
   and the zero map. The resulting global perfect object Q is supported on T and P is
   a retract of its restriction. Q has quasi-coherent cohomology: its local strictly
   perfect representatives have quasi-coherent finite locally free terms and hence
   quasi-coherent homology; quasi-coherence is local.
4. Derived exact open restriction has a right adjoint, obtained by deriving open direct
   image using K-injective resolutions. Transport the adjunction through the canonical
   open module equivalence to obtain R and adj in the displayed localized categories.
5. Given K supported on T, exact restriction and the homology comparison give a
   supported quasi-coherent object on U. If every Hom from the restriction of Q[n]
   vanishes, the shift comparison and the shifted retract of P make every Hom from
   P[n] vanish. The detector from step 2 makes the restriction of K zero. Notice this
   argument never assumes an invertible global unit and never concludes that K is zero.
   When U is empty its derived category is zero; redundant charts only decrease the
   size of the induced cover and do not affect the argument. -/
theorem exists_supported_detector_open_lift_core
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (s : Finset X.affineOpens) (hcover : (⨆ U ∈ s, (U : X.Opens)) = ⊤)
    (hcard : 2 ≤ s.card)
    (ih : ∀ (Y : Scheme.{u}) [CompactSpace Y] [QuasiSeparatedSpace Y]
      [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
      [∀ U : Y.Opens,
        HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
      (t : Finset Y.affineOpens), t.card < s.card →
      (⨆ U ∈ t, (U : Y.Opens)) = ⊤ →
      ∀ (S : Set Y), IsClosed S → IsCompact Sᶜ →
        ∃ E : schemeDerivedQCohCategory Y, Scheme.IsPerfect Y E.obj ∧
          (∀ (n : ℤ) (x : Y), x ∉ S →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E.obj).val.presheaf x))) ∧
          ∀ K : schemeDerivedQCohCategory Y,
            (∀ (n : ℤ) (x : Y), x ∉ S →
              Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
            (∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj)) → IsZero K.obj)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ) :
    ∃ (U : X.Opens) (V : X.affineOpens), IsCompact (U : Set X) ∧
      U ⊔ (V : X.Opens) = ⊤ ∧
      ∃ (R : DerivedCategory
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
          schemeDerivedCategory X)
        (_ : (SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory ⊣ R)
        (Q : schemeDerivedQCohCategory X),
        Scheme.IsPerfect X Q.obj ∧
        (∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj Q.obj).val.presheaf x))) ∧
        ∀ K : schemeDerivedQCohCategory X,
          (∀ (n : ℤ) (x : X), x ∉ T →
            Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K.obj).val.presheaf x))) →
          (∀ n : ℤ, Subsingleton
            ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
               (Q.obj⟦n⟧) ⟶
            (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
               K.obj)) →
          IsZero
            ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
               K.obj) := by
  classical
  obtain ⟨V, hV⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  let a := s.erase V
  let U : X.Opens := ⨆ W ∈ a, (W : X.Opens)
  have hU : IsCompact (U : Set X) := by
    simpa only [U, TopologicalSpace.Opens.coe_iSup] using
      a.isCompact_biUnion (fun W _ ↦ W.property.isCompact)
  have hUV : U ⊔ (V : X.Opens) = ⊤ := by
    rw [← hcover]
    apply le_antisymm
    · apply sup_le
      · exact iSup₂_le fun W hW ↦ le_iSup₂_of_le W (Finset.mem_of_mem_erase hW) le_rfl
      · exact le_iSup₂_of_le V hV le_rfl
    · apply iSup₂_le
      intro W hW
      by_cases hWV : W = V
      · subst W
        exact le_sup_right
      · exact le_sup_of_le_left
          (le_iSup₂_of_le W (Finset.mem_erase.mpr ⟨hWV, hW⟩) le_rfl)
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let : QuasiSeparatedSpace U.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding U.isOpenEmbedding
  let f : {W // W ∈ a} → U.toScheme.affineOpens := fun W ↦
    ⟨U.ι ⁻¹ᵁ (W.val : X.Opens), W.val.property.preimage_of_isOpenImmersion U.ι
      (by
        rw [Scheme.Opens.opensRange_ι]
        exact le_iSup₂_of_le W.val W.property le_rfl)⟩
  let t : Finset U.toScheme.affineOpens := Finset.univ.image f
  have htcard : t.card < s.card := by
    have ht : t.card ≤ a.card := by
      simpa [t] using (Finset.card_image_le (s := Finset.univ) (f := f))
    exact lt_of_le_of_lt ht (Finset.card_erase_lt_of_mem hV)
  have htcover : (⨆ W ∈ t, (W : U.toScheme.Opens)) = ⊤ := by
    apply top_unique
    intro x _
    have hx : x.val ∈ U := x.property
    simp only [U, TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨W, hW, hxW⟩ := hx
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨f ⟨W, hW⟩, TopologicalSpace.Opens.mem_iSup.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨⟨W, hW⟩, Finset.mem_univ _, rfl⟩
    · exact hxW
  let S : Set U.toScheme := Subtype.val ⁻¹' T
  have hS : IsClosed S := hT.preimage continuous_subtype_val
  have hSc : IsCompact Sᶜ := by
    have hi : IsCompact ((U : Set X) ∩ Tᶜ) :=
      hU.inter_of_isOpen hTc U.isOpen hT.isOpen_compl
    apply Subtype.isCompact_iff.mpr
    have heq : Subtype.val '' Sᶜ = (U : Set X) ∩ Tᶜ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hxU, hxT⟩
        exact ⟨⟨x, hxU⟩, hxT, rfl⟩
    rw [heq]
    exact hi
  obtain ⟨hD, hO, R, adj, hqc, hsupp, horth, hzero⟩ :=
    open_derived_restriction_comparison X U
  let := hD
  let := hO
  let M := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
  obtain ⟨P, hP, hPT, hdet⟩ := ih U.toScheme t htcard htcover S hS hSc
  have hzfree : IsZero
      (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero :=
    ⟨⟨_, hzfree, SheafOfModules.isQuasicoherent_free
      (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}⟩⟩
  let E : schemeDerivedQCohCategory X := ⟨0, fun n ↦
    (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_isZero
      ((DerivedCategory.homologyFunctor _ n).map_isZero (isZero_zero _))⟩
  obtain ⟨Q, β, hQ, hQT, i, p, hip, _⟩ :=
    Scheme.exists_perfect_supported_map_lift X U hU T hT hTc E P.obj hP hPT 0
  have hQqc : schemeDerivedQCohProperty X Q := by
    have : ∀ W : X.Opens, HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) :=
      fun W ↦ (open_derived_restriction_comparison X W).choose
    exact Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent X Q
      (Scheme.perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension X Q hQ).1
  let Qc : schemeDerivedQCohCategory X := ⟨Q, hQqc⟩
  refine ⟨U, V, hU, hUV, R, adj, Qc, hQ, hQT, ?_⟩
  intro K hKT hKorth
  apply hzero
  let Ku : schemeDerivedQCohCategory U.toScheme := ⟨M.obj K.obj, hqc K.obj K.property⟩
  apply hdet Ku (hsupp T K.obj hKT)
  intro n
  have := horth Q K.obj n (hKorth n)
  let i' := (shiftFunctor (schemeDerivedCategory U.toScheme) n).map i
  let p' := (shiftFunctor (schemeDerivedCategory U.toScheme) n).map p
  have hi'p' : i' ≫ p' = 𝟙 (P.obj⟦n⟧) := by
    dsimp [i', p']
    rw [← Functor.map_comp, hip]
    exact (shiftFunctor _ n).map_id _
  refine ⟨fun b c ↦ ?_⟩
  have hbc : p' ≫ b = p' ≫ c := Subsingleton.elim _ _
  have := congrArg (fun k ↦ i' ≫ k) hbc
  simpa only [← Category.assoc, hi'p', Category.id_comp] using this
end AlgebraicGeometry
