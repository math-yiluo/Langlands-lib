/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.AmplePullbackIdealAffineSection
import WeilConjectures.AlgebraicGeometry.AffineImageAwayClosedCover
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ConductorSections
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine power sections away from component intersections

Source: Stacks Project, Varieties, Lemma 09NX, final paragraph, and Remark 09NW.
(blueprint: lem-sc-component-supported-affine-section).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- An invertible module with ample restrictions to the reduced components has an
ambient affine power-section neighbourhood at a point on exactly one component.
No ampleness near component intersections is asserted.

Source: Stacks Project, Varieties, Lemma 09NX, final paragraph, and Remark 09NW;
Properties, Proposition 01Q3 and Lemma 01PV.
(blueprint: lem-sc-component-supported-affine-section).

Proof: Choose the unique component containing x and the reduced union Z of the other
components. Let I be the ideal of Z and I_a its image on the chosen component. The point
lifting x does not belong to V(I_a). The ample-ideal-section theorem supplies a positive
power section t1 coming from I_a, nonvanishing there. Ampleness on that component also
supplies a positive-power section t2 whose affine locus contains that point. Multiply
the two sections. Its degree is the sum of two positive integers, it still comes from
I_a, and its nonvanishing locus is the intersection of their loci. Apply
lem-sc-affine-cap-section-open inside the affine locus of t2 to make this intersection
affine. Use the canonical compatibility of pullback with tensor powers, then
lem-sc-conductor-sections to extend the product to X with zero restriction on Z.
Its nonvanishing locus is the image of the component locus. It avoids Z, and away from
Z the reduced component immersion is an isomorphism: its ideal vanishes because X is
reduced and its support is empty there. Thus this image is an affine open of X
containing x. For a single component Z is empty and the same argument uses I = O_X.
With no components the hypothesis on x is impossible. -/
theorem exists_component_supported_affine_section
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] [IsReduced X]
    (r : ℕ) (C : Fin r → Scheme.{u}) (i : ∀ a, C a ⟶ X)
    [∀ a, IsReduced (C a)] [∀ a, IsClosedImmersion (i a)]
    (hcomponents : ∀ a, Set.range (i a) ∈ irreducibleComponents X)
    (hdistinct : Function.Injective fun a ↦ Set.range (i a))
    (hcover : (⋃ a, Set.range (i a)) = Set.univ)
    (L : X.Modules) [L.IsInvertible]
    (hL : ∀ a, ∃ h : ((tensorPullback (i a)).obj L).IsInvertible,
      @IsAmple (C a) ((tensorPullback (i a)).obj L) h)
    (x : X) (hx : ∃! a, x ∈ Set.range (i a)) :
    ∃ n : ℕ, 0 < n ∧
      ∃ s : (L.tensorPow n).val.presheaf.obj (Opposite.op ⊤),
        ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
          (U : Set X) = nonvanishingLocus (L.tensorPow n) s := by
  classical
  obtain ⟨a, hxa, huniq⟩ := hx
  obtain ⟨y, hy⟩ := hxa
  let T : TopologicalSpace.Closeds X :=
    Finset.univ.sup (fun b : {b : Fin r // b ≠ a} ↦
      ⟨Set.range (i b.val), (i b.val).isClosedEmbedding.isClosed_range⟩)
  have hT : (T : Set X) = ⋃ b : Fin r, ⋃ (_ : b ≠ a), Set.range (i b) := by
    simp only [T, TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion,
      Finset.mem_univ, Set.iUnion_true, Function.comp_apply]
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨⟨b, hba⟩, hz⟩
      exact ⟨b, hba, hz⟩
    · rintro ⟨b, hba, hz⟩
      exact ⟨⟨b, hba⟩, hz⟩
  let I := Scheme.IdealSheafData.vanishingIdeal T
  let Z := I.subscheme
  let j : Z ⟶ X := I.subschemeι
  have hZ : Set.range j = ⋃ b : Fin r, ⋃ (_ : b ≠ a), Set.range (i b) := by
    change Set.range I.subschemeι = _
    simpa [I] using hT
  have hxT : x ∉ (T : Set X) := by
    rw [hT]
    intro hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hba, hxb⟩ := Set.mem_iUnion.mp hb
    exact hba (huniq b hxb)
  have hyI : y ∉ ((j.ker.comap (i a)).support : Set (C a)) := by
    rw [Scheme.IdealSheafData.support_comap]
    change i a y ∉ (j.ker.support : Set X)
    rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq]
    rw [hZ, ← hT, hy]
    exact hxT
  obtain ⟨hLa, hample⟩ := hL a
  let := hLa
  obtain ⟨n, hn, v, V, hyV, hV, hVs, havoid⟩ :=
    exists_ample_pullback_ideal_affine_section (i a) L hample (j.ker.comap (i a)) y hyI
  obtain ⟨e, _, hext⟩ := conductor_sections C i hcomponents hdistinct hcover a j hZ L n
  obtain ⟨⟨s, hs, _⟩, hloc⟩ := hext v
  have hlocus := hloc s hs.1 hs.2
  have himage : nonvanishingLocus (L.tensorPow n) s = i a '' (V : Set (C a)) := by
    exact hlocus.trans (congrArg (fun S ↦ i a '' S) hVs.symm)
  have hcoverT : Set.range (i a) ∪ (T : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ ⋃ b, Set.range (i b) := by rw [hcover]; trivial
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hz
    by_cases hba : b = a
    · exact Or.inl (hba ▸ hb)
    · exact Or.inr (by rw [hT]; exact
        Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hba, hb⟩⟩)
  have havoidT : Disjoint (i a '' (V : Set (C a))) (T : Set X) := by
    rw [Set.disjoint_left]
    rintro z ⟨w, hw, rfl⟩ hz
    have hwJ : w ∈ ((j.ker.comap (i a)).support : Set (C a)) := by
      rw [Scheme.IdealSheafData.support_comap]
      change i a w ∈ (j.ker.support : Set X)
      rw [Scheme.Hom.support_ker, j.isClosedEmbedding.isClosed_range.closure_eq]
      rwa [hZ, ← hT]
    exact Set.disjoint_left.mp havoid hw hwJ
  obtain ⟨U, hU, hUimage⟩ :=
    Scheme.exists_affineOpen_image_away_closed_cover (i a) T hcoverT V hV havoidT
  refine ⟨n, hn, s, U, ?_, hU, hUimage.trans himage.symm⟩
  rw [← SetLike.mem_coe, hUimage]
  exact ⟨y, hyV, hy⟩

end AlgebraicGeometry.Scheme.Modules
