/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GenericFinite
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Quasi-finite separated morphisms are finite over a neighbourhood of the generic point

`AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_genericPoint`: over an irreducible
Noetherian base, a quasi-compact separated locally quasi-finite morphism of finite type is
finite over an open neighbourhood of the generic point. Factor it through a finite morphism with
dense open image (Zariski's main theorem followed by the scheme-theoretic image); a point of the
compactification over the generic point is maximal in its fibre, hence a generic point of an
irreducible component, hence in the dense open image.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- In a Noetherian space, a dense open set contains the generic point of every irreducible
component. -/
lemma mem_of_isGenericPoint_of_dense {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {U : Set T} (hU : IsOpen U) (hd : Dense U) {C : Set T}
    (hC : C ∈ irreducibleComponents T) {y : T} (hy : IsGenericPoint y C) : y ∈ U := by
  by_contra hyU
  obtain ⟨o, ho, hne, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨z, hzo, hzU⟩ := hd.inter_open_nonempty o ho hne
  have hCU : C ⊆ Uᶜ := by
    rw [← hy.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hyU) hU.isClosed_compl
  exact hCU (hoC hzo) hzU

/-- **Generic finiteness of quasi-finite morphisms.** Over an irreducible Noetherian scheme `S`,
a quasi-compact separated locally quasi-finite morphism locally of finite type is finite over an
open neighbourhood of the generic point. -/
theorem Hom.exists_isFinite_morphismRestrict_genericPoint {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    [IsNoetherian S] [IrreducibleSpace S] :
    ∃ V : S.Opens, genericPoint S ∈ V ∧ IsFinite (f ∣_ V) := by
  obtain ⟨T, j, p, hj, hjq, hp, rfl⟩ := f.exists_isOpenImmersion_isFinite_of_locallyQuasiFinite
  -- replace `T` by the closure of the image of `j`
  let j' := j.toImage
  let p' := j.imageι ≫ p
  have hjp : j' ≫ p' = j ≫ p := by simp [j', p', Scheme.Hom.toImage_imageι_assoc]
  have : IsNoetherian j.image := isNoetherian_of_locallyOfFiniteType p'
  have hd : Dense (Set.range j'.base) := j'.denseRange
  have hopen : IsOpen (Set.range j'.base) := j'.isOpenEmbedding.isOpen_range
  -- every point of the compactification over the generic point lies in the image of `j'`
  have key (x : j.image) (hx : p'.base x = genericPoint S) : x ∈ Set.range j'.base := by
    obtain ⟨C, hC, hxC⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {x} isIrreducible_singleton
    have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    have hy : IsGenericPoint hC.1.genericPoint C := by
      simpa [hCc.closure_eq] using hC.1.isGenericPoint_genericPoint_closure
    have hyU := mem_of_isGenericPoint_of_dense hopen hd hC hy
    have hyx : hC.1.genericPoint ⤳ x := hy.specializes (hxC rfl)
    have hpy : p'.base hC.1.genericPoint = genericPoint S := by
      have h1 : p'.base hC.1.genericPoint ⤳ genericPoint S := hx ▸ hyx.map p'.base.hom.continuous
      have h2 : IsGenericPoint (p'.base hC.1.genericPoint) ⊤ :=
        isGenericPoint_iff_specializes.mpr fun z ↦
          ⟨fun _ ↦ trivial, fun _ ↦ h1.trans ((genericPoint_spec S).specializes trivial)⟩
      exact h2.eq (genericPoint_spec S)
    have hdisc := (p'.isDiscrete_preimage_singleton (genericPoint S)).to_subtype
    have : (⟨hC.1.genericPoint, hpy⟩ : p'.base ⁻¹' {genericPoint S}) ⤳ ⟨x, hx⟩ :=
      (subtype_specializes_iff _ _).mpr hyx
    have h3 := congrArg Subtype.val this.eq
    simp only at h3
    exact h3 ▸ hyU
  have hZ : IsClosed (p'.base '' (Set.range j'.base)ᶜ) :=
    p'.isClosedMap _ hopen.isClosed_compl
  refine ⟨⟨_, hZ.isOpen_compl⟩, fun ⟨x, hx, hpx⟩ ↦ hx (key x hpx), ?_⟩
  rw [← hjp, morphismRestrict_comp]
  have : IsIso (j' ∣_ p' ⁻¹ᵁ ⟨_, hZ.isOpen_compl⟩) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
    have hy : y.1 ∈ Set.range j'.base := by
      by_contra h
      exact y.2 ⟨y.1, h, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨⟨x, ?_⟩, Subtype.ext ?_⟩
    · change p'.base (j'.base x) ∈ (p'.base '' (Set.range j'.base)ᶜ)ᶜ
      rw [hx]
      exact y.2
    · rw [morphismRestrict_base_coe]
      exact hx
  infer_instance

end AlgebraicGeometry.Scheme
