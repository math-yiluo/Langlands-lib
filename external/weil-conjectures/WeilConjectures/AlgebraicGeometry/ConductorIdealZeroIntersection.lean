/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.Images
import WeilConjectures.AlgebraicGeometry.ClosedImmersionDisjointIdealTwist

/-!
# Conductor ideal: zero intersection and restriction to a component

Source: literature/stacks-project/varieties.tex, Varieties Remark 09NW, as used in the proof
of Lemma 09NX (blueprint: lem-sc-conductor-ideal-zero-intersection).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Limits

namespace AlgebraicGeometry

open Scheme

/-- On a reduced scheme covered by its finitely many reduced irreducible components, the
ideal `I` of the reduced union of the components other than `Z₁` meets the ideal `J₁` of
`Z₁` in zero on every open, and for every invertible module `M` and every `m ≥ 0` the
restriction `Γ(U, I M^{⊗m}) → Γ(U ∩ Z₁, I₁ (M|_{Z₁})^{⊗m})` is bijective on every open `U`.

Source: Stacks Project, Varieties Remark 09NW and Lemma 09NX
(blueprint: lem-sc-conductor-ideal-zero-intersection).

Here, as in `Scheme.conductorIdeal_restriction_isIso`, `i` lists the distinct components
(`hdistinct`), `a` labels `Z₁`, `j` is the immersion of the reduced union `Z` of the other
components, `I = j.ker`, `J₁ = (i a).ker`, and `I₁` is the image of the map
`φ : i₁^* I → 𝒪_{Z₁}` adjoint to the inclusion of `I` followed by the structure-sheaf map.
`μ` and `μ₁` are the multiplication maps `I ⊗ M^{⊗m} → M^{⊗m}` and
`I₁ ⊗ (M|_{Z₁})^{⊗m} → (M|_{Z₁})^{⊗m}`; their images are `I M^{⊗m}` and
`I₁ (M|_{Z₁})^{⊗m}`. The restriction is the unit `M^{⊗m} → i₁_* i₁^* M^{⊗m}` followed by an
identification `e : i₁^*(M^{⊗m}) ≅ (i₁^* M)^{⊗m}`; any `O_{Z₁}`-linear `e` carries
`I₁ · i₁^*(M^{⊗m})` onto `I₁ (M|_{Z₁})^{⊗m}`, so the clause is stated for every `e`.
`ρ` is the restriction corestricted to `I₁ (M|_{Z₁})^{⊗m}`; its sections over `U` are the map
`Γ(U, I M^{⊗m}) → Γ(U ∩ Z₁, I₁ (M|_{Z₁})^{⊗m})`.

Proof:
1. On an affine open `U = Spec A` the closed subschemes `Z₁` and `Z` are cut out by ideals
`J₁` and `I` with `V(I) ∪ V(J₁) = Spec A`, and `A` is reduced since `Y` is
(def-pc-reduced-scheme, def-sbc-closed-immersion-ideal-sheaf).
2. By lem-sc-reduced-ideals-zero-intersection, `I ∩ J₁ = 0` and `I` maps isomorphically onto
its image `(I + J₁)/J₁` in `A/J₁`. Hence the sheaf intersection is zero and the restriction
`I → i₁_* I₁` is bijective on a basis of opens, so it is an isomorphism of sheaves and is
bijective on every open (this is the case `m = 0`).
3. On an open `V` trivialising `M` (def-sc-invertible-module), `M^{⊗m}|_V ≅ 𝒪_V` and
`(M|_{Z₁})^{⊗m}|_{V ∩ Z₁} ≅ 𝒪_{V ∩ Z₁}` (def-pur-sheaf-tensor-product), under which the two
image sheaves become `I|_V` and `I₁|_{V ∩ Z₁}` compatibly with restriction. So the restriction
is locally the isomorphism of step 2, hence an isomorphism, bijective on every open. -/
theorem conductorIdealZeroIntersection
    {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (C : ι → Scheme.{u}) (i : ∀ b : ι, C b ⟶ Y)
    [∀ b : ι, IsReduced (C b)] [∀ b : ι, IsClosedImmersion (i b)]
    (hcomponents : ∀ b : ι, Set.range (i b) ∈ irreducibleComponents Y)
    (hdistinct : Function.Injective fun b : ι => Set.range (i b))
    (hcover : (⋃ b : ι, Set.range (i b)) = Set.univ) (a : ι)
    {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hZ : Set.range j = ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i b)) :
    let I : Y.IdealSheafData := j.ker
    let J₁ : Y.IdealSheafData := (i a).ker
    let adj := Classical.choice (Modules.nonempty_tensorPullbackAdjunction (i a))
    let φ := (adj.homEquiv I.toModules (SheafOfModules.unit (C a).ringCatSheaf)).symm
      (I.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit (i a).toRingCatSheafHom)
    (∀ U : Y.Opens, I.idealOfOpens U ⊓ J₁.idealOfOpens U = ⊥) ∧
    ∀ (M : Y.Modules) [M.IsInvertible] (m : ℕ)
      (e : (Modules.tensorPullback (i a)).obj (M.tensorPow m) ≅
        ((Modules.tensorPullback (i a)).obj M).tensorPow m),
      let μ := I.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
      let μ₁ := image.ι φ ▷ ((Modules.tensorPullback (i a)).obj M).tensorPow m ≫
        (λ_ (((Modules.tensorPullback (i a)).obj M).tensorPow m)).hom
      ∃ ρ : image μ ⟶ (Modules.pushforward (i a)).obj (image μ₁),
        ρ ≫ (Modules.pushforward (i a)).map (image.ι μ₁) =
            image.ι μ ≫ adj.unit.app (M.tensorPow m) ≫ (Modules.pushforward (i a)).map e.hom ∧
          ∀ U : Y.Opens, Function.Bijective (ρ.app U) := by
  classical
  -- The support argument only needs the cover, but preserves the component interface.
  have _ := hcomponents
  have _ := hdistinct
  dsimp only
  have hzero : ∀ U : Y.Opens,
      j.ker.idealOfOpens U ⊓ (i a).ker.idealOfOpens U = ⊥ := by
    intro U
    apply le_antisymm _ bot_le
    intro s hs
    rw [Ideal.mem_bot, ← basicOpen_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro y hy
    have avoid (K : Y.IdealSheafData) (hsK : s ∈ K.idealOfOpens U)
        (hyK : y ∈ K.support) : False := by
      have hyrange : y ∈ Set.range K.subschemeι := by
        rw [K.range_subschemeι]
        exact hyK
      obtain ⟨z, hz⟩ := hyrange
      have hm : K.subschemeι.app U s = 0 :=
        K.mem_idealOfOpens_iff.mp hsK
      have hb : K.subschemeι ⁻¹ᵁ Y.basicOpen s = ⊥ := by
        rw [Scheme.preimage_basicOpen, hm, Scheme.basicOpen_zero]
      have hzmem : z ∈ K.subschemeι ⁻¹ᵁ Y.basicOpen s := by
        change K.subschemeι z ∈ Y.basicOpen s
        rwa [hz]
      rw [hb] at hzmem
      exact hzmem
    have hycover : y ∈ ⋃ b : ι, Set.range (i b) := by rw [hcover]; trivial
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hycover
    by_cases hba : b = a
    · subst b
      exact avoid (i a).ker hs.2 ((i a).range_subset_ker_support hb)
    · have hyZ : y ∈ Set.range j := by
        rw [hZ]
        exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hba, hb⟩⟩
      exact avoid j.ker hs.1 (j.range_subset_ker_support hyZ)
  refine ⟨hzero, ?_⟩
  intro M _ m e
  obtain ⟨ρ, hρ, hbij⟩ := Modules.closedImmersion_disjointIdeal_twist (i a) j.ker hzero M m e
  exact ⟨ρ, hρ, hbij⟩

end AlgebraicGeometry
