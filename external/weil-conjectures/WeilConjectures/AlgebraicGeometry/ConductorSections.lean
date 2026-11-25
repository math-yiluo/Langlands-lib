/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ConductorSectionsRestriction
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Modules.Dual

/-! # Extending conductor-supported sections from one component

Source: Stacks Project, Varieties, Remark 09NW and the conductor equality in the proof
of Lemma 09NX (blueprint: lem-sc-conductor-sections).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction identifies the sections of the ideal of the other components, tensored
with an invertible module, with the corresponding sections on the first component.

Source: Stacks Project, Varieties, Remark 09NW and Lemma 09NX, proof
(blueprint: lem-sc-conductor-sections).

Here `i` lists the distinct components `Z₁, …, Z_r` (`hdistinct`), `a` labels the first
component, `j` is the immersion of the reduced union of all other components, `I = j.ker`
and `I₁ = I.comap (i a)` is the image of `(i a)^* I` in `O_{Z₁}`. Module pullback is
`tensorPullback` (def-pc-module-pullback); `res₁` and `resZ` are restriction of global
sections, the units of its canonical adjunction (lem-pc-module-pullback-adjunction). We use
`(i a)^*(M^{⊗ m})`, canonically isomorphic to `((i a)^* M)^{⊗ m}`. The maps `μ` and `μ₁`
are the inclusions of the ideal products, injective since tensoring with an invertible
module is exact. `X_s` is `nonvanishingLocus` (def-weil-pbc-ample-invertible-module).

Proof: apply `lem-sc-conductor-ideal-restriction` to the reduced cover by the first
component and the union of the others. Tensor its ideal restriction isomorphism with
`M^{⊗ m}`, using `def-sc-invertible-module`. By
`lem-sc-conductor-ideal-zero-intersection`, the two defining ideals have zero
intersection, and restriction of the ideal-supported tensor product is a bijection
on sections over every open. Apply this on the whole scheme to obtain `e` and unique
extension. Its inclusion in the tensor power vanishes on the other components by
`def-sbc-closed-immersion-ideal-sheaf`. Away from their union there is only the first
component, so the germ criterion in `def-weil-pbc-ample-invertible-module` gives
exactly the image of the original nonvanishing locus. -/
theorem conductor_sections {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (C : ι → Scheme.{u}) (i : ∀ b : ι, C b ⟶ Y)
    [∀ b : ι, IsReduced (C b)] [∀ b : ι, IsClosedImmersion (i b)]
    (hcomponents : ∀ b : ι, Set.range (i b) ∈ irreducibleComponents Y)
    (hdistinct : Function.Injective fun b : ι => Set.range (i b))
    (hcover : (⋃ b : ι, Set.range (i b)) = Set.univ) (a : ι)
    {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hZ : Set.range j = ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i b))
    (M : Y.Modules) [M.IsInvertible] (m : ℕ) :
    let N := M.tensorPow m
    let N₁ := (tensorPullback (i a)).obj N
    let adj₁ := Classical.choose (exists_tensorPullbackAdjunction (i a))
    let adjZ := Classical.choose (exists_tensorPullbackAdjunction j)
    let res₁ : Γ(N, ⊤) → Γ(N₁, ⊤) := fun t ↦ (adj₁.unit.app N).val.app (op ⊤) t
    let resZ : Γ(N, ⊤) → Γ((tensorPullback j).obj N, ⊤) :=
      fun t ↦ (adjZ.unit.app N).val.app (op ⊤) t
    let I := j.ker
    let I₁ := I.comap (i a)
    let μ : I.toModules ⊗ N ⟶ N := I.toModulesι ▷ N ≫ (λ_ N).hom
    let μ₁ : I₁.toModules ⊗ N₁ ⟶ N₁ := I₁.toModulesι ▷ N₁ ≫ (λ_ N₁).hom
    ∃ e : Γ(I.toModules ⊗ N, ⊤) ≃+ Γ(I₁.toModules ⊗ N₁, ⊤),
      (∀ s, μ₁.app ⊤ (e s) = res₁ (μ.app ⊤ s)) ∧
      ∀ s : Γ(I₁.toModules ⊗ N₁, ⊤),
        (∃! t : Γ(N, ⊤), res₁ t = μ₁.app ⊤ s ∧ resZ t = 0) ∧
        ∀ t : Γ(N, ⊤), res₁ t = μ₁.app ⊤ s → resZ t = 0 →
          nonvanishingLocus N t = i a '' nonvanishingLocus N₁ (μ₁.app ⊤ s) := by
  classical
  dsimp only
  obtain ⟨r, hr, hcompat⟩ := conductor_sections_restriction C i hcomponents
    hdistinct hcover a j hZ M m
  obtain ⟨_, hkernel⟩ := closedImmersion_ideal_tensor_sections j M m
  let N₁ := (tensorPullback (i a)).obj (M.tensorPow m)
  let μ₁ := (j.ker.comap (i a)).toModulesι ▷ N₁ ≫ (λ_ N₁).hom
  have : N₁.IsInvertible := ((invertible_pullback_tensor (i a)).1 (M.tensorPow m)).2
  have : Mono μ₁ := inferInstance
  have hμ₁ : Function.Injective (μ₁.app ⊤) :=
    (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation (C a).ringCatSheaf (op ⊤)).map μ₁)).mp inferInstance
  let e := AddEquiv.ofBijective r hr
  refine ⟨e, hcompat, ?_⟩
  intro s
  let q := e.symm s
  have he : r q = s := e.apply_symm_apply s
  have hzero :
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (M.tensorPow m)).val.app (op ⊤)
          ((j.ker.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom).app ⊤ q) = 0 :=
    (hkernel _).2 ⟨q, rfl⟩
  constructor
  · refine ⟨_, ⟨?_, hzero⟩, ?_⟩
    · exact (hcompat q).symm.trans (congrArg (μ₁.app ⊤) he)
    · intro t ht
      obtain ⟨q', hq'⟩ := (hkernel t).1 ht.2
      have hq : r q' = r q := by
        apply hμ₁
        exact (hcompat q').trans ((congrArg
          (fun t ↦ ((Classical.choose (exists_tensorPullbackAdjunction (i a))).unit.app
            (M.tensorPow m)).val.app (op ⊤) t) hq').trans
              (ht.1.trans (congrArg (μ₁.app ⊤) he.symm)))
      exact hq'.symm.trans (congrArg _ (hr.1 hq))
  · intro t ht₁ htZ
    ext y
    constructor
    · intro hy
      have hyZ : y ∉ Set.range j := by
        rintro ⟨z, rfl⟩
        have hz := (nonvanishing_tensorPullback j (M.tensorPow m) t z).2 hy
        rw [htZ] at hz
        simp [nonvanishingLocus] at hz
      have hycover : y ∈ ⋃ b : ι, Set.range (i b) := by rw [hcover]; trivial
      obtain ⟨b, x, hx⟩ := Set.mem_iUnion.mp hycover
      have hb : b = a := by
        by_contra hba
        apply hyZ
        rw [hZ]
        exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hba, ⟨x, hx⟩⟩⟩
      subst b
      refine ⟨x, ?_, hx⟩
      rw [← ht₁]
      exact (nonvanishing_tensorPullback (i a) (M.tensorPow m) t x).2 (hx ▸ hy)
    · rintro ⟨x, hx, rfl⟩
      apply (nonvanishing_tensorPullback (i a) (M.tensorPow m) t x).1
      rwa [ht₁]

end AlgebraicGeometry.Scheme.Modules
