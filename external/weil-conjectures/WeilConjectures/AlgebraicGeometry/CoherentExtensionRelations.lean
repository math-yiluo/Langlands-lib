/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeKernelOver
import WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeSubKernel

/-! # Coherent ExtensionRelations

Source: Stacks Project, Modules, Lemma 01BY
(blueprint: lem-weil-pbc-coherent-extension-relations).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

private theorem finiteType_of_iso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ V, HasWeakSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (e : F ≅ G) (hF : F.IsFiniteType) :
    G.IsFiniteType := by
  obtain ⟨d, hd⟩ := hF.exists_localGeneratorsData
  have : d.IsFiniteType := hd
  let d' : G.LocalGeneratorsData :=
    { I := d.I
      X := d.X
      coversTop := d.coversTop
      generators i := (d.generators i).ofEpi (e.hom.over (d.X i)) }
  refine ⟨⟨d', ?_⟩⟩
  constructor
  intro i
  have := hd.isFiniteType i
  dsimp [d']
  infer_instance

private theorem extension_kernel_iso {C : Type*} [Category C] [Abelian C]
    (T : ShortComplex C) (hT : T.ShortExact) {A : C} (g : A ⟶ T.X₂) :
    ∃ φ : kernel (g ≫ T.g) ⟶ T.X₁, Nonempty (kernel φ ≅ kernel g) := by
  have : Mono T.f := hT.mono_f
  let q := g ≫ T.g
  let k := kernel.ι q
  let φ : kernel q ⟶ T.X₁ := hT.fIsKernel.lift
    (KernelFork.ofι (k ≫ g) (by simp [q, k, Category.assoc]))
  have fac : φ ≫ T.f = k ≫ g := by
    exact Fork.IsLimit.lift_ι hT.fIsKernel
  let a : kernel φ ⟶ kernel g := kernel.lift g (kernel.ι φ ≫ k) (by
    rw [Category.assoc, ← fac, ← Category.assoc, kernel.condition, zero_comp])
  let b₀ : kernel g ⟶ kernel q := kernel.lift q (kernel.ι g) (by
    simp [q])
  have hb : b₀ ≫ φ = 0 := by
    apply (cancel_mono T.f).1
    simp [Category.assoc, fac, b₀, k]
  let b : kernel g ⟶ kernel φ := kernel.lift φ b₀ hb
  let e : kernel φ ≅ kernel g :=
    { hom := a
      inv := b
      hom_inv_id := by
        apply (cancel_mono (kernel.ι φ)).1
        apply (cancel_mono k).1
        simp [a, b, b₀, k, Category.assoc]
      inv_hom_id := by
        apply (cancel_mono (kernel.ι g)).1
        simp [a, b, b₀, k, Category.assoc] }
  exact ⟨φ, ⟨e⟩⟩

/-- Relations in the middle term of an extension of coherent modules are of finite type.
Source: Stacks Project, Modules, Lemma 01BY (lemma-coherent-abelian), proof of (4),
the relation-kernel diagram (blueprint: lem-weil-pbc-coherent-extension-relations).

Proof: Restrict the short exact sequence to U and compose g with the quotient map.
The kernel K3 of this composite is finite type by coherence of the last term,
which remains coherent on restriction to U. The composite of K3 into the middle
term lands in the first term because its image in the last term is zero. Exactness
identifies the kernel K of g with the kernel of this induced map K3 to the first
term on U. The open-slice version of part (2) of Lemma 01BY makes this induced kernel finite
type. The two kernel lifts are inverse by cancellation of their monic inclusions;
transport finite local generating families along the resulting isomorphism.
This assertion concerns only the relation kernels; finite type
of the middle term is supplied separately by Lemma 01B7. -/
theorem coherent_extension_relations (X : RingedSpace.{u})
    (S : ShortComplex (SheafOfModules.{u} (moduleRings X))) (hS : S.ShortExact)
    (h₁ : IsCoherent X S.X₁) (h₃ : IsCoherent X S.X₃)
    (U : Opens X) (n : ℕ)
    (g : SheafOfModules.free (R := (moduleRings X).over U) (ULift.{u} (Fin n)) ⟶
      S.X₂.over U) :
    (kernel g).IsFiniteType := by
  let R := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let T := S.map R
  have hT : T.ShortExact := hS.map_of_exact R
  obtain ⟨φ, ⟨e⟩⟩ := extension_kernel_iso
    (C := SheafOfModules.{u} ((moduleRings X).over U)) T hT g
  have hq : (kernel (g ≫ T.g)).IsFiniteType := h₃.2 U n (g ≫ T.g)
  have hφ : (kernel φ).IsFiniteType :=
    coherent_finiteType_kernel_over X U S.X₁ (kernel (g ≫ T.g)) φ hq h₁
  exact finiteType_of_iso.{u, u, u} e hφ

end AlgebraicGeometry.RingedSpace
