/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Positive tensor products of families and their sections

Source: Stacks Project, Varieties, Tag 09NC, displayed tensor construction
(blueprint: def-sc-positive-tensor-family).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Left-associated tensor product of a nonempty ordered family. Source: Stacks, Tag 09NC
(blueprint: def-sc-positive-tensor-family). The parameter `n` means `n + 1` factors. -/
noncomputable def positiveTensorFamily {X : Scheme.{u}} :
    (n : ℕ) → (Fin (n + 1) → X.Modules) → X.Modules
  | 0, L => L 0
  | n + 1, L => positiveTensorFamily n (fun i ↦ L i.castSucc) ⊗ L (Fin.last (n + 1))

/-- The pointwise tensor of compatible sections is compatible with restriction.
Source: Stacks, Tag 09NC (blueprint: def-sc-positive-tensor-family).
Proof: apply `tmulSection_map` to each restriction, then the compatibility equations
of the two section families. A morphism in the opposite category of opens is precisely
an inclusion in the reverse direction. -/
theorem tensorGlobalSections_naturality {X : Scheme.{u}} {M N : X.Modules}
    (s : M.sections) (t : N.sections) {U V : X.Opensᵒᵖ} (f : U ⟶ V) :
    (M ⊗ N).val.map f (tmulSection (s.val U) (t.val U)) =
      tmulSection (s.val V) (t.val V) := by
  have hf : (homOfLE (leOfHom f.unop)).op = f := Subsingleton.elim _ _
  have h := tmulSection_map (leOfHom f.unop) (s.val U) (t.val U)
  rw [hf] at h
  change (M ⊗ N).val.map f (tmulSection (s.val U) (t.val U)) =
    tmulSection (M.val.map f (s.val U)) (N.val.map f (t.val U)) at h
  simpa only [PresheafOfModules.sections_property] using h

/-- Tensor product of two global sections, evaluated on every open.
Source: Stacks, Tag 09NC (blueprint: def-sc-positive-tensor-family). -/
noncomputable def tensorGlobalSections {X : Scheme.{u}} {M N : X.Modules}
    (s : M.sections) (t : N.sections) : (M ⊗ N).sections :=
  PresheafOfModules.sectionsMk (fun U ↦ tmulSection (s.val U) (t.val U))
    (fun {_ _} f ↦ tensorGlobalSections_naturality s t f)

/-- Left-associated tensor of one global section from each factor.
Source: Stacks, Tag 09NC (blueprint: def-sc-positive-tensor-family). -/
noncomputable def positiveTensorFamilySection {X : Scheme.{u}} :
    (n : ℕ) → (L : Fin (n + 1) → X.Modules) →
      ((i : Fin (n + 1)) → (L i).sections) → (positiveTensorFamily n L).sections
  | 0, _, s => s 0
  | n + 1, L, s => tensorGlobalSections
      (positiveTensorFamilySection n (fun i ↦ L i.castSucc) (fun i ↦ s i.castSucc))
      (s (Fin.last (n + 1)))

end AlgebraicGeometry.Scheme.Modules
