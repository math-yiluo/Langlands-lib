/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Extending bilinear operations from the affine basis

Source: the affine-basis gluing argument in the construction of the associated
graded algebra in Stacks Tag 087Z, with the sheaf axiom (Tag 0072).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

/-- Sections of a module sheaf agree if they agree on every affine subopen.
Source: Stacks Tag 0072, sheaf separatedness, and the affine basis of a scheme.
Proof: Cover U by all its affine subopens and apply sheaf separatedness. The
basis property supplies a cover also when U is empty. -/
theorem sections_eq_of_affine {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (a b : Γ(M, U))
    (h : ∀ (V : X.affineOpens) (hVU : V.1 ≤ U),
      M.presheaf.map (homOfLE hVU).op a = M.presheaf.map (homOfLE hVU).op b) :
    a = b := by
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U
    (fun i ↦ homOfLE i.2) ?_ _ _ (fun i ↦ h i.1 i.2)
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩

/-- Natural bilinear operations on the affine basis extend to all opens.
Source: Stacks Tags 087Z and 0072, affine-basis descent.
(blueprint: lem-weil-pbc-affine-bilinear-extension).

Proof: For sections a and b on U, restrict to all affine opens V contained in U
and apply beta V. On an overlap, restrict further to every affine open W in the
overlap; naturality and the presheaf composition law show that both outputs
restrict to beta W of the same inputs. Sheaf separatedness on the affine basis
therefore proves compatibility on the whole overlap. Glue uniquely to U.
Uniqueness shows restriction compatibility, by comparing on each affine open
contained in the smaller open. It also proves additivity and scalar linearity
in each input: compare the two sides on the affine basis, using bilinearity of
beta and semilinearity of the restrictions. Package these four identities as
curried linear maps. For affine U the glued section is beta U by uniqueness.
The empty open is covered by the empty family and has a unique section; no
separatedness or quasi-separatedness assumption on X is needed. -/
theorem affineBilinear_extension {X : Scheme.{u}} (M N P : X.Modules)
    (beta : ∀ V : X.affineOpens,
      M.val.obj (op V.1) →ₗ[Γ(X, V.1)] N.val.obj (op V.1) →ₗ[Γ(X, V.1)]
        P.val.obj (op V.1))
    (hbeta : ∀ (V W : X.affineOpens) (h : W.1 ≤ V.1)
      (a : M.val.obj (op V.1)) (b : N.val.obj (op V.1)),
      P.val.map (homOfLE h).op (beta V a b) =
        beta W (M.val.map (homOfLE h).op a) (N.val.map (homOfLE h).op b)) :
    ∃ mu : ∀ U : X.Opens,
      M.val.obj (op U) →ₗ[Γ(X, U)] N.val.obj (op U) →ₗ[Γ(X, U)] P.val.obj (op U),
      (∀ (U V : X.Opens) (h : V ≤ U)
        (a : M.val.obj (op U)) (b : N.val.obj (op U)),
        P.val.map (homOfLE h).op (mu U a b) =
          mu V (M.val.map (homOfLE h).op a) (N.val.map (homOfLE h).op b)) ∧
      (∀ (V : X.affineOpens) (a : M.val.obj (op V.1)) (b : N.val.obj (op V.1)),
        mu V.1 a b = beta V a b) := by
  classical
  have hglue (U : X.Opens) (a : Γ(M, U)) (b : Γ(N, U)) :
      ∃ c : Γ(P, U), ∀ (V : X.affineOpens) (hVU : V.1 ≤ U),
        P.presheaf.map (homOfLE hVU).op c =
          beta V (M.presheaf.map (homOfLE hVU).op a)
            (N.presheaf.map (homOfLE hVU).op b) := by
    let A := {V : X.affineOpens // V.1 ≤ U}
    let t (i : A) := beta i.1 (M.presheaf.map (homOfLE i.2).op a)
      (N.presheaf.map (homOfLE i.2).op b)
    have hcover : U ≤ ⨆ i : A, i.1.1 := by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩
    have hcompat : TopCat.Presheaf.IsCompatible P.presheaf (fun i : A ↦ i.1.1) t := by
      intro i j
      apply sections_eq_of_affine P (i.1.1 ⊓ j.1.1)
      intro W hW
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      change P.val.map (homOfLE (hW.trans inf_le_left)).op (t i) =
        P.val.map (homOfLE (hW.trans inf_le_right)).op (t j)
      dsimp [t]
      rw [hbeta, hbeta]
      change beta W
          (M.presheaf.map (homOfLE (hW.trans inf_le_left)).op
            (M.presheaf.map (homOfLE i.2).op a))
          (N.presheaf.map (homOfLE (hW.trans inf_le_left)).op
            (N.presheaf.map (homOfLE i.2).op b)) =
        beta W
          (M.presheaf.map (homOfLE (hW.trans inf_le_right)).op
            (M.presheaf.map (homOfLE j.2).op a))
          (N.presheaf.map (homOfLE (hW.trans inf_le_right)).op
            (N.presheaf.map (homOfLE j.2).op b))
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    obtain ⟨c, hc, _⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨P.presheaf, P.isSheaf⟩
      (fun i : A ↦ i.1.1) U (fun i ↦ homOfLE i.2) hcover t hcompat
    exact ⟨c, fun V hVU ↦ hc ⟨V, hVU⟩⟩
  choose g hg using hglue
  have hadd_right (U : X.Opens) (a : Γ(M, U)) (b c : Γ(N, U)) :
      g U a (b + c) = g U a b + g U a c := by
    apply sections_eq_of_affine P U
    intro V hVU
    simp only [map_add, hg]
  have hsmul_right (U : X.Opens) (a : Γ(M, U)) (r : Γ(X, U)) (b : Γ(N, U)) :
      g U a (r • b) = r • g U a b := by
    apply sections_eq_of_affine P U
    intro V hVU
    simp only [Scheme.Modules.map_smul, hg, LinearMap.map_smul]
  have hadd_left (U : X.Opens) (a b : Γ(M, U)) (c : Γ(N, U)) :
      g U (a + b) c = g U a c + g U b c := by
    apply sections_eq_of_affine P U
    intro V hVU
    simp only [map_add, hg, LinearMap.add_apply]
  have hsmul_left (U : X.Opens) (r : Γ(X, U)) (a : Γ(M, U)) (b : Γ(N, U)) :
      g U (r • a) b = r • g U a b := by
    apply sections_eq_of_affine P U
    intro V hVU
    simp only [Scheme.Modules.map_smul, hg, LinearMap.map_smul,
      LinearMap.smul_apply]
  let mu (U : X.Opens) : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(P, U) :=
    { toFun := fun a ↦
        { toFun := g U a
          map_add' := hadd_right U a
          map_smul' := hsmul_right U a }
      map_add' := fun a b ↦ LinearMap.ext (hadd_left U a b)
      map_smul' := fun r a ↦ LinearMap.ext (hsmul_left U r a) }
  refine ⟨mu, ?_, ?_⟩
  · intro U V hVU a b
    change P.presheaf.map (homOfLE hVU).op (g U a b) =
      g V (M.presheaf.map (homOfLE hVU).op a) (N.presheaf.map (homOfLE hVU).op b)
    apply sections_eq_of_affine P V
    intro W hWV
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    change P.presheaf.map (homOfLE (hWV.trans hVU)).op (g U a b) =
      P.presheaf.map (homOfLE hWV).op
        (g V (M.presheaf.map (homOfLE hVU).op a) (N.presheaf.map (homOfLE hVU).op b))
    rw [hg, hg]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  · intro V a b
    have h := hg V.1 a b V le_rfl
    change g V.1 a b = beta V a b
    simpa using h


end AlgebraicGeometry
