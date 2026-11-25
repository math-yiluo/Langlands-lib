/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTrace
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegreeTrace
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant

/-!
# Degree and trace of a finite étale cover

Source: Stacks Project, Section 03SH, after Definition 03SE
(blueprint: lem-weil-pbc-finite-etale-trace-degree).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- (blueprint: lem-weil-pbc-finite-etale-trace-degree)
A finite étale morphism over a connected scheme has constant degree; its geometric fibres
have that cardinality, and restriction followed by trace is multiplication by the degree. Source:
Stacks Project, Section 03SH, after Definition 03SE (blueprint:
lem-weil-pbc-finite-etale-trace-degree).

Proof (the node's eight steps):
1. Finiteness and étaleness give finiteness, flatness, and local finite presentation
   (definition-ind-etale-pro-etale-weakly--3, def-weil-etale-morphism), which is finite local
   freeness (def-pc-finite-locally-free; Stacks 02KB).
2. The fibre degree is locally constant by
   lem-weil-pbc-finite-locally-free-degree-locally-constant (Stacks 04MH). Choose a point
   of the nonempty connected base; its degree d has a nonempty clopen level set, whose
   clopen complement must be empty (def-weil-connected-scheme). This proves (a).
3. Work in an affine chart about the image of a geometric point. The fibre rings are
   A tensor kappa(x) and A tensor Omega (lem-weil-pbc-open-fibre-product and
   lem-weil-pbc-fibre-product-affine-spectra). A basis remains a basis on field extension,
   so the geometric fibre has dimension d (def-weil-geometric-point).
4. By lem-galois-geometric-fibre, that fibre is a finite coproduct of copies of Spec Omega.
   Its global sections are Omega to the power of the number of copies, so the dimension
   in step 3 forces that number to be d. Its underlying space has exactly d points: (b).
5. Use lem-weil-pbc-finite-etale-etale-local-split (Stacks 04HN) at each base point.
   A geometric point above the distinguished point counts the local summands, using
   (b) and Cartesian pasting (def-pc-fibre-product). Hence there are d summands.
   Gluing along these disjoint opens gives a coproduct of d copies of the neighbourhood
   (definition-torsion-sheaves--3).
6. Under lem-weil-pbc-etale-inverse-image-restriction, restriction on a site object W
   is restriction along W times_X Y to W. Cartesian pasting identifies this projection
   with the corresponding projection after localisation. The trace commutes with the
   same localisation by lem-weil-pbc-finite-etale-trace-exists, property (1).
7. The sheaf condition identifies sections over the split cover with the d-fold product
   (situation-conventions). Restriction is the diagonal, and trace is the
   sum by lem-weil-pbc-finite-etale-trace-exists, property (2). Their composite is d times
   the identity; this also holds for the empty family, whose sections are zero.
8. Pull back the jointly surjective splitting neighbourhoods to each site object
   (lem-weil-pbc-etale-covering-base-change). The difference between the composite and
   d times the identity restricts to zero on this covering by steps 6 and 7. Sheaf
   separatedness makes the difference zero globally, proving (c).
-/
theorem exists_finiteEtaleTrace_degree
    {X Y : Scheme.{u}} [ConnectedSpace X] (f : Y ⟶ X) [IsFinite f] [Etale f] :
    ∃ d : ℕ, ∃ (_ : f.IsFiniteLocallyFreeOfDegree d),
      (∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ X),
        Finite ↥(pullback f x : Scheme.{u}) ∧
          Nat.card ↥(pullback f x : Scheme.{u}) = d ∧
          Nonempty (Over.mk (pullback.snd f x) ≅
            Over.mk (Sigma.desc fun _ : Fin d ↦ 𝟙 (Spec (.of Ω))))) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
        finiteEtaleRestriction f F ≫ finiteEtaleTrace f F = d • 𝟙 F := by
  classical
  let : f.IsFiniteLocallyFree := {}
  obtain ⟨_, hδ, _⟩ := finiteLocallyFree_fiberDimension_isLocallyConstant f
  let x₀ : X := Classical.arbitrary X
  let d := f.fiberDegree x₀
  have hd (x : X) : f.fiberDegree x = d :=
    hδ.apply_eq_of_preconnectedSpace x x₀
  let : f.IsFiniteLocallyFreeOfDegree d := { fiberDegree_eq := hd }
  refine ⟨d, inferInstance, ?_, finiteEtaleTrace_comp_restriction f d⟩
  intro Ω _ _ x
  let z : Spec (.of Ω) := Classical.arbitrary _
  have hr : (pullback.snd f x).finrankΓ = d := by
    rw [← fiberDegree_eq_finrankΓ _ z,
      Scheme.Hom.fiberDegree_of_isPullback f (.of_hasPullback f x)]
    exact hd _
  obtain ⟨ι, hι, hcard, ⟨e⟩⟩ := f.exists_overIso_sigma_of_isSepClosed x
  let := hι
  let := Fintype.ofFinite ι
  have hc : Fintype.card ι = d := by simpa using hcard.trans hr
  let r : ι ≃ Fin d := (Fintype.equivFin ι).trans (finCongr hc)
  let q : (∐ fun _ : ι ↦ Spec (.of Ω)) ≅
      (∐ fun _ : Fin d ↦ Spec (.of Ω)) :=
    Sigma.whiskerEquiv (f := fun _ : ι ↦ Spec (.of Ω))
      (g := fun _ : Fin d ↦ Spec (.of Ω)) r (fun _ ↦ Iso.refl _)
  have hq : q.hom ≫ (Sigma.desc fun _ : Fin d ↦ 𝟙 (Spec (.of Ω))) =
      Sigma.desc fun _ : ι ↦ 𝟙 (Spec (.of Ω)) := by
    apply Sigma.hom_ext
    intro j
    simp [q, Sigma.whiskerEquiv_hom, Sigma.map']
  let e' : Over.mk (pullback.snd f x) ≅
      Over.mk (Sigma.desc fun _ : Fin d ↦ 𝟙 (Spec (.of Ω))) :=
    e ≪≫ Over.isoMk q hq
  let ep : ↥(pullback f x) ≃ ↥(∐ fun _ : ι ↦ Spec (.of Ω)) :=
    { toFun := e.hom.left.base
      invFun := e.inv.left.base
      left_inv := fun t ↦ by
        have h := congrArg (fun k ↦ k.left.base t) e.hom_inv_id
        exact h
      right_inv := fun t ↦ by
        have h := congrArg (fun k ↦ k.left.base t) e.inv_hom_id
        exact h }
  let es := (sigmaMk (fun _ : ι ↦ Spec (.of Ω))).symm.toEquiv
  have : Unique (Spec (.of Ω)) := inferInstance
  let ec : (Σ _ : ι, Spec (.of Ω)) ≃ ι :=
    { toFun := fun t ↦ t.1
      invFun := fun j ↦ ⟨j, default⟩
      left_inv := fun t ↦ by
        exact Sigma.ext (by rfl) (heq_of_eq (Subsingleton.elim _ _))
      right_inv := fun _ ↦ rfl }
  let ee := ep.trans (es.trans (ec.trans r))
  exact ⟨Finite.of_equiv (Fin d) ee.symm, by simpa using Nat.card_congr ee, ⟨e'⟩⟩

end AlgebraicGeometry.Etale
