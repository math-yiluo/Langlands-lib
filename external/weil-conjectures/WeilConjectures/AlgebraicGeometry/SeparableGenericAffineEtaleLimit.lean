/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.SeparableClosure
import WeilConjectures.AlgebraicGeometry.SeparableGenericAffineEtaleStages
import WeilConjectures.AlgebraicGeometry.SeparableGenericAffineEtaleLimitCompletion

/-!
# The separable generic point as an affine étale inverse limit

Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), Tag 03QL
(theorem-henselization), and Tag 0032 (lemma-directed-category-system).
(blueprint: lem-pd-separable-generic-affine-etale-limit)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A specified separable generic point is presented by affine étale stages.

Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), Tag 03QL
(theorem-henselization, clauses (3),(4)), Tag 0032 (lemma-directed-category-system).
The vertex is fixed to be the specified `Spec (separableClosure F Ω)`, and the final
equality records that its map to `S` is the canonical generic-point map.

Proof (node steps):
1. Choose an affine open `U = Spec R ⊆ S` containing the generic point. The affine
   pointed étale neighbourhoods of the geometric generic point `Spec Ω → S` form a
   cofiltered category, and those factoring through `U` are initial
   (lem-weil-pbc-etale-local-ring-triples); def-weil-pbc-strict-henselization-limit
   identifies the spectrum of the coordinate-ring colimit with the inverse limit.
2. On the small cofiltered category `J` of these neighbourhoods, the spectrum of the
   colimit is a limit of the forgetful diagram (lem-weil-pbc-spec-small-colimit-limit).
   The directed reindexing lem-weil-pbc-cofiltered-limit-directed-reindex gives a
   nonempty directed `I`, stages `S_i` and pointed transitions `v_ji` whose restricted
   cone is still a limit. Each `S_i` is affine and étale over `S`, each `v_ji` is an
   `S`-morphism between affine schemes, hence affine.
3. By lem-weil-pbc-strict-henselization-triples at `R = Γ(U, 𝒪_U)`, the generic prime
   `(0)` and `K = F^s`, the colimit ring `C` has a surjection `ψ : C → F^s` with
   `𝔪_C = ker ψ = 0`, so `ψ` is the canonical identification `C ≅ F^s` and the vertex
   is `Spec F^s` (def-weil-pbc-strict-henselization-point-evaluation).
4. By lem-weil-pbc-strict-henselization-point-evaluation-pointed the evaluation map
   composed with each cone leg is the chosen geometric point of the stage, so composing
   with `u_i` gives the original map `Spec F^s → Spec F → S`; the transition and
   compatibility identities are those of the inverse-system cone.
(blueprint: lem-pd-separable-generic-affine-etale-limit) -/
theorem exists_separableGeneric_affineEtale_limit
    (S : Scheme.{u}) [IsIntegral S]
    (Ω : Type u) [Field Ω] [Algebra S.functionField Ω]
    [IsAlgClosure S.functionField Ω] :
    let F := S.functionField
    let Fs := separableClosure F Ω
    let X := Spec (CommRingCat.of Fs)
    let g : X ⟶ S :=
      Spec.map (CommRingCat.ofHom (algebraMap F Fs)) ≫ S.fromSpecFunctionField
    ∃ (I : Type u) (_ : Nonempty I) (_ : Preorder I)
      (_ : IsDirected I (· ≤ ·))
      (D : Iᵒᵖ ⥤ Scheme.{u})
      (π : ∀ i : Iᵒᵖ, X ⟶ D.obj i)
      (hπ : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), π j = π i ≫ D.map f)
      (u : ∀ i : I, D.obj (op i) ⟶ S)
      (_hc : IsLimit
        ({ pt := X
           π := { app := π
                  naturality := by
                    intro i j f
                    exact hπ f } } : Cone D)),
      (∀ i : I, IsAffine (D.obj (op i))) ∧
      (∀ i : I, Etale (u i)) ∧
      (∀ {i j : I} (h : i ≤ j),
        u j = D.map (homOfLE h).op ≫ u i) ∧
      (∀ {i j : I} (h : i ≤ j),
        IsAffineHom (D.map (homOfLE h).op)) ∧
      (∀ i : I, π (op i) ≫ u i = g) := by
  dsimp
  let F := S.functionField
  let Fs := separableClosure F Ω
  let X := Spec (CommRingCat.of Fs)
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  let η : Spec (CommRingCat.of Ω) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap F Ω)) ≫ S.fromSpecFunctionField
  let J := SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods η)
  let : SmallCategory J := inferInstance
  let D₀ := (Scheme.strictHenselizationAffineDiagram η).op ⋙ Scheme.Spec
  obtain ⟨A, hpre, hdir, hne, R, hR, π₀, u, hrest⟩ :=
    exists_separableGeneric_affineEtale_stages S Ω
  have hπ₀ : ∀ {i j : Aᵒᵖ} (f : i ⟶ j),
      π₀ j = π₀ i ≫ (R.op ⋙ D₀).map f := hrest.1
  have haff : ∀ i : A, IsAffine ((R.op ⋙ D₀).obj (op i)) := hrest.2.1
  have het : ∀ i : A, Etale (u i) := hrest.2.2.1
  have htrans : ∀ {i j : A} (h : i ≤ j),
      u j = (R.op ⋙ D₀).map (homOfLE h).op ≫ u i := hrest.2.2.2.1
  have haffhom : ∀ {i j : A} (h : i ≤ j),
      IsAffineHom ((R.op ⋙ D₀).map (homOfLE h).op) := hrest.2.2.2.2.1
  have hπcan : ∀ j : Aᵒᵖ,
      π₀ j = (Scheme.strictHenselizationCone η).π.app (R.op.obj j) :=
    hrest.2.2.2.2.2.1
  have hucan : ∀ i : A,
      u i =
        Spec.map (Scheme.ΓSpecIso
          (Opposite.unop ((equivSmallModel
            (Scheme.strictHenselizationNeighbourhoods η)).inverse.obj
              (Opposite.unop (R.obj i))).1.left)).inv ≫
          ((Scheme.AffineEtale.Spec S).obj
            ((equivSmallModel
              (Scheme.strictHenselizationNeighbourhoods η)).inverse.obj
              (Opposite.unop (R.obj i))).1).hom :=
    hrest.2.2.2.2.2.2
  obtain ⟨e, hEval, hc⟩ := separableGeneric_affineEtale_limit S Ω A hpre hdir hne
    R hR π₀ hπcan
  have hp := separableGeneric_affineEtale_pointed S Ω A hpre hdir hne R π₀ u e hEval
    hπcan hucan
  let π : ∀ i : Aᵒᵖ, X ⟶ (R.op ⋙ D₀).obj i :=
    fun i ↦ Spec.map (CommRingCat.ofHom e.toRingHom) ≫ π₀ i
  have hπ : ∀ {i j : Aᵒᵖ} (f : i ⟶ j),
      π j = π i ≫ (R.op ⋙ D₀).map f := by
    intro i j f
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ π₀ j =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ π₀ i ≫ (R.op ⋙ D₀).map f
    simpa only [Category.assoc] using
      congrArg (fun q ↦ Spec.map (CommRingCat.ofHom e.toRingHom) ≫ q) (hπ₀ f)
  refine ⟨A, hne, hpre, hdir, R.op ⋙ D₀, π, hπ, u, ?_, ?_⟩
  · convert Classical.choice hc using 1
  · exact ⟨haff, het, htrans, haffhom, hp⟩

end AlgebraicGeometry
