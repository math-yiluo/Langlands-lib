/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.FinitePresentationAffineChartSectionsModel
import WeilConjectures.AlgebraicGeometry.FinitePresentationAffineSectionsRealization
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Object models on one fixed affine chart

Source: Stacks Project, Limits, Tag 01ZR, first proof, affine case;
Algebra, Tag 05N7, object clause.
(blueprint: lem-pc-fp-affine-chart-object-models). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finitely presented module has a model at one finite stage on a fixed affine chart.
No finiteness of the cover or of the ambient morphism is needed.
Source: Stacks Project, Limits, Tag 01ZR, first proof, affine case;
Algebra, Tag 05N7, object clause.
(blueprint: lem-pc-fp-affine-chart-object-models).

Proof: Work on the upper tail above i, replacing its directed preorder by its
partial-order quotient. This tail is nonempty because it contains i. For the
fixed affine chart V.X a, its base changes have rings
Gamma(V.X a) tensor_{R_i} R_j. Tensor products commute with directed colimits.
The affine spectrum functor takes ring colimits to limits; uniqueness of the
limit and the affine pullback comparison identify the limit chart ring with
this colimit. Restrict M to the limit chart. Its quasi-coherence and finite
presentation identify its sections with a finitely presented module over that
ring. Choose a finite free presentation, lift the finitely many entries of
its relation matrix to a stage k above i, and take the cokernel of the lifted
matrix. This is a genuine finite-presentation module, not an unspecified
chosen sheaf. Its associated sheaf pulls back to the restriction of M by the
affine module equivalence and the tensor-pullback comparison. For any j above
k extend this cokernel along the stage ring map. Finite presentation and
quasi-coherence are preserved. Associativity of scalar extension, followed
by the original comparison, gives the asserted isomorphism on the iterated
pullback chart. Equivalent indices give canonically isomorphic rings, so the
construction descends back from the partial-order quotient. Empty charts,
zero rings and zero modules use the same cokernel construction. -/
theorem exists_finitePresentation_affine_chart_object_models
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (M : (pullback f (c.π.app (op i))).Modules)
    (hM : M.IsFinitePresentation) (hMq : M.IsQuasicoherent)
    (V : Xi.OpenCover.{u}) (a : V.I₀) (ha : IsAffine (V.X a)) :
    ∃ (j : I) (hij : i ≤ j),
      let U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u} :=
        V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE hij))))
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
      ∃ N : (U.X a).Modules,
        N.IsFinitePresentation ∧ N.IsQuasicoherent ∧
        Nonempty ((Scheme.Modules.pullback (U.pullbackHom p a)).obj N ≅
          (Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M) := by
  obtain ⟨j, hij, Q, hQ, e⟩ :=
    exists_finitePresentation_affine_chart_sections_model R c hc i f M hM hMq V a ha
  let U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u} :=
    V.pullback₁ (pullback.fst f (Spec.map (R.map (homOfLE hij))))
  let p := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
  have : IsAffine (V.X a) := ha
  have hstage : IsAffineHom (Spec.map (R.map (homOfLE hij))) := inferInstance
  have hfst : IsAffineHom (pullback.fst f (Spec.map (R.map (homOfLE hij)))) :=
    MorphismProperty.pullback_fst _ _ hstage
  have hU : IsAffine (U.X a) := by
    change IsAffine (pullback (pullback.fst f _) (V.f a))
    exact isAffine_of_isAffineHom (pullback.snd _ _)
  have : IsAffine (U.X a) := hU
  have hcmap : IsAffineHom (c.π.app (op j)) := by
    exact @isAffineHom_of_isAffine c.pt (Spec (R.obj j)) (c.π.app (op j))
      ‹IsAffine c.pt› inferInstance
  have hp : IsAffineHom p := by
    dsimp [p]
    exact MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).flip hcmap
  have hY : IsAffine ((U.pullback₁ p).X a) := by
    change IsAffine (pullback p (U.f a))
    exact isAffine_of_isAffineHom (pullback.snd _ _)
  have : IsAffine ((U.pullback₁ p).X a) := hY
  have : M.IsQuasicoherent := hMq
  refine ⟨j, hij, ?_⟩
  exact exists_finitePresentation_affine_sections_realization (U.pullbackHom p a)
    ((Scheme.Modules.pullback ((U.pullback₁ p).f a)).obj M) (by infer_instance) Q hQ e

end AlgebraicGeometry
