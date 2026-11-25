/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence

/-!
# Finite étale covers as finite locally constant sheaves

Source: Stacks Project, Tags 03RV, 03Q1, 00Y6 and 09ZB
(blueprint: thm-galois-lc-etale).
These are `AlgebraicGeometry.Scheme.exists_finiteEtale_flc_equivalence` and
`AlgebraicGeometry.Scheme.finiteEtale_flc_preserves_torsors`, stated for the category
`Scheme.FLC`, which is `Scheme.FiniteLocallyConstant`.
-/

@[expose] public section

universe v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- The Yoneda equivalence, with base change and stalk compatibility. This is
`AlgebraicGeometry.Scheme.exists_finiteEtale_flc_equivalence`.
Source: Stacks Project, Tags 03RV, 03Q1, 00Y6 and 09ZB
(blueprint: thm-galois-lc-etale). -/
theorem exists_finiteEtale_flc_equivalence_sheaf (Y : Scheme.{v}) :
    ∃ Φ : Y.FiniteEtale ≌ Y.FLC,
      Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
      (∀ (Ω : Type v) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙
            (pointSmallEtale s).sheafFiber (A := Type (v + 1)) ≅
          FiniteEtale.fiber s ⋙ CategoryTheory.forget FintypeCat.{v} ⋙ uliftFunctor.{v + 1, v})) ∧
      (∀ (X : Scheme.{v}) (f : X ⟶ Y), ∃ Ψ : X.FiniteEtale ≌ X.FLC,
        Nonempty (Ψ.functor ⋙ ObjectProperty.ι _ ≅
          ObjectProperty.ι _ ⋙ X.smallEtaleTopology.uliftYoneda.{v + 1}) ∧
        Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ⋙ etaleSetPullback f ≅
          FiniteEtale.pullback f ⋙ Ψ.functor ⋙ ObjectProperty.ι _)) :=
  exists_finiteEtale_flc_equivalence Y

/-- The Yoneda equivalence carries a finite abelian torsor and its action to its sheaf torsor.
This is `AlgebraicGeometry.Scheme.finiteEtale_flc_preserves_torsors`.
Source: Stacks Project, proof of Tag 09ZB, with Tag 03RV
(blueprint: thm-galois-lc-etale). -/
theorem finiteEtale_flc_preserves_torsors_sheaf {Y : Scheme.{v}}
    (Φ : Y.FiniteEtale ≌ Y.FLC)
    (α : Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{v + 1}) :
    ∀ (M : Type (v + 1)) [AddCommGroup M] [Finite M] (t : EtaleTorsor M Y),
      ∃ ε : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj ≅ t.toSheafTorsor.sheaf,
        ε = α.app ⟨t.toEtale, t.isFinite⟩ ∧
        ∀ (U : Y.Etale) (m : M)
          (x : (Φ.functor.obj ⟨t.toEtale, t.isFinite⟩).obj.obj.obj (op U)),
          ε.hom.hom.app (op U)
            ((Φ.functor.map (ObjectProperty.homMk
              (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)))).hom.hom.app (op U) x) =
            ⟨(ε.hom.hom.app (op U) x).down ≫
              MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m)⟩ :=
  finiteEtale_flc_preserves_torsors Φ α


end AlgebraicGeometry.Scheme
