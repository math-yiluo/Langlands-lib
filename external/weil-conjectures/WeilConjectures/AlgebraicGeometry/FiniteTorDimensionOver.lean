/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Finite Tor dimension over the inverse-image structure sheaf

Source: Stacks Project, Tags 08CG and 08EV, hypothesis (3)
(blueprint: def-pc-finite-tor-dimension-over).
-/

@[expose] public section

universe u₀ w₀

open CategoryTheory CategoryTheory.Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Finite Tor dimension of `E` after forgetting scalars from `𝒪_X` to `f⁻¹𝒪_S`.
Choose a complex `K` representing `E`, restrict its scalars along the structure map
`f⁻¹𝒪_S → 𝒪_X` (`Modules.tensorPullbackRingMap f`), and choose a K-flat resolution
`q : P ⟶ K|_{f⁻¹𝒪_S}` (a quasi-isomorphism from a K-flat complex of `f⁻¹𝒪_S`-modules).
One finite interval `[a, b]` bounds the cohomology of the total tensor `P ⊗ F[0]` over
`f⁻¹𝒪_S` for every `f⁻¹𝒪_S`-module sheaf `F`; this complex computes
`E ⊗^L_{f⁻¹𝒪_S} F` (Tags 06YS, 06YU), so the choices of `K` and `P` do not matter.
Source: Stacks Project, Definition 20.48.1 (08CG), applied to `(X,f⁻¹𝒪_S)` as in
Lemma 36.27.1 (08EV), hypothesis (3) (blueprint: def-pc-finite-tor-dimension-over). -/
def HasFiniteTorDimensionOver {X S : Scheme.{u₀}} (f : X ⟶ S)
    [HasDerivedCategory.{w₀} (SheafOfModules.{u₀} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X) : Prop :=
  ∃ K : CochainComplex (SheafOfModules.{u₀} (moduleRings X.toRingedSpace)) ℤ,
    Nonempty (DerivedCategory.Q.obj K ≅ E) ∧
    ∃ P : CochainComplex (SheafOfModules.{u₀} ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u₀} RingCat.{u₀})).obj
          (TopCat.Sheaf.inverseImageRing f.base S.sheaf))) ℤ,
      CochainComplex.IsKFlatTensor (R := TopCat.Sheaf.inverseImageRing f.base S.sheaf) P ∧
      ∃ q : P ⟶ ((SheafOfModules.restrictScalars
          ((sheafCompose (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u₀} RingCat.{u₀})).map
              (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K,
        QuasiIso q ∧
        ∃ a b : ℤ, a ≤ b ∧
          ∀ F : SheafOfModules.{u₀} ((sheafCompose (Opens.grothendieckTopology X)
              (forget₂ CommRingCat.{u₀} RingCat.{u₀})).obj
                (TopCat.Sheaf.inverseImageRing f.base S.sheaf)),
            ∀ i : ℤ, i < a ∨ b < i →
              IsZero ((CochainComplex.mapBifunctor P
                ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                (@curriedTensor _ _ (SheafOfModules.monoidalCategory
                  (TopCat.Sheaf.inverseImageRing f.base S.sheaf)))).homology i)

end AlgebraicGeometry.Scheme
