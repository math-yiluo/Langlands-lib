# Presheaf tensor products and sections of tensor products

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.TwistCechBridge` (namespace
`Langlands.AlgebraicGeometry.Modules.CechBridge`) builds two morphisms of FLT presheaves on affine
opens (`OModulePresheaf.AffHom`), used to compare FLT Čech cohomology of twisted presheaves with
cohomology of tensor products of modules. It contains only internal helper declarations.

- `tensorSectionsAffHom F M : (ofModules q F).tensor (ofModules q M) ⟶ ofModules q (F ⊗ M)`: on an
  affine open `U`, the linear extension of the FLT sectionwise tensor map
  `Scheme.Modules.tensorSectionsBilin F M U` (`s ⊗ t ↦ s ⊗ t`). Naturality is the FLT
  `map_homOfLE_tensorSections`.
  `tensorSectionsAffHom_bijective`: for invertible `F` and `M` it is bijective on every affine
  open (FLT `IsInvertible.bijective_lift_tensorSectionsBilin_monoidalV2`).
- `tensorRightAffHom F' G H e he : F'.tensor G ⟶ F'.tensor H`: tensoring on the right with a
  natural family of `Γ(X, U)`-linear maps `e U : G(U) → H(U)`. `tensorRightAffHom_bijective`: it
  is bijective on every affine open where `e U` is bijective.

The `A`-module structures on sections are those of the FLT presheaves (through
`Scheme.TwoAffineOpenCover.algebraOfHom`). The module uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
