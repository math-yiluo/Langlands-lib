/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu, Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRestriction
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalarsStrictArrow
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientSliceRealization

/-! # K-flatness of fixed scalar chart coordinates

Source: Stacks Project, Tags 03CY, 06YN and 03DH.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme

/-- The fixed-scalar encoding followed by restriction to a weakly etale chart carries K-flat
complexes over the constant ring sheaf to K-flat complexes of sheaves of `B`-modules on the
chart.
Source: Stacks Project, Tags 03CY, 06YN, 0E8K and 03DH.

Proof: restriction of modules to the slice at the chart preserves K-flatness
(`SheafOfModules.ringedSite_restriction_exact_kflat`, Tag 0E8K). Sheaves of `B`-modules on
the chart are identified with modules over the restricted constant ring sheaf by an additive
equivalence compatible with the sheafified tensor products
(`proEtaleSliceRealization_tensor`), which carries the chart coordinates to the slice
restriction (`finiteCoefficientSliceRestrictionRealizationIso`). Such an equivalence preserves
and reflects the acyclic tensor test
(`finiteCoefficientSliceRestriction_acyclicTensorTest`), and the acyclic tensor test gives
K-flatness for quasi-isomorphisms by the symmetry of the tensor product. -/
theorem finiteCoefficientSliceRestriction_kFlat_of_constant
    (X : Scheme.{t}) (B : Type t) [CommRing B]
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1})
    (φ : adicConstantRing X B ⟶ R) (V : X.Etale)
    (K : CochainComplex (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)) ℤ)
    (hK : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X B)
      ((Functor.mapHomologicalComplex (SheafOfModules.restrictScalars.{t + 1}
        ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ))
          (.up ℤ)).obj K)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((finiteCoefficientSliceRestriction X B R φ V).mapHomologicalComplex (.up ℤ)).obj K) := by
  exact ProEt.sheafModule_kFlat_of_acyclicTensorTest B _ _
    (finiteCoefficientSliceRestriction_acyclicTensorTest X B R φ V K hK _ (Iso.refl _))

end AlgebraicGeometry.Scheme
