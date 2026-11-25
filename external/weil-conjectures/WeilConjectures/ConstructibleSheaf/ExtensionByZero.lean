/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.OpenClosedStratification

/-!
# Extension by zero and closed pushforward of constructible sheaves

The open–closed dévissage of `WeilConjectures.ConstructibleSheaf.OpenClosed` is phrased for a
complementary pair `(j, i)` of an open and a closed immersion. Here the second member of the
pair is constructed:

- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact`
  (blueprint `proposition-six-operations-dctf--6`): the extension by zero `j_! F` of a constructible
  sheaf along a quasi-compact open immersion `j` is constructible; the complement is the closed
  complement `j.closedComplement`.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.lowerStar_of_isClosedImmersion_of_quasiCompact`
  (blueprint `proposition-proper-direct-image-finite-coefficients`, sheaf part): the pushforward
  `i_* G` of a constructible sheaf along a closed immersion `i` with quasi-compact open complement
  is constructible.

Quasi-compactness of the open immersion (retrocompactness of its range) is needed because
constructible sheaves are defined via stratifications by *constructible* locally closed subsets;
on a non-Noetherian scheme the extension by zero of the constant sheaf along a non-quasi-compact
open immersion is not constructible. It is automatic on a locally Noetherian scheme, where every
open immersion is quasi-compact (an instance of Mathlib), which covers the schemes of finite type
over a field of the blueprint.
-/

@[expose] public section

universe u u'

open CategoryTheory Limits
open AlgebraicGeometry.Etale

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
  {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- Blueprint `proposition-six-operations-dctf--6`: Extension by zero preserves constructibility.

Let `j : U ⟶ X` be an open immersion and `F` a constructible sheaf on `U_ét`. Then `j_! F` is
constructible on `X_ét`. The open immersion is assumed quasi-compact, which is automatic on a
locally Noetherian scheme and is needed for the strata of `U` to remain constructible subsets
of `X`, see the module docstring. -/
theorem IsConstructibleSheaf.openImmersionLowerShriek_of_quasiCompact {U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (F : Sheaf U.smallEtaleTopology A)
    [IsConstructibleSheaf F] : IsConstructibleSheaf ((j)_!open[A].obj F) :=
  IsConstructibleSheaf.openImmersionLowerShriek j j.closedComplement
    j.range_closedComplement F

variable [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

/-- Blueprint `proposition-proper-direct-image-finite-coefficients`, constructibility part: closed
immersions preserve constructibility.

Let `i : Z ⟶ X` be a closed immersion and `G` a constructible sheaf on `Z_ét`. Then `i_* G` is
constructible on `X_ét`. The open complement of `i` is assumed quasi-compact, which is automatic
on a locally Noetherian scheme, see the module docstring. The vanishing of the higher direct
images is `AlgebraicGeometry.Etale.isConstructibleSheaf_lowerStar_of_isClosedImmersion`. -/
theorem IsConstructibleSheaf.lowerStar_of_isClosedImmersion_of_quasiCompact {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact (openComplementOfIsClosedImmersion i).ι]
    [Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (G : Sheaf Z.smallEtaleTopology A) [IsConstructibleSheaf G] :
    IsConstructibleSheaf ((i)_*[A].obj G) :=
  IsConstructibleSheaf.lowerStar_of_isClosedImmersion (openComplementOfIsClosedImmersion i).ι i
    (by simp [openComplementOfIsClosedImmersion]) G

end AlgebraicGeometry.Scheme

end
