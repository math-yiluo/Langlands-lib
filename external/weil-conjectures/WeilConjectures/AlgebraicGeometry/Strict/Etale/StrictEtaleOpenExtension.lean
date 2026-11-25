/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemOpenAssembly

/-! # Ordinary extension by zero for strict coefficient systems

Source: Stacks 03S2, 03DI and 03DJ; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

variable (O : Type (u + 1)) [CommRing O] (t : O)
  {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
  (I : StrictEtaleOrdinaryImage O t j)
  (PX : StrictEtaleEvaluation X O t) (PZ : StrictEtaleEvaluation Z O t)

/-- Ordinary open extension, its evaluation adjunctions and scalar transition equations.
All functors here act on abelian categories, before passing to complexes or localization.
Source: Stacks 03S2, 03DI and 03DJ; Zheng, Construction 4.1
(blueprint: lem-pur-strict-etale-ordinary-open-extension). -/
structure StrictEtaleOrdinaryOpen where
  extension : strictEtaleCoefficientSystem X O t ⥤ strictEtaleCoefficientSystem Z O t
  [additive : extension.Additive]
  exact : PreservesFiniteLimits extension ∧ PreservesFiniteColimits extension
  adjunction : extension ⊣ I.inverse
  level : ∀ n, strictEtaleLevel X O t n ⥤ strictEtaleLevel Z O t n
  [levelAdditive : ∀ n, (level n).Additive]
  levelExact : ∀ n, PreservesFiniteLimits (level n) ∧ PreservesFiniteColimits (level n)
  levelAdjunction : ∀ n, level n ⊣ (I.lift n).modules
  evaluation : ∀ n, extension ⋙ coefficientEvaluation
    (J := Z.smallEtaleTopology) (O := O) (ell := t) n ≅
      coefficientEvaluation (J := X.smallEtaleTopology) (O := O) (ell := t) n ⋙ level n
  evaluationMate : ∀ n, (I.inverseEvaluation n).hom =
    (mateEquiv adjunction (levelAdjunction n) (.mk _ _ _ _ (evaluation n).inv))
  restriction : ∀ {m n : ℕ} (h : n ≤ m),
    coefficientRestriction (J := X.smallEtaleTopology) O t h ⋙ level m ≅
      level n ⋙ coefficientRestriction (J := Z.smallEtaleTopology) O t h
  restrictionMate : ∀ {m n : ℕ} (h : n ≤ m),
    (mateEquiv (levelAdjunction n) (levelAdjunction m)
      (.mk _ _ _ _ (restriction h).hom)) = (I.restrictInverse h).inv
  transition : ∀ {m n : ℕ} (h : n ≤ m) M,
    (PZ.strictTransition h).app (extension.obj M) ≫
      (coefficientRestriction (J := Z.smallEtaleTopology) O t h).map
        ((evaluation n).hom.app M) =
    (evaluation m).hom.app M ≫ (level m).map ((PX.strictTransition h).app M) ≫
      (restriction h).hom.app (M.level n)

attribute [instance] StrictEtaleOrdinaryOpen.additive StrictEtaleOrdinaryOpen.levelAdditive

/-- Construct ordinary extension by zero with its actual scalar-restriction mates.
Source: Stacks 03S2 (the presheaf formula), 03DI (the adjunction), 03DJ (exactness);
Zheng, Construction 4.1
(blueprint: lem-pur-strict-etale-ordinary-open-extension).

Proof: at level n identify modules over the constant quotient-ring sheaf with
fixed-quotient-ring module sheaves using constant_ring_module_sheaves. Transport
openImmersionLowerShriek and its adjunction to the given algebraic inverse image;
the underlying geometric adjunction and constant sections identify that inverse
image with the fixed-ring inverse image. For a quotient-ring homomorphism,
restriction of scalars leaves the underlying additive sheaf and its section maps
unchanged. In the presheaf formula for open extension, both orders of restriction
and extension therefore have the same summands, additive groups and restriction maps;
the scalar action on each summand is multiplication by the image of the scalar.
Sheafification gives a canonical isomorphism, inverse to the same sectionwise
identification. Its transpose is restriction of the open unit on each summand.
Transport this comparison along the constant-ring equivalences. Its mate is the
inverse of I.restrictInverse because the latter is fixed on underlying sheaves by
I.restrictInverseUnderlying and the unit has just been checked on the same sections.
For a strict system M define its n-th
extended level by this level extension and its successor transition by extension
of M.transition followed by this scalar comparison. Define maps levelwise.
Naturality proves the transition condition and the functor laws. Transpose maps
levelwise using the level open adjunctions and I.inverseEvaluation. Their mate
identities say precisely that compatible families transpose to compatible families,
so the resulting Hom equivalence defines the system adjunction and evaluationMate.
Exactness follows levelwise from 03DJ, since kernels and cokernels of strict systems
are levelwise and evaluation jointly reflects exactness. The successor transition
identity is the definition. The normalized strict transitions are the iterated
successor transitions; identity and composition therefore prove the displayed
transition formula for all n ≤ m, including n = m. These constructions work for
the zero coefficient ring and the empty open, where the same zero maps and Hom
bijections apply. No regularity or completeness is used in this ordinary step. -/
theorem strictEtaleOrdinaryOpen_exists : Nonempty (StrictEtaleOrdinaryOpen O t j I PX PZ) := by
  obtain ⟨L⟩ := strictEtaleLevelOpenData_exists O t j I
  obtain ⟨A⟩ := strictEtaleSystemOpenAssembly_exists O t j I PX PZ L
  let _ : ∀ n, (L.level n).Additive := L.levelAdditive
  let _ : A.extension.Additive := A.additive
  exact ⟨{
    extension := A.extension
    exact := A.exact
    adjunction := A.adjunction
    level := L.level
    levelExact := L.levelExact
    levelAdjunction := L.levelAdjunction
    evaluation := A.evaluation
    evaluationMate := A.evaluationMate
    restriction := L.restriction
    restrictionMate := L.restrictionMate
    transition := A.transition }⟩

end AlgebraicGeometry
