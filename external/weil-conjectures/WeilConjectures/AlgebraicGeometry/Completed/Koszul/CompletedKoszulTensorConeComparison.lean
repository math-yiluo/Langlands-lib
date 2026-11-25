/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulCoefficientConeRealization
import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorConeComparisonAux
public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorAugmentationComponent

/-! # Tensor comparison for normalized completed Koszul augmentation cones

Source: Stacks Project, Tags 099M and 06YP; the signed total-tensor cone formula.
(blueprint: lem-weil-pbc-completed-koszul-tensor-cone-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] completedKoszulCochainMonoidal
  completedKoszulCochainMonoidalStruct
attribute [local instance] Functor.preservesZeroMorphisms_of_additive

attribute [local instance] augmentationComponentPreadditive

attribute [local irreducible] completedAdicRing

/-- The actual cone tower at P is tensor of its coefficient cone tower. This is
an isomorphism of strict towers of complexes, before any localization. It imposes
no K-flatness and asserts neither eventual vanishing nor a derived-limit result.

Source: Stacks Project, proetale.tex, proof of lemma-naive-completion (099M), and
sites-cohomology.tex, lemma-K-flat-quasi-isomorphism (06YP), tensor-cone calculation.
(blueprint: lem-weil-pbc-completed-koszul-tensor-cone-comparison).

Proof: put U equal to the cochain tensor unit and K_n equal to the completed
exterior Koszul complex. At each level the source of beta at U is U tensor K_n.
The left unitor identifies it with K_n. In its target the left unitor on modules
identifies the ordinary quotient tensor of U with the quotient module in degree
zero. Under these identifications beta_U is the coefficient augmentation epsilon_n.
Its degree-zero component is fixed by the unit equation, since the degree-zero
Koszul unit is an isomorphism; every other component is zero by the stated total
summand equation. For any P, use the inverse associator followed by the right
unitor to identify P tensor (U tensor K_n) with P tensor K_n. On the target use
the same unitors and the total-tensor/single-degree-zero comparison to identify
P tensor (U tensor Q_n[0]) with the ordinary termwise P tensor Q_n. The square
with beta_P and P tensor beta_U commutes: on the (p,q) summand with q nonzero
both maps vanish; on (p,0) precompose by P^p tensor the invertible Koszul unit.
The resulting equality is the unit equation for beta_P and beta_U and naturality
of the unitors. Joint detection by total summand inclusions proves the square.
All comparisons commute with strict successors: associators and unitors are
natural, and the single-degree-zero comparison is natural in the quotient map.
Apply the natural tensor-cone isomorphism at every level to these commuting
squares. On the shifted source component in tensor degree p its sign is (-1)^p;
on the target component it is the identity. The differential identity follows
from (-1)^(p+1) = -(-1)^p, including the mixed cone differential. The same sign
occurs on both sides of every transition square, so the component isomorphisms
assemble into the displayed tower isomorphism. This uses no boundedness of P,
products, or regularity of the generators, and includes r=0 and the zero ring. -/
theorem completedKoszulTensorConeComparison
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (β : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ))
    (hu : ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
      completedAdicKoszulTensorUnit T d r a P n ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app (op n) =
          completedQuotientTensorUnit T d P n)
    (hz : ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ) (p q : ℤ) (_hq : q ≠ 0),
      completedKoszulTensorSummand T d r a P n p q ≫
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (β.app P)).app (op n)).f (p + q) = 0)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    Nonempty
      ((CochainComplex.mappingCone
        (β.app (𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)))).asFunctor ⋙
          tensorLeft P ≅ (CochainComplex.mappingCone (β.app P)).asFunctor) := by
  let U := 𝟙_ (CochainComplex (CompletedAdicModules T d) ℤ)
  let f := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app U)
  let g := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)
  let s := koszulTensorTowerUnitor T d (completedAdicKoszul T d r a)
    (completedAdicKoszulStep T d r a) P
  let q := quotientTensorTowerIso T d (completedAdicFiniteModule T d)
    (completedAdicFiniteModuleStep T d) P
  have h : Functor.whiskerRight f (tensorLeft P) ≫ q.hom = s.hom ≫ g := by
    apply NatTrans.ext
    funext n
    change P ◁ f.app n ≫ (quotientTensorIso T d
        (completedAdicFiniteModule T d n.unop) P).hom =
      (koszulTensorUnitor T d (completedAdicKoszul T d r a n.unop) P).hom ≫ g.app n
    unfold quotientTensorIso quotientUnitIso koszulTensorUnitor
    dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    change P ◁ f.app n ≫ (tensorLeft P).map
        ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
          (completedAdicFiniteModule T d n.unop) U).inv ≫
          (λ_ ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (completedAdicFiniteModule T d n.unop))).hom) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
          (completedAdicFiniteModule T d n.unop) P).hom =
      P ◁ (λ_ (completedAdicKoszul T d r a n.unop)).hom ≫ g.app n
    exact completedKoszulTensorAugmentationComponent T d r a n.unop P
        (g.app n) (f.app n) (hu P n.unop) (hz P n.unop) (hu U n.unop)
  exact ⟨Functor.isoWhiskerRight (levelConeTowerIso f) (tensorLeft P) ≪≫
    levelConeTower_mapBifunctorIso (curriedTensor (CompletedAdicModules T d)) P f ≪≫
    coneTowerIso (Functor.whiskerRight f (tensorLeft P)) g s q h ≪≫
    (levelConeTowerIso g).symm⟩

end AlgebraicGeometry.Scheme
