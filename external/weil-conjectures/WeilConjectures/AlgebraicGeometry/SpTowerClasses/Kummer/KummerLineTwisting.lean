/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassTwisting

import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.KummerRootRankOne
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import WeilConjectures.Algebra.Homology.SiteTensorHom.SiteTensorHomEquiv
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Tensor/Hom equivalence for the scalar-extended Kummer root line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {T : Scheme.{u}} (c : Chern l E T)

private abbrev negative : Systems T (Arings l E T) ⥤ Systems T (Arings l E T) :=
  (SheafOfModules.homFunctor (systemRing l E T)).obj (op (lineModule l E c))

private def lineAdjunction : positive l E c ⊣ negative l E c := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦
        SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1} M (lineModule l E c) N
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro M' M N f g
    change M ⟶ SheafOfModules.homObj (R := systemRing l E T) (lineModule l E c) N at g
    change
      (SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1}
        M' (lineModule l E c) N).symm (f ≫ g) =
      (SheafOfModules.siteSheafTensorRight (lineModule l E c)).map f ≫
        (SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1}
          M (lineModule l E c) N).symm g
    apply (SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1}
      M' (lineModule l E c) N).injective
    rw [Equiv.apply_symm_apply,
      SheafOfModules.SiteTensorHom.equiv_naturality.{u + 1, u, u + 1, u + 1},
      Equiv.apply_symm_apply]
  · intro M N N' f g
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    rfl

private theorem lineRankOne
    [(c.rootModule).IsFiniteLocallyFreeOfRank 1] :
    (lineModule l E c).IsFiniteLocallyFreeOfRank 1 := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let R := SemilinearSections.systemRing.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (fun n ↦ (Rrings l T).obj (op n))
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op)
  let A := systemRing l E T
  let a := coefficientSystemMap l E T
  let : c.rootModule.IsInvertible :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one _).mpr inferInstance
  have hi := (SheafOfModules.scalarExtensionDual_localIsomorphism R A a c.rootModule).1
  have hraw : SheafOfModules.changeOfRingsPresheafOfUniverses a c.rootModule =
      SheafOfModules.changeOfRingsPresheaf a c.rootModule := by rfl
  have hobj : SheafOfModules.changeOfRingsOfUniverses a c.rootModule =
      SheafOfModules.changeOfRings a c.rootModule := by
    unfold SheafOfModules.changeOfRingsOfUniverses SheafOfModules.changeOfRings
    rw [hraw]
    rfl
  let := hi
  let e := eqToIso (hobj.trans (c.scalar.model.obj_eq c.rootModule).symm)
  have := SheafOfModules.IsInvertible.of_iso e
  exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one _).mp this

private theorem positive_isEquivalence
    [(lineModule l E c).IsFiniteLocallyFreeOfRank 1] :
    (positive l E c).IsEquivalence := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let R := systemRing l E T
  let L := lineModule l E c
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let Q := SheafOfModules.homObj (R := R) L (SheafOfModules.unit _)
  obtain ⟨I, U, hc, hU⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
      (M := L) (r := 1)).mp inferInstance
  have hL : ∀ W : ℕ × T.ProEt, ∃ s : Sieve W,
      s ∈ coefficientSequenceTopology (Scheme.ProEt.topology T) W ∧
      ∀ (V : ℕ × T.ProEt) (f : V ⟶ W), s f →
        Nonempty (L.over V ≅ SheafOfModules.unit
          ((SemilinearSections.ring.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology T)) R).over V)) := by
    intro W
    refine ⟨Sieve.ofObjects U W, hc W, ?_⟩
    rintro V f ⟨i, ⟨g⟩⟩
    let e := (hU i).some ≪≫ SheafOfModules.freeUniqueIso _
    exact ⟨(SheafOfModules.overFunctorMap _ g).symm.app L ≪≫
      (SheafOfModules.overMap _ g).mapIso e ≪≫ SheafOfModules.overMapUnitIso g⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ev, _⟩ :=
    SheafOfModules.LineEvaluation.evaluation_inverse_pair.{u + 1, u, u + 1} R L hL
  let e := BraidedCategory.tensorRightEquivalence L Q ev
  exact (Functor.isEquivalence_iff_of_iso
    (SheafOfModules.siteSheafTensorRightIso R L)).mpr e.isEquivalence_functor

/-- The root module already present in Chern data defines the normalized tensor/Hom twist.
No existence or normalization of Chern arrows is asserted here.

Source: blueprint latest, `sk-prop-diagonal-tower/_section.md`, Tate-twist paragraph;
`sk-prop-sp-tower-geometric-classes.proof.md`, clause (2), rank-one scalar extension.
(blueprint: lem-sfb-kummer-line-twisting).

Proof: on the pro-etale covering obtained by adjoining compatible primitive
l^(n+1)-th roots, identify the actual roots tower with its quotient ring system,
using the chosen roots as compatible generators. The specified section and map
equations for c.reduction.forget, followed by c.rootForget, identify c.rootModule
with this root system as modules: the action of the constant finite quotient
ring is determined by the additive group and its annihilation. Scalar extension
along coefficientSystemMap preserves this rank-one trivialization, with its
counit giving the same lineModule that defines positive. Define the inverse
functor by homObj from this line and homObjMap on morphisms. The ordinary sheaf
tensor/Hom adjunction gives coevaluation x mapping to (y mapping to x tensor y)
and evaluation z tensor y mapping to z(y). On every trivializing chart these
are the ordinary rank-one module unit and counit, hence are isomorphisms.
Their formulas commute with restrictions and the power transitions, so they
glue on the sequence site; local isomorphy proves global isomorphy. Use these
unit and counit isomorphisms and the tensor/Hom triangle identities to construct
the equivalence. Both functors are additive, and equivalences preserve finite
limits and colimits. Multiplication a tensor y mapping to a times y identifies
the tensor of the coefficient unit with lineModule and supplies exactly the
unit_normalization field. These formulas also give the backward_maps,
coevaluation and evaluation fields, with the displayed endpoint HEq transports.
The empty scheme is covered by the same sheaf-local argument; l=2 and n=0
use the same primitive-root and tensor formulas. -/
theorem nonempty_kummerLineTwisting (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (l : Γ(T, ⊤))) (c : Chern l E T) :
    Nonempty (Twisting l E c) := by
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := kummerRoot_rank_one l T hT c.reduction.forget c.rootModule c.rootForget
  let := lineRankOne l E c
  let := positive_isEquivalence l E c
  let adj := lineAdjunction l E c
  let e := adj.toEquivalence
  let : e.functor.Additive := Functor.additive_of_preserves_binary_products e.functor
  refine ⟨{
    equivalence := e
    forward := rfl
    backward := fun _ ↦ rfl
    backward_maps := fun _ ↦ HEq.rfl
    coevaluation := ?_
    evaluation := ?_
    additive := inferInstance
    inverseAdditive := inferInstance
    limits := inferInstance
    colimits := inferInstance
    inverseLimits := inferInstance
    inverseColimits := inferInstance
    unitIso := SheafOfModules.scalarTensorLeftUnitor (systemRing l E T) (lineModule l E c)
    unit_normalization := ?_ }⟩
  · intro M U x z hz y
    have hz' := eq_of_heq hz
    subst z
    apply heq_of_eq
    change (((SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1} M (lineModule l E c)
      ((positive l E c).obj M) (𝟙 _)).val.app U x).app
        (op (Over.mk (𝟙 U.unop)))) y = _
    rw [SheafOfModules.SiteTensorHom.equiv_apply.{u + 1, u, u + 1, u + 1}]
    change pure l E c M U (M.val.map (𝟙 U) x) y = pure l E c M U x y
    rw [M.val.map_id]
    rfl
  · intro M U z z' y v hz hv
    have hz' := eq_of_heq hz
    subst z'
    have hv' := eq_of_heq hv
    subst v
    let H := (negative l E c).obj M
    let q := SheafOfModules.SiteTensorHom.equiv.{u + 1, u, u + 1, u + 1}
      H (lineModule l E c) M
    change (q.symm (𝟙 H)).val.app U
      (SheafOfModules.siteSheafTensorTmul H (lineModule l E c) U z y) = _
    have h := q.apply_symm_apply (𝟙 H)
    have hh := congrArg (fun f ↦ (f.val.app U z).app (op (Over.mk (𝟙 U.unop))) y) h
    have he := SheafOfModules.SiteTensorHom.equiv_apply.{u + 1, u, u + 1, u + 1}
      H (lineModule l E c) M (q.symm (𝟙 H)) U z (Over.mk (𝟙 U.unop)) y
    have hh' := he.symm.trans hh
    change (q.symm (𝟙 H)).val.app U
      (SheafOfModules.siteSheafTensorTmul H (lineModule l E c) U
        (H.val.map (𝟙 U) z) y) = z.app (op (Over.mk (𝟙 U.unop))) y at hh'
    rw [H.val.map_id] at hh'
    exact hh'
  · intro U a y v hv
    have hv' := eq_of_heq hv
    subst v
    exact SheafOfModules.scalarTensorLeftUnitor_tmul (systemRing l E T)
      (lineModule l E c) U a y

end AlgebraicGeometry.ProEtale.SpTowerClasses
