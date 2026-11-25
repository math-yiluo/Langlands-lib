/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicIsomorphismPresentation
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy

/-! # Finite isomorphism sheaves and evaluation for a supplied algebraic tower

Source: Stacks Project, Tags 09BV, 09C6 and 0F63.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- A supplied normalized algebraic model has finite Isom sheaves with nonempty stalks.
Their reduction and evaluation respect the actual strict tower arrows. This constructs
no covering and chooses no compatible sections.

Source: Stacks Project, Tags 09BV and 0F63, with the scalar comparisons of Tag 09C6;
finite-level etale presentation and finite-ring derived local constancy.
(blueprint: lem-weil-pbc-finite-perfect-adic-isomorphism-sections).

Proof: Descend the actual finite quotient diagram on the chart by finite-ring derived
comparison and its full faithfulness. Lift the supplied algebraic tower to the coefficient
universe by the exact module equivalences. At each level take the etale sheaf of derived
isomorphisms from its constant algebraic level to the descended quotient level. Both
complexes are bounded with finite locally constant cohomology: the supplied perfect
models give this locally, and boundedness is inherited from their single algebraic level.
The finite-ring derived mapping-sheaf theorem makes this Isom sheaf finite locally
constant. The separate local markings give nonempty geometric stalks. Use the two
normalization universal arrows to define reduction on these sheaves, by conjugating
scalar extension with the normalization isomorphisms. Sheafify the resulting presheaf
maps; preservation of the generator normalization equation by source-site evaluation
proves compatibility on weakly contractible affine pro-etale objects. Evaluate a section
there and invert its isomorphism to orient it from the actual
quotient toward the algebraic level. Forget quotient scalars, apply the normalized finite
coefficient identifications and the constant/completed scalar comparison. The scalar
compatibility of φ identifies the resulting maps with the actual levelwise arrows of the
specified strict derived quotient system, rather than independent isomorphic quotients.
Consecutive transition compatibility is precisely the adjunct normalization square.
Finally apply exact slice restriction along any W → U; functoriality preserves these
isomorphisms and their square, and the canonical composition comparison identifies the
objects with restriction from X to W. All these constructions are finite-level; none
requires an inverse limit or existence of a common trivializing covering. The zero ring,
zero complexes and empty charts satisfy the same constructions. -/
theorem finitePerfectAdic_isomorphism_sections
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    ∃ (I : ℕ → Sheaf V.left.smallEtaleTopology (Type (t + 1)))
      (r : ∀ n : ℕ, I (n + 1) ⟶ I n)
      (ev : ∀ (U : V.left.ProEt), IsAffine U.left →
        (ProEt.topology V.left).IsWeaklyContractible.{t + 1} U →
        ∀ (W : X.ProEt), (W ⟶ finitePerfectAdicChartObject V U) → ∀ n : ℕ,
        ((Functor.sheafPullbackConstruction.sheafPullback (toProEt V.left)
          (Type (t + 1)) V.left.smallEtaleTopology (ProEt.topology V.left)).obj (I n)).obj.obj
            (op U) →
        ((finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
            (op n) ≅ (finitePerfectAdicModelDiagram X d W T).obj (op n))),
      (∀ n : ℕ, IsLisseEtaleSheafOfSets (I n)) ∧
      (∀ (n : ℕ) (Ω : Type t) [Field Ω] [IsSepClosed Ω]
        (x : Spec (.of Ω) ⟶ V.left), Nonempty ((pointSmallEtale x).sheafFiber.obj (I n))) ∧
      ∀ (U : V.left.ProEt) (ha : IsAffine U.left)
        (hw : (ProEt.topology V.left).IsWeaklyContractible.{t + 1} U)
        (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
        (s : ((Functor.sheafPullbackConstruction.sheafPullback (toProEt V.left)
          (Type (t + 1)) V.left.smallEtaleTopology (ProEt.topology V.left)).obj
            (I (n + 1))).obj.obj (op U)),
        (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
            (homOfLE (Nat.le_succ n)).op ≫
          (ev U ha hw W f n
            (((Functor.sheafPullbackConstruction.sheafPullback (toProEt V.left)
              (Type (t + 1)) V.left.smallEtaleTopology (ProEt.topology V.left)).map
                (r n)).hom.app (op U) s)).hom =
          (ev U ha hw W f (n + 1) s).hom ≫
            (finitePerfectAdicModelDiagram X d W T).map (homOfLE (Nat.le_succ n)).op := by
  classical
  obtain ⟨D⟩ := finitePerfectAdic_isomorphism_presentation X d φ hφ hcompat M V T
    hperfect hmark
  let I (n : ℕ) := derivedLocalIsomorphismSheaf (D.C n) (D.K n)
  let r (n : ℕ) : I (n + 1) ⟶ I n :=
    (presheafToSheaf V.left.smallEtaleTopology (Type (t + 1))).map (D.p n)
  let ev (U : V.left.ProEt) (ha : IsAffine U.left)
      (hw : (ProEt.topology V.left).IsWeaklyContractible.{t + 1} U)
      (W : X.ProEt) (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ)
      (s : ((comparisonSetUpperStar V.left).obj (I n)).obj.obj (op U)) :=
    (D.transport U W f n
      (sourceDerivedIsoEvaluation V.left (finitePerfectAdicIsomorphismRing d n)
        (D.C n) (D.K n) U ha hw s)).symm
  refine ⟨I, r, ev, ?_, D.stalk, ?_⟩
  · intro n
    let : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
    exact ((AlgebraicGeometry.Etale.finiteRing_derived_local_constancy V.left
      (finitePerfectAdicIsomorphismRing d n) (D.C n) (D.boundedC n) (D.lisseC n)).2.1
        (D.K n) (D.boundedK n) (D.lisseK n)).2
  · intro U ha hw W f n s
    have hs := sourceIsomorphism_normalized_presheaf_evaluation V.left
      (finitePerfectAdicIsomorphismQuotient d n)
      (D.C (n + 1)) (D.K (n + 1)) (D.C n) (D.K n)
      (D.dC n) (D.dK n) (D.p n) (D.normalized n) U ha hw s
    have ht := D.transport_square U W f n _ _ hs
    dsimp only [ev, Iso.symm_hom]
    apply (cancel_epi (D.transport U W f (n + 1)
      (sourceDerivedIsoEvaluation V.left (finitePerfectAdicIsomorphismRing d (n + 1))
        (D.C (n + 1)) (D.K (n + 1)) U ha hw s)).hom).mp
    apply (cancel_mono (D.transport U W f n
      (sourceDerivedIsoEvaluation V.left (finitePerfectAdicIsomorphismRing d n)
        (D.C n) (D.K n) U ha hw
        (((comparisonSetUpperStar V.left).map (r n)).hom.app (op U) s))).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc]
    convert ht.symm using 1

end AlgebraicGeometry.Scheme
