/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic

/-! # K-flatness on the ringed sequence site of singleton extension

Source: Stacks 06YN and 0G7E; Zheng, Construction 4.1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Ordinary singleton extension preserves flat-term K-flat complexes on the whole
ringed sequence site. Source: Zheng, Construction 4.1; Stacks, Cohomology on Sites,
definition-K-flat (06YN), lemma-pullback-K-flat (0G7E), and the representative argument
of lemma-derived-pullback-composition (0D6D).
(blueprint: lem-pur-system-singleton-kflat)

Proof: vertical coverings make tensor products and sheafification levelwise. At a
level j at most n the singleton is extension of scalars from B_n to B_j; at a
higher level it is zero. Extension of a flat module is flat. Exactness of tensoring
with a singleton term is therefore detected by the exact, jointly conservative
evaluations, which proves flatness on the sequence site. For an acyclic sequence
complex K, evaluation commutes with the coproducts in total tensor. Below n its
tensor with the singleton complex is, as an abelian complex,
Res_{B_n to B_j}(K_j) tensor_{B_n} P: on each summand the isomorphism sends
x tensor (b tensor p) to bx tensor p and its inverse inserts the scalar 1.
Balancing verifies the two inverse laws; the degree-zero scalar respects the
signed total differential. Exact restriction makes Res(K_j) acyclic, so K-flatness
of P makes this tensor acyclic. Above n it is zero. Joint detection of acyclicity
by the evaluations proves K-flatness on the whole sequence site. -/
theorem singletonSequenceOrdinary_kFlat (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) (hP : systemLevelKFlat B n P) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemSequenceRing B)
      (((singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ)).obj P) ∧
    (∀ i : ℤ, IsFlatOnSite (R := systemSequenceRing B)
      ((singletonSequenceOrdinary S T B n).obj (P.X i))) := by sorry

end SheafOfModules
