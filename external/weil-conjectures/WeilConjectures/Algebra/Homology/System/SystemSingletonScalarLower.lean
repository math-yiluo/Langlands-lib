/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonScalarBasic

/-! # Compatibility of singleton coefficient change with lower-singleton maps

Source: Zheng, Construction 4.1; Stacks 0D6D and 06YT.
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
  {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)
  (A : SystemScalarModel (singletonSequenceRingMap a))

/-- The normalized singleton coefficient comparisons commute with the canonical
lower-singleton maps and the specified scalar associators.
Source: Zheng, Construction 4.1, and Stacks, Cohomology on Sites, 0D6D and 06YT;
this is Step 9 of the parent singleton/scalar argument.
(blueprint: lem-pur-system-singleton-scalar-lower)

Proof: resolve the input by a flat-term K-flat B_m-complex Q. Every scalar extension
in the square remains flat-term K-flat by ringed-topos pullback for the identity
topos. The lower-singleton map below n is the balanced associator
b tensor (t tensor q) to b rho_jn(t) tensor q; its source is zero above n.
The scalar coefficient comparison sends (b tensor q) tensor c to
 a_j(b)c tensor (q tensor 1). Thus the two routes below n send the generator
(b tensor (t tensor q)) tensor c respectively to
 a_j(b rho_jn(t))c tensor (q tensor 1) and
 a_j(b)c rho_jn(a_n(t)) tensor (q tensor 1). Naturality of a equates them.
Balancing and sheafification extend equality to actual cochain maps. Above n both
maps vanish, including n < j <= m; when n=m the calculation is multiplication.
The normalized singleton transpose identifies these lower representative maps with
the maps defined using systemSingleDerivedBelow. Normalized adjunction composition
identifies the coefficient comparisons with their representatives, and scalar
coherence identifies the associators. Localize the cochain equality and transport
along the resolution isomorphism. Naturality gives the assertion for every input. -/
theorem singletonScalarDerivedIso_lower (n m : ℕ) (h : n ≤ m)
    (P : DerivedCategory (systemLevel B m)) :
      A.model.T.map (singletonLowerMap S T B h P) ≫
          (singletonScalarDerivedIso S T a A m).hom.app P =
        (singletonScalarDerivedIso S T a A n).hom.app ((systemDerivedTensor S B h).obj P) ≫
          (singletonSequenceDerived S T D n).map ((singletonScalarSquare S a n m h).hom.app P) ≫
          singletonLowerMap S T D h ((S (a.app (op m))).model.T.obj P) := by sorry

end SheafOfModules
