/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteImpliesUnitIso
import WeilConjectures.AlgebraicGeometry.ExtendedCechUnitIsoImpliesComplete

/-! # Fixed objects of the augmented extended Cech completion

Source: Stacks Project, algebraization.tex, Tags 099B and 099F.
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace CategoryTheory

/-- Local ideal completeness is equivalent to invertibility of the actual Cech unit.
This is a criterion for a single object; it contains no assertion about maps to other
objects or about the value of completion on arbitrary objects.

Source: Stacks Project, algebraization.tex, Tag 099B, proof of lemma-derived-completion,
and Tag 099F, proof of proposition-derived-completion.
(auxiliary; not a blueprint node).

Proof: choose a covering family on which the ideal has a specified finite generating
list. Restrict K and its augmentation to such a slice and use hK to replace them by
the ordered tensor of the two-term localization complexes, preserving augmentation.
Exact restriction commutes with derived internal Hom. Its comparison at the ring
complex is evaluation at one, so the induced unit agrees with the specified unit
up to invertible comparisons.

If E is locally complete, its derived internal Hom from every nonempty product of
the generators' localizations vanishes: these products belong to the ideal, and
iterated localization is localization at the product. Cancel the identity pair in
the augmentation cone. Filter the remaining bounded complex by its positive Cech
degrees. Each graded piece is a finite sum of shifted nonempty-product localization
modules. Contravariant derived internal Hom into E annihilates each graded piece;
exactness and induction on the finite filtration annihilate the cone. Thus the
augmentation induces an isomorphism on derived internal Hom, and evaluation at one
identifies it with the unit on E. Cohomology sheaves detect and descend this local
isomorphism to the original site.

Conversely, suppose that the unit on E is invertible. For each generator b_i on a
finite-generator slice, tensor its localization with the ordered Cech complex.
The i-th factor then has invertible differential, whose inverse contracts that
factor, with the Koszul sign in the total tensor. Tensor-Hom adjunction identifies
RHom(O[1/b_i], RHom(K,E)) with RHom(K tensor O[1/b_i], E), which is zero. Transport
along the invertible unit gives RHom(O[1/b_i], E) = 0. The sections with this vanishing
form a sheaf of ideals (Tag 0998), so all sections of the ideal satisfy the test,
using generation and covering-sieve descent. This is exactly local completeness.
The empty list has identity augmentation, the zero ideal imposes only the zero
localization test, and an invertible generator gives zero completion. The same
argument includes the zero ring and empty covering families; it uses no boundedness
of E, enough points, or exactness of infinite products. -/
theorem ringedExtendedCech_complete_iff_unit_isIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (E : ringedSiteDerived O) :
    IsLocallyDerivedRingedIdealComplete O I ι E ↔
      IsIso (ringedCechCompletionUnit O K ε E) := by
  constructor
  · exact ringedExtendedCech_complete_implies_unit_isIso J O I ι K ε hK E
  · exact ringedExtendedCech_unit_isIso_implies_complete J O I ι K ε hK E

end CategoryTheory
