/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.AcyclicKFlatTensor
import WeilConjectures.Algebra.Homology.ChangeOfRingsTensorAcyclic

/-!
# Extension of scalars of acyclic K-flat complexes

Source: Stacks Project, Cohomology on Sites, Tags 06YT and 06YY.
(blueprint: lem-pur-change-of-rings-acyclic-kflat).
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

/-- Extension of scalars sends an acyclic K-flat complex to an acyclic complex.
Source: Stacks Project, Tag 06YT, proof, and Tag 06YY, change-of-rings specialization.

Proof: regard O' as an O-module concentrated in degree zero, called S. Take a K-flat
resolution r : R → S (Tag 06YS). The cone of r is acyclic. By K-flatness of K,
Tot(Cone(r) ⊗ K) is acyclic. The tensor-cone comparison identifies this with the cone
of Tot(r ⊗ id_K), so the latter is a quasi-isomorphism. Since R is K-flat and K is
acyclic, Tot(K ⊗ R) is acyclic. The signed tensor symmetry, acting on the (p,q)
summand by (-1)^(pq) times the module braiding, identifies it with Tot(R ⊗ K).
Thus Tot(S ⊗ K) is acyclic, by invariance of cohomology under quasi-isomorphisms.
There is just one nonzero S-degree, so this last total complex is naturally the
restriction of the termwise extension of scalars of K. Restriction of scalars does
not change the underlying sheaf of abelian groups and is exact and faithful; it
therefore reflects acyclicity. Finally the equalities h and hm give the natural
isomorphism from E to extension of scalars (naturality is exactly hm), and its
termwise complex isomorphism transports acyclicity. No flatness of O' is required.
The zero complex and the zero ring also satisfy the argument: all their relevant
cohomology sheaves vanish.
(blueprint: lem-pur-change-of-rings-acyclic-kflat) -/
theorem changeOfRings_acyclic_of_isKFlat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {O O' : Sheaf J CommRingCat.{u}} (φ : O ⟶ O')
    (E : SheafOfModules.{u} (𝓡 O) ⥤ SheafOfModules.{u} (𝓡 O'))
    (h : ∀ M : SheafOfModules.{u} (𝓡 O), E.obj M = changeOfRings.{u, u, u} φ M)
    (hm : ∀ {M N : SheafOfModules.{u} (𝓡 O)} (a : M ⟶ N),
      E.map a = eqToHom (h M) ≫ changeOfRingsHom.{u, u, u} φ M a ≫ eqToHom (h N).symm)
    [E.Additive]
    (K : CochainComplex (SheafOfModules.{u} (𝓡 O)) ℤ)
    (hK : K.IsKFlatTensor) (hA : K.Acyclic) :
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic  := by
  apply changeOfRings_acyclic_of_tensor_acyclic φ E h hm K
  intro F
  exact tensor_acyclic_of_isKFlat K hK hA F

end SheafOfModules
