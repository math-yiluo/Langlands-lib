/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.LocalizedCohomologyMayerVietoris
import WeilConjectures.AlgebraicGeometry.CohomologySectionDivision
import Mathlib.Algebra.FiveLemma

universe u_1
@[expose] public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Additive maps from the fraction presentation agree if they agree on fractions. -/
private theorem fraction_hom_ext {X : Scheme.{u_1}} (L F : X.Modules)
    (s : Γ(L, ⊤)) (p : ℕ) (W : X.Opens) {G : Type u_1} [AddCommGroup G]
    (f g : CohomologyFractionPresentation L F s p W →+ G)
    (h : ∀ n ξ, f (cohomologyFraction L F s p W n ξ) =
      g (cohomologyFraction L F s p W n ξ)) : f = g := by
  have hh : f.comp (QuotientAddGroup.mk' _) = g.comp (QuotientAddGroup.mk' _) :=
    DirectSum.addHom_ext h
  apply AddMonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective
    (cohomologyFractionRelations L F s p W) x
  exact DFunLike.congr_fun hh y

/-- Cohomology restriction along the identity is the identity. -/
private theorem cohomology_restriction_id (X : RingedSpace.{u_1}) (p : ℕ)
    (W : TopologicalSpace.Opens X) :
    RingedSpace.openModuleCohomologyRestriction X p (𝟙 W) =
      𝟙 (RingedSpace.openModuleCohomology X p W) := by
  unfold RingedSpace.openModuleCohomologyRestriction
  simp
  rfl

private noncomputable def cohomology_pair (X : RingedSpace.{u_1})
    (F : SheafOfModules (moduleRings X)) (p : ℕ)
    (A B J : TopologicalSpace.Opens X) (hA : A ≤ J) (hB : B ≤ J) :=
  ((RingedSpace.openModuleCohomologyRestriction X p (homOfLE hA)).app F).hom.prod
    ((RingedSpace.openModuleCohomologyRestriction X p (homOfLE hB)).app F).hom

private noncomputable def cohomology_diff (X : RingedSpace.{u_1})
    (F : SheafOfModules (moduleRings X)) (p : ℕ)
    (A B I : TopologicalSpace.Opens X) (hA : I ≤ A) (hB : I ≤ B) :=
  ((RingedSpace.openModuleCohomologyRestriction X p (homOfLE hA)).app F).hom.comp
      (AddMonoidHom.fst _ _) -
    ((RingedSpace.openModuleCohomologyRestriction X p (homOfLE hB)).app F).hom.comp
      (AddMonoidHom.snd _ _)

private noncomputable def cohomology_boundary (X : RingedSpace.{u_1})
    (F : SheafOfModules (moduleRings X)) (p : ℕ)
    (A B I J : TopologicalSpace.Opens X) (hI : A ⊓ B = I) (hJ : A ⊔ B = J)
    (δ : RingedSpace.openModuleCohomology X p (A ⊓ B) ⟶
      RingedSpace.openModuleCohomology X (p + 1) (A ⊔ B)) :=
  ((RingedSpace.openModuleCohomologyRestriction X (p + 1) (homOfLE hJ.ge)).app F).hom.comp
    ((δ.app F).hom.comp
      ((RingedSpace.openModuleCohomologyRestriction X p (homOfLE hI.le)).app F).hom)

/-- Rewrite the open-cover row along the intersection and union equalities. -/
private theorem cohomology_exact_reindex (X : RingedSpace.{u_1})
    (F : SheafOfModules (moduleRings X)) (p : ℕ)
    (A B I J : TopologicalSpace.Opens X) (hI : A ⊓ B = I) (hJ : A ⊔ B = J)
    (δ : RingedSpace.openModuleCohomology X p (A ⊓ B) ⟶
      RingedSpace.openModuleCohomology X (p + 1) (A ⊔ B))
    (he : Function.Exact (cohomology_pair X F p A B (A ⊔ B) le_sup_left le_sup_right)
        (cohomology_diff X F p A B (A ⊓ B) inf_le_left inf_le_right) ∧
      Function.Exact (cohomology_diff X F p A B (A ⊓ B) inf_le_left inf_le_right)
        (δ.app F) ∧
      Function.Exact (δ.app F)
        (cohomology_pair X F (p + 1) A B (A ⊔ B) le_sup_left le_sup_right)) :
    Function.Exact (cohomology_pair X F p A B J (le_sup_left.trans hJ.le)
        (le_sup_right.trans hJ.le))
      (cohomology_diff X F p A B I (hI.ge.trans inf_le_left)
        (hI.ge.trans inf_le_right)) ∧
    Function.Exact (cohomology_diff X F p A B I (hI.ge.trans inf_le_left)
        (hI.ge.trans inf_le_right))
      (cohomology_boundary X F p A B I J hI hJ δ) ∧
    Function.Exact (cohomology_boundary X F p A B I J hI hJ δ)
      (cohomology_pair X F (p + 1) A B J (le_sup_left.trans hJ.le)
        (le_sup_right.trans hJ.le)) := by
  subst I
  subst J
  simpa only [cohomology_boundary, show homOfLE (le_refl (A ⊔ B)) = 𝟙 (A ⊔ B) from rfl,
    show homOfLE (le_refl (A ⊓ B)) = 𝟙 (A ⊓ B) from rfl,
    cohomology_restriction_id, NatTrans.id_app, AddCommGrpCat.hom_id,
    AddMonoidHom.id_comp, AddMonoidHom.comp_id] using he

/-- Rewrite the initial injection along the equality of the union opens. -/
private theorem cohomology_injective_reindex (X : RingedSpace.{u_1})
    (F : SheafOfModules (moduleRings X)) (A B J : TopologicalSpace.Opens X)
    (hJ : A ⊔ B = J)
    (he : Function.Injective
      (cohomology_pair X F 0 A B (A ⊔ B) le_sup_left le_sup_right)) :
    Function.Injective (cohomology_pair X F 0 A B J (le_sup_left.trans hJ.le)
      (le_sup_right.trans hJ.le)) := by
  subst J
  exact he

/- Historical counterexample to the former interface: on Spec k for a nonzero field,
 U = V = S = top, L = F = O, s = 1, and c W p = 0 satisfied the old local
 premises but gave the nonbijective zero map k -> k in degree zero. The old
 STATEMENT-DISPUTED interface omitted hc and replaced the intersection formula
 by True. The corrected hc excludes this example. -/

/-- Bijectivity of the canonical middle comparison in the localization diagram.
The fraction formula `hc` identifies `c` with the canonical comparison; all three
local equivalences satisfy that same formula.

Source: Stacks Project, Cohomology of Schemes, Tag 09MR, Mayer--Vietoris paragraph
(blueprint: lem-sc-invert-s-cohomology-gluing-aux).

Proof: On the nonvanishing open S the section s trivializes L. Consequently the
map on cohomology induced by multiplication by s^n is an isomorphism, for every
open W intersected with S. The formula hc therefore determines c W p on every
fraction [n, xi]. These fractions generate the quotient of the direct sum, so
additive homomorphisms satisfying the formula agree on the entire presentation.
Apply localizedCohomology_mayerVietoris to U and V. Its nonvanishing open equals
S by equality of underlying sets. Uniqueness identifies its comparison family
with c, transferring the exact rows and all commuting squares to c. The same
uniqueness identifies the equivalences in h_locU, h_locV and h_locUV with c on
U, V and their intersection. Thus the product comparisons and intersection
comparisons are bijective in every degree.
In degree zero both rows begin with an injective union-to-product map, followed
by the product-to-intersection map. Injectivity of c on the union follows by
mapping a kernel element to the product, using injectivity of its comparison,
and then injectivity of the upper union-to-product map. For surjectivity, map a
lower union element into the lower product, lift it through the product
comparison, and use the intersection comparison's injectivity and the commuting
square to see that the lift lies in the upper kernel. Upper exactness lifts it
to the upper union; lower injectivity shows its comparison is the given element.
For degree p = q + 1 use the five consecutive terms: product in degree q,
intersection in degree q, union in degree q + 1, product in degree q + 1,
intersection in degree q + 1. Both rows are exact, all squares commute, and all
four outside comparisons are bijective. The additive five lemma gives
bijectivity of the middle comparison c (U union V) (q + 1). Together with the
degree-zero argument this proves the claim in every natural-number degree. -/
theorem localized_middle_comparison_bijective
    (X : Scheme.{u_1}) [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsInvertible] (s : Γ(L, ⊤))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : X.Opens) (hS : (S : Set X) = nonvanishingLocus L s)
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (c : ∀ (W : X.Opens) (p : ℕ), CohomologyFractionPresentation L F s p W →+
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F)
    (hc : ∀ (W : X.Opens) (p n : ℕ)
        (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p W).obj
          (F ⊗ L.tensorPow n : X.Modules)),
      (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
          (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
            F ⟶ (F ⊗ L.tensorPow n : X.Modules))
          (c W p (cohomologyFraction L F s p W n ξ)) =
        (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (inf_le_left : W ⊓ S ≤ W))).app
            (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locU : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p U ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p U n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ S ≤ U))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p V ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p V).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p V n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : V ⊓ S ≤ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ)
    (h_locUV : ∀ p : ℕ, ∃ e : CohomologyFractionPresentation L F s p (U ⊓ V) ≃+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).obj F,
      ∀ (n : ℕ) (ξ : (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V)).obj
          (F ⊗ L.tensorPow n : X.Modules)),
        (RingedSpace.openModuleCohomology X.toRingedSpace p (U ⊓ V ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p (U ⊓ V) n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : U ⊓ V ⊓ S ≤ U ⊓ V))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ) :
    ∀ p : ℕ, Function.Bijective (c (U ⊔ V) p) := by
  classical
  obtain ⟨_, _, _, hmul⟩ := exists_cohomologySection_division X L F s S hS
  have huniq (W : X.Opens) (p : ℕ)
      (e : CohomologyFractionPresentation L F s p W →+
        (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).obj F)
      (he : ∀ n ξ,
        (RingedSpace.openModuleCohomology X.toRingedSpace p (W ⊓ S)).map
            (((ρ_ F).inv ≫ F ◁ tensorPowSection (homOfGlobalSection L s) n) :
              F ⟶ (F ⊗ L.tensorPow n : X.Modules))
            (e (cohomologyFraction L F s p W n ξ)) =
          (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
            (homOfLE (inf_le_left : W ⊓ S ≤ W))).app
              (F ⊗ L.tensorPow n : X.Modules) ξ) : c W p = e := by
    apply fraction_hom_ext
    intro n ξ
    exact (hmul W p n).1 ((hc W p n ξ).trans (he n ξ).symm)
  have hUbij (p : ℕ) : Function.Bijective (c U p) := by
    obtain ⟨e, he⟩ := h_locU p
    rw [huniq U p e.toAddMonoidHom he]
    exact e.bijective
  have hVbij (p : ℕ) : Function.Bijective (c V p) := by
    obtain ⟨e, he⟩ := h_locV p
    rw [huniq V p e.toAddMonoidHom he]
    exact e.bijective
  have hIbij (p : ℕ) : Function.Bijective (c (U ⊓ V) p) := by
    obtain ⟨e, he⟩ := h_locUV p
    rw [huniq (U ⊓ V) p e.toAddMonoidHom he]
    exact e.bijective
  obtain ⟨S', hS', hI, hJ, δ, hinj, hexact, hrestrict, c', hc',
    a, b, d, ha, hbU, hbV, hd, hainj, hab, hca, hcb, hcd⟩ :=
      localizedCohomology_mayerVietoris X L F s U V hU hV
  have hSS : S' = S := SetLike.coe_injective (hS'.trans hS.symm)
  subst S'
  have hcc : c = c' := by
    funext W p
    exact huniq W p (c' W p) (hc' W p)
  subst c'
  let a' (p : ℕ) := cohomology_pair X.toRingedSpace F p (U ⊓ S) (V ⊓ S)
    ((U ⊔ V) ⊓ S) (inf_le_inf_right S le_sup_left) (inf_le_inf_right S le_sup_right)
  let b' (p : ℕ) := cohomology_diff X.toRingedSpace F p (U ⊓ S) (V ⊓ S)
    ((U ⊓ V) ⊓ S) (inf_le_inf_right S inf_le_left) (inf_le_inf_right S inf_le_right)
  let d' (p : ℕ) := cohomology_boundary X.toRingedSpace F p (U ⊓ S) (V ⊓ S)
    ((U ⊓ V) ⊓ S) ((U ⊔ V) ⊓ S) hI hJ (δ (U ⊓ S) (V ⊓ S) p)
  let cp (p : ℕ) := (c U p).prodMap (c V p)
  have hcp (p : ℕ) : Function.Bijective (cp p) := by
    constructor
    · intro x y h
      exact Prod.ext ((hUbij p).1 (congrArg Prod.fst h))
        ((hVbij p).1 (congrArg Prod.snd h))
    · intro y
      obtain ⟨xU, hxU⟩ := (hUbij p).2 y.1
      obtain ⟨xV, hxV⟩ := (hVbij p).2 y.2
      exact ⟨(xU, xV), Prod.ext hxU hxV⟩
  have hca' (p : ℕ) : (a' p).comp (c (U ⊔ V) p) = (cp p).comp (a p) := by
    apply AddMonoidHom.ext
    intro x
    exact Prod.ext (hca p x).1.symm (hca p x).2.symm
  have hcb' (p : ℕ) : (b' p).comp (cp p) = (c (U ⊓ V) p).comp (b p) := by
    apply AddMonoidHom.ext
    intro x
    exact (hcb p x).symm
  have hcd' (p : ℕ) : (d' p).comp (c (U ⊓ V) p) =
      (c (U ⊔ V) (p + 1)).comp (d p) := by
    apply AddMonoidHom.ext
    intro x
    exact (hcd p x).symm
  have hab' (p : ℕ) : Function.Exact (a' p) (b' p) ∧
      Function.Exact (b' p) (d' p) ∧ Function.Exact (d' p) (a' (p + 1)) :=
    cohomology_exact_reindex X.toRingedSpace F p (U ⊓ S) (V ⊓ S)
      ((U ⊓ V) ⊓ S) ((U ⊔ V) ⊓ S) hI hJ (δ (U ⊓ S) (V ⊓ S) p)
        (hexact (U ⊓ S) (V ⊓ S) F p)
  have hainj' : Function.Injective (a' 0) :=
    cohomology_injective_reindex X.toRingedSpace F (U ⊓ S) (V ⊓ S)
      ((U ⊔ V) ⊓ S) hJ (hinj (U ⊓ S) (V ⊓ S) F)
  intro p
  cases p with
  | zero =>
    exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      (a 0) (b 0) (a' 0) (b' 0) (c (U ⊔ V) 0) (cp 0) (c (U ⊓ V) 0)
      (hca' 0) (hcb' 0) (hab 0).1 (hab' 0).1 (hcp 0) (hIbij 0).1 hainj hainj'
  | succ q =>
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (b q) (d q) (a (q + 1)) (b (q + 1))
      (b' q) (d' q) (a' (q + 1)) (b' (q + 1))
      (cp q) (c (U ⊓ V) q) (c (U ⊔ V) (q + 1)) (cp (q + 1))
      (c (U ⊓ V) (q + 1)) (hcb' q) (hcd' q) (hca' (q + 1)) (hcb' (q + 1))
      (hab q).2.1 (hab q).2.2 (hab (q + 1)).1
      (hab' q).2.1 (hab' q).2.2 (hab' (q + 1)).1
      (hcp q).2 (hIbij q) (hcp (q + 1)) (hIbij (q + 1)).1

end AlgebraicGeometry.Scheme.Modules
