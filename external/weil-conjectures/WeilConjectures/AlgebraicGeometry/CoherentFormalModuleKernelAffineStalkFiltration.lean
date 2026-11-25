/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Order.Hom.Basic

import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelAffineSectionQuotients
import WeilConjectures.AlgebraicGeometry.AffineIntersectionQuotientsStalk
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Affine intersection-filtration models for stabilized kernel stalks

Source: Stacks Project, Lemmas 087W and 087X, affine calculation for claim (a).
(blueprint: lem-weil-pbc-formal-kernel-affine-stalk-filtration).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- On an affine open, stabilized kernel stalks have the intersection filtration of
one submodule of a finite completed module. No bound for this filtration is asserted.

Source: Stacks Project, Lemmas 087W and 087X, affine calculation for claims (a) and (b),
and Tags 01IB and 01IC for the affine module/sheaf correspondence.
(blueprint: lem-weil-pbc-formal-kernel-affine-stalk-filtration).

Proof: Put A = Gamma(U,O_X), R = its I(U)-adic completion, and K = I(U)R.
The affine equivalence 087W identifies the restrictions of F and H with finite
R-modules N and P and alpha with f : N -> P, with level m given by reduction
modulo K^(m+1). Take L = ker(f). Artin--Rees applied to the image of f gives a
bound a for images of reduced kernels. For fixed m compare the image at level
m+c with that at l = max(m+c,m+a): hc identifies these images, while the
reduced-kernel calculation identifies the latter with the image of L. Thus hS
identifies S_m on U with L/(L intersect K^(m+1)N), compatibly with its inclusion
in F_m. The inclusions are monic, so naturality of j makes these identifications
compatible with every transition map, not only consecutive ones.
For x in U restrict L's scalars to A and localize at the prime corresponding to
x; call the resulting stalk module M. Exactness of localization gives the
surjective quotient maps p_m and their displayed kernels. For a submodule Q of L,
define phi(Q) to be the image of its scalar restriction after localization in M.
Inclusions give an order homomorphism phi. Scalar restriction carries K^r L to
I(U)^r L, since K is the extended ideal, including r = 0. Localization commutes
with ideal products, so phi(K^r L) = J^r M: the ideal-product stalk theorem and
the germ equation for e identify the localized ideal with J. The kernel formula
is exactness applied to L intersect K^(m+1)N. Empty U has no stalk conditions;
zero modules, zero ideals and unit ideals give the same quotient computations.
This construction uses no Artin--Rees assertion for L inside N and no finite cover. -/
theorem coherentFormalModule_kernel_affine_stalk_filtration
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m))
    (U : X.affineOpens) :
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let K := (I.ideal U).map (algebraMap A R)
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧
      ∃ L : Submodule R N, ∀ (x : X), x ∈ U.1 →
        ∀ e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
            (SheafOfModules.unit X.ringCatSheaf) ≅
            ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
        (∀ (V : X.Opens) (hx : x ∈ V) (r : Γ(X, V)),
          e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
            V x hx r) = X.presheaf.germ V x hx r) →
        let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
        let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
        ∃ M : ModuleCat.{u} (X.presheaf.stalk x),
          ∃ p : ∀ m : ℕ, M →ₗ[X.presheaf.stalk x] T.obj (S.obj (op m)),
            (∀ m : ℕ, Function.Surjective (p m)) ∧
            (∀ (a b : ℕ) (h : a ≤ b) (z : M),
              (T.map (S.map (homOfLE h).op)).hom (p b z) = p a z) ∧
            ∃ φ : Submodule R L →o Submodule (X.presheaf.stalk x) M,
              (∀ r : ℕ, φ (K ^ r • (⊤ : Submodule R L)) =
                J ^ r • (⊤ : Submodule (X.presheaf.stalk x) M)) ∧
              (∀ m : ℕ, LinearMap.ker (p m) =
                φ ((K ^ (m + 1) • (⊤ : Submodule R N)).comap L.subtype)) := by
  obtain ⟨N, hN, L, q, hq, ht, hk⟩ :=
    coherentFormalModule_kernel_affine_section_quotients I F H α c S j hc hS U
  have hqc (m : ℕ) : (S.obj (op m)).IsQuasicoherent := by
    have : (F.obj.obj (op (m + c))).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (F.property.1 (m + c))).1
    have : (F.obj.obj (op m)).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (F.property.1 m)).1
    have : (H.obj.obj (op (m + c))).IsQuasicoherent :=
      ((Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mp
        (H.property.1 (m + c))).1
    have := Scheme.Modules.isQuasicoherent_kernel (α.hom.app (op (m + c)))
    let f := kernel.ι (α.hom.app (op (m + c))) ≫
      F.obj.map (homOfLE (Nat.le_add_right m c)).op
    have him := Scheme.Modules.quasiCoherent_cokernel_image f
    obtain ⟨a, _⟩ := hS m
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso a.symm
      him.2.2.2.2.2.2.2.1
  refine ⟨N, hN, L, ?_⟩
  intro x hx e he
  exact affine_intersection_quotients_stalk I S U
    (AdicCompletion (I.ideal U) Γ(X, U.1)) (ModuleCat.of _ L)
    (fun m ↦ (((I.ideal U).map (algebraMap Γ(X, U.1)
      (AdicCompletion (I.ideal U) Γ(X, U.1)))) ^ (m + 1) •
        (⊤ : Submodule _ N)).comap L.subtype) q hqc hq ht hk x hx e he

end AlgebraicGeometry
