/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineQuotient
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAffineQuotientCone
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # CoherentFormalModulesAffineComplete

Source: Stacks Project, Cohomology of Schemes, Lemma 087W.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Applying a completed-module limit functor to the canonical quotient system recovers
any finite completed module. This is the finite-module half of the equivalence.
Source: Stacks Project, Lemma 087W, implicit converse; Algebra 0316, 05GG and 00MA (3).
(blueprint: lem-weil-pbc-coherent-formal-modules-affine-complete).

Proof: Put B = completion and K = I B. The completion quotient formula identifies
B/K^(n+1) with A/I^(n+1), and makes B K-adically complete. B is Noetherian by 0316.
Every finite B-module N is K-adically complete by 00MA (3); K^m N and I^m N coincide
as A-submodules. The affine ideal-product/cokernel comparison identifies the sections
of Q(N) with N/I^(n+1)N, compatibly with their reductions. The canonical quotient
maps therefore make restricted N a limit cone on these sections. Compare this cone
with the assumed limit cone p(Q(N)) to obtain an A-linear isomorphism N -> L(Q(N)).
It is B-linear: for any completed scalar and any coordinate, choose an A representative
of its residue modulo I^(n+1). Both cone projections carry its action to multiplication
by that representative, by hscalar and the quotient description. Limit projections
jointly distinguish maps, so scalar compatibility at all coordinates proves B-linearity
for this isomorphism and its inverse. Naturality follows by testing on the same
projections, using hnatural and naturality of the quotient maps. These isomorphisms
in the full finite-module subcategory form the asserted natural isomorphism. -/
theorem coherentFormalModules_affine_complete (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (L : CoherentFormalModule (Spec (CommRingCat.of A)) J ⥤
    ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N))
    (p : ∀ F : CoherentFormalModule (Spec (CommRingCat.of A)) J,
      (Functor.const ℕᵒᵖ).obj
        ((ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).obj
          (L.obj F).obj) ⟶ F.obj ⋙ moduleSpecΓFunctor (R := CommRingCat.of A))
    (hlimit : (∀ F, Nonempty (IsLimit (Cone.mk _ (p F)))))
    (hnatural : (∀ (F G : CoherentFormalModule (Spec (CommRingCat.of A)) J) (f : F ⟶ G)
      (n : ℕ),
      (ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))).map
        (L.map f).hom ≫ (p G).app (op n) =
      (p F).app (op n) ≫ (moduleSpecΓFunctor (R := CommRingCat.of A)).map (f.hom.app (op n))))
    (hscalar : (∀ (F : CoherentFormalModule (Spec (CommRingCat.of A)) J) (n : ℕ)
      (r : AdicCompletion I A) (a : A) (x : (L.obj F).obj),
      AdicCompletion.evalₐ I (n + 1) r = Ideal.Quotient.mk (I ^ (n + 1)) a →
      (p F).app (op n) (r • x) = a • (p F).app (op n) x)) :
    Nonempty ((coherentFormalModules_affine_quotientFunctor A I J hJ) ⋙ L ≅ 𝟭 _) := by
  classical
  let Q := coherentFormalModules_affine_quotientFunctor A I J hJ
  let S := ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A))
  let q := fun N ↦ coherentFormalModules_affine_quotientCone A I J N
  have hq := fun N ↦ coherentFormalModules_affine_quotientCone_complete A I J hJ N
  let e := fun N ↦ (hlimit (Q.obj N)).some.conePointUniqueUpToIso (hq N).1.some
  have he (N) (n : ℕᵒᵖ) :
      (e N).hom ≫ (q N.obj).π.app n = (p (Q.obj N)).app n :=
    (hlimit (Q.obj N)).some.conePointUniqueUpToIso_hom_comp (hq N).1.some n
  have heval (N) (n : ℕᵒᵖ) (x) :
      (q N.obj).π.app n ((e N).hom x) = (p (Q.obj N)).app n x :=
    congrArg (fun f ↦ f x) (he N n)
  have hsmul (N) (r : AdicCompletion I A) (x : (L.obj (Q.obj N)).obj) :
      (e N).hom (r • x : (L.obj (Q.obj N)).obj) =
        (@SMul.smul (AdicCompletion I A) N.obj _ r ((e N).hom x)) := by
    apply Concrete.isLimit_ext _ (hq N).1.some
    intro n
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n.unop + 1) r)
    calc
      _ = (p (Q.obj N)).app n (r • x) := heval N n _
      _ = a • (p (Q.obj N)).app n x := hscalar (Q.obj N) n.unop r a x ha.symm
      _ = a • (q N.obj).π.app n ((e N).hom x) :=
        congrArg (a • ·) (heval N n x).symm
      _ = _ := ((hq N).2 n.unop r a ((e N).hom x) ha.symm).symm
  let ε := fun N ↦ ObjectProperty.isoMk _
    (LinearEquiv.toModuleIso
      (show (L.obj (Q.obj N)).obj ≃ₗ[AdicCompletion I A] N.obj from
        { (e N).toLinearEquiv.toAddEquiv with map_smul' := hsmul N }))
  have hqnat {N M : ObjectProperty.FullSubcategory
      (fun N : ModuleCat.{u} (AdicCompletion I A) ↦ Module.Finite (AdicCompletion I A) N)}
      (f : N ⟶ M) (n : ℕᵒᵖ) :
      S.map f.hom ≫ (q M.obj).π.app n =
        (q N.obj).π.app n ≫
          (moduleSpecΓFunctor (R := CommRingCat.of A)).map ((Q.map f).hom.app n) := by
    change S.map f.hom ≫
        ((tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app (S.obj M.obj) ≫
          (moduleSpecΓFunctor (R := CommRingCat.of A)).map
            (formalModuleQuotientπ J (n.unop + 1) _)) =
      ((tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app (S.obj N.obj) ≫
          (moduleSpecΓFunctor (R := CommRingCat.of A)).map
            (formalModuleQuotientπ J (n.unop + 1) _)) ≫
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map
          (formalModuleQuotientMap J
            ((tilde.functor (CommRingCat.of A)).map (S.map f.hom))
            (Nat.le_refl (n.unop + 1)))
    have hη := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.naturality (S.map f.hom)
    dsimp only [Functor.id_map, Functor.comp_map] at hη
    rw [← Category.assoc, hη]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 1
    simp [formalModuleQuotientπ, formalModuleQuotientMap]
  refine ⟨NatIso.ofComponents ε ?_⟩
  intro N M f
  apply ObjectProperty.hom_ext
  ext x
  change (e M).hom ((L.map (Q.map f)).hom x) = f.hom ((e N).hom x)
  apply Concrete.isLimit_ext _ (hq M).1.some
  intro n
  rw [heval]
  have hp := congrArg (fun g ↦ g x) (hnatural (Q.obj N) (Q.obj M) (Q.map f) n.unop)
  have hqn := congrArg (fun g ↦ g ((e N).hom x)) (hqnat f n)
  change (p (Q.obj M)).app n ((L.map (Q.map f)).hom x) =
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map ((Q.map f).hom.app n)
      ((p (Q.obj N)).app n x) at hp
  change (q M.obj).π.app n (f.hom ((e N).hom x)) =
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map ((Q.map f).hom.app n)
      ((q N.obj).π.app n ((e N).hom x)) at hqn
  rw [hqn, heval]
  exact hp

end AlgebraicGeometry
