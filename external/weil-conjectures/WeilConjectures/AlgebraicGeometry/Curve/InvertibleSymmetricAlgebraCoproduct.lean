/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # The homogeneous coproduct of a line bundle's symmetric algebra

Source: Stacks Project, Modules, Section 01CF; Schemes, Section 01LA (9); Tag 09MS.
(blueprint: lem-sc-invertible-symmetric-algebra-coproduct).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Multiplicative tensor-power maps to a locally symmetric algebra of a line bundle
are a coproduct cofan of module sheaves.

Source: Stacks Project, Modules, Section 01CF; Schemes, Section 01LA (9); Tag 09MS.
(blueprint: lem-sc-invertible-symmetric-algebra-coproduct).
Proof: Refine the affine cover by affine opens on which L has a frame e. The affine
comparison identifies B there with Sym(L(U)), hence with O(U)[T], sending j(e) to T.
The degree-zero and degree-one conditions and multiplicativity identify b_d(e^d) with
T^d. These identifications persist on smaller affine opens: the symmetric algebra
comparison is determined by the structure map and its values on degree one, so it
commutes with restrictions. The tensor powers have frames e^d, and polynomial modules
are direct sums of their monomials. A family of module-sheaf maps from L^d to any M
therefore extends locally to B by finite summation of coefficients times the images
of e^d. Sheafify the polynomial-module presheaf to extend to arbitrary opens, whose
sections need only be locally finite sums. On intersections the extensions agree,
since both send each b_d to the prescribed map and the local polynomial expansion
is unique. Sheaf gluing gives the global desc map. The same local calculation proves
its factorization through every b_d and uniqueness; these three facts define IsColimit.
No global direct-sum formula for sections is used. Empty opens have the unique map;
zero coefficients and degree zero are covered by the polynomial expansion. -/
theorem isColimit_invertible_symmetricAlgebra_cofan {X : Scheme.{u}}
    (L : X.Modules) [L.IsInvertible] (B : X.CommAlgebraSheaf)
    (j : L ⟶ commAlgebraSheafModule X.sheaf B)
    (b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B)
    (hAffine : ∀ U : X.affineOpens,
      ∃ e : SymmetricAlgebra (X.presheaf.obj (op U.1)) (L.val.obj (op U.1)) ≃+*
          B.right.obj.obj (op U.1),
        (∀ r : X.presheaf.obj (op U.1),
          e (algebraMap (X.presheaf.obj (op U.1))
            (SymmetricAlgebra (X.presheaf.obj (op U.1)) (L.val.obj (op U.1))) r) =
            B.hom.hom.app (op U.1) r) ∧
        (∀ x : L.val.obj (op U.1),
          e (SymmetricAlgebra.ι (X.presheaf.obj (op U.1)) (L.val.obj (op U.1)) x) =
            j.val.app (op U.1) x))
    (hZero : ∀ (U : X.Opens) (r : Γ(X, U)),
      (b 0).app U (unitSectionsEquiv U r) = B.hom.hom.app (op U) r)
    (hOne : b 1 = (ρ_ L).hom ≫ j)
    (hMul : ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
      (t : Γ(L.tensorPow d, U)),
      (show B.right.obj.obj (op U) from (b a).app U s) *
        (show B.right.obj.obj (op U) from (b d).app U t) =
        (show B.right.obj.obj (op U) from
          (b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t)))) :
    Nonempty (IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf B) b)) := by
  classical
  -- The homogeneous images generate every affine section additively.
  have hgen (U : X.affineOpens) (z : B.right.obj.obj (op U.1)) :
      z ∈ AddSubgroup.closure {y : B.right.obj.obj (op U.1) |
        ∃ (d : ℕ) (s : Γ(L.tensorPow d, U.1)), (b d).app U.1 s = y} := by
    let S : Set (B.right.obj.obj (op U.1)) :=
      {y | ∃ (d : ℕ) (s : Γ(L.tensorPow d, U.1)), (b d).app U.1 s = y}
    let H := AddSubgroup.closure S
    have hprod {x y : B.right.obj.obj (op U.1)} (hx : x ∈ H) (hy : y ∈ H) :
        x * y ∈ H := by
      induction hx, hy using AddSubgroup.closure_induction₂ with
      | mem x y hx hy =>
        obtain ⟨a, s, rfl⟩ := hx
        obtain ⟨d, t, rfl⟩ := hy
        apply AddSubgroup.subset_closure
        exact ⟨a + d, (L.tensorPowAddIso a d).inv.app U.1 (tmulSection s t),
          (hMul U.1 a d s t).symm⟩
      | zero_left => simp
      | zero_right => simp
      | add_left _ _ _ _ _ _ hx hy => simpa [add_mul] using H.add_mem hx hy
      | add_right _ _ _ _ _ _ hx hy => simpa [mul_add] using H.add_mem hx hy
      | neg_left _ _ _ _ hx => simpa using H.neg_mem hx
      | neg_right _ _ _ _ hx => simpa using H.neg_mem hx
    obtain ⟨e, he0, he1⟩ := hAffine U
    obtain ⟨z, rfl⟩ := e.surjective z
    induction z using SymmetricAlgebra.induction with
    | algebraMap r =>
      rw [he0]
      exact AddSubgroup.subset_closure ⟨0, unitSectionsEquiv U.1 r, hZero U.1 r⟩
    | ι x =>
      rw [he1]
      apply AddSubgroup.subset_closure
      refine ⟨1, (ρ_ L).inv.app U.1 x, ?_⟩
      rw [hOne]
      change Hom.app ((ρ_ L).inv ≫ (ρ_ L).hom ≫ j) U.1 x = j.val.app (op U.1) x
      rw [Iso.inv_hom_id_assoc]
      rfl
    | mul x y hx hy => simpa only [map_mul] using hprod hx hy
    | add x y hx hy => simpa only [map_add] using H.add_mem hx hy
  -- Generation and sheaf separation give global uniqueness.
  have hext (M : X.Modules) (f g : commAlgebraSheafModule X.sheaf B ⟶ M)
      (hfg : ∀ d, b d ≫ f = b d ≫ g) : f = g := by
    have haff (U : X.affineOpens) (z : B.right.obj.obj (op U.1)) :
        Hom.app f U.1 z = Hom.app g U.1 z := by
      apply AddMonoidHom.eqOn_closure
        (f := (Hom.app f U.1).hom)
        (g := (Hom.app g U.1).hom) ?_ (hgen U z)
      rintro _ ⟨d, s, rfl⟩
      exact congrArg (fun k ↦ Hom.app k U.1 s) (hfg d)
    refine hom_ext f g fun U ↦ ?_
    ext z
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
      (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U
      (fun i ↦ homOfLE i.2) ?_ (Hom.app f U z) (Hom.app g U z) fun i ↦ ?_
    · intro y hy
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
    · rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
      exact haff i.1 _
  -- Polynomial coefficients give independence, checked on framed neighbourhoods.
  have hinj (U : X.affineOpens) : Function.Injective
      (DirectSum.toModule (Γ(X, U.1)) ℕ (Γ(commAlgebraSheafModule X.sheaf B, U.1))
        (fun d ↦ ((b d).val.app (op U.1)).hom)) := by
    let N : X.Modules := commAlgebraSheafModule X.sheaf B
    let sumB (V : X.affineOpens) :=
      DirectSum.toModule (Γ(X, V.1)) ℕ (Γ(N, V.1))
        (fun d ↦ ((b d).val.app (op V.1)).hom)
    have hlocal (V : X.affineOpens) (g : Γ(L, V.1)) (hg : IsFreeGenerator g) :
        Function.Injective (sumB V) := by
      let g1 : Γ(L.tensorPow 1, V.1) := (ρ_ L).inv.app V.1 g
      have hg1 : IsFreeGenerator g1 := hg.app_hom (ρ_ L).symm
      have hg0 : IsFreeGenerator (unitSectionsEquiv V.1 1) := by
        intro W hW
        simpa only [presheaf_map_unitSectionsEquiv, map_one,
          ← unitSectionsEquiv_eq_smul_one] using (unitSectionsEquiv W).bijective
      let frame : (d : ℕ) → Γ(L.tensorPow d, V.1) :=
        Nat.rec (unitSectionsEquiv V.1 1)
          (fun n s ↦ (L.tensorPowAddIso n 1).inv.app V.1 (tmulSection s g1))
      have hframe (d : ℕ) : IsFreeGenerator (frame d) := by
        induction d with
        | zero => exact hg0
        | succ d hd => exact (hd.tmulSection hg1).app_hom (L.tensorPowAddIso d 1).symm
      let eg : Γ(X, V.1) ≃ₗ[Γ(X, V.1)] Γ(L, V.1) :=
        LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _ g) hg.bijective
      let bg : Module.Basis Unit (Γ(X, V.1)) Γ(L, V.1) :=
        (Module.Basis.singleton Unit (Γ(X, V.1))).map eg
      have hbg : bg () = g := by simp [bg, eg, LinearMap.toSpanSingleton_apply]
      obtain ⟨a, ha0, ha1⟩ := hAffine V
      let poly : B.right.obj.obj (op V.1) ≃+* Polynomial (Γ(X, V.1)) :=
        a.symm.trans ((SymmetricAlgebra.equivMvPolynomial bg).toRingEquiv.trans
          (MvPolynomial.uniqueAlgEquiv (Γ(X, V.1)) Unit).toRingEquiv)
      have hp0 (r : Γ(X, V.1)) : poly (B.hom.hom.app (op V.1) r) = Polynomial.C r := by
        rw [← ha0]
        simp [poly]
      have hp1 : poly (j.val.app (op V.1) g) = Polynomial.X := by
        rw [← ha1, ← hbg]
        dsimp only [poly, RingEquiv.trans_apply]
        rw [a.symm_apply_apply]
        change (MvPolynomial.uniqueAlgEquiv (Γ(X, V.1)) Unit)
          (SymmetricAlgebra.equivMvPolynomial bg (SymmetricAlgebra.ι _ _ (bg ()))) = _
        rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
        simp [MvPolynomial.uniqueAlgEquiv]
      have hb1 : (b 1).app V.1 g1 = j.val.app (op V.1) g := by
        rw [hOne]
        change Hom.app ((ρ_ L).inv ≫ (ρ_ L).hom ≫ j) V.1 g = _
        rw [Iso.inv_hom_id_assoc]
        rfl
      have hpframe (d : ℕ) : poly ((b d).app V.1 (frame d)) = Polynomial.X ^ d := by
        induction d with
        | zero =>
          change poly ((b 0).app V.1 (unitSectionsEquiv V.1 1)) = _
          rw [hZero, hp0, Polynomial.C_1, pow_zero]
        | succ d hd =>
          change poly ((b (d + 1)).app V.1
            ((L.tensorPowAddIso d 1).inv.app V.1 (tmulSection (frame d) g1))) = _
          have hm := congrArg poly (hMul V.1 d 1 (frame d) g1)
          exact hm.symm.trans (by rw [map_mul, hb1, hp1, hd, pow_succ])
      have hp (d : ℕ) (s : Γ(L.tensorPow d, V.1)) :
          poly ((b d).app V.1 s) =
            Polynomial.monomial d ((hframe d).coeff s) := by
        obtain ⟨r, rfl⟩ := (hframe d).exists_smul_eq s
        rw [(hframe d).coeff_smul_self]
        have hb : (show B.right.obj.obj (op V.1) from (b d).app V.1 (r • frame d)) =
            B.hom.hom.app (op V.1) r *
              (show B.right.obj.obj (op V.1) from (b d).app V.1 (frame d)) :=
          (b d).val.app (op V.1) |>.hom.map_smul r (frame d)
        exact (congrArg poly hb).trans (by
          rw [map_mul, hp0, hpframe, Polynomial.C_mul_X_pow_eq_monomial])
      have hcoeff (v : DirectSum ℕ (fun d ↦ Γ(L.tensorPow d, V.1))) (d : ℕ) :
          (poly (sumB V v)).coeff d = (hframe d).coeff (v d) := by
        induction v using DirectSum.induction_on with
        | zero => simp [sumB]
        | of a s =>
          change (poly (sumB V (DirectSum.lof (Γ(X, V.1)) ℕ
            (fun d ↦ Γ(L.tensorPow d, V.1)) a s))).coeff d = _
          have he : sumB V (DirectSum.lof (Γ(X, V.1)) ℕ
              (fun d ↦ Γ(L.tensorPow d, V.1)) a s) = (b a).app V.1 s :=
            DirectSum.toModule_lof _ _ _
          rw [he, hp]
          by_cases h : a = d
          · subst a
            simp
          · simp [Polynomial.coeff_monomial, h, DirectSum.of_apply]
        | add x y hx hy =>
          rw [map_add, map_add, Polynomial.coeff_add, hx, hy, DFinsupp.add_apply,
            (hframe d).coeff_add]
      intro x y hxy
      ext d
      have hc := congrArg (fun z ↦ (poly z).coeff d) hxy
      rw [hcoeff, hcoeff] at hc
      exact (hframe d).coeff_smul (x d) |>.symm.trans
        ((congrArg (fun r ↦ r • frame d) hc).trans ((hframe d).coeff_smul (y d)))
    let restrict (V : X.affineOpens) (h : V.1 ≤ U.1) :
        DirectSum ℕ (fun d ↦ Γ(L.tensorPow d, U.1)) →+
          DirectSum ℕ (fun d ↦ Γ(L.tensorPow d, V.1)) :=
      DirectSum.toAddMonoid (fun d ↦
        (DirectSum.of (fun d ↦ Γ(L.tensorPow d, V.1)) d).comp
          ((L.tensorPow d).presheaf.map (homOfLE h).op).hom)
    have restrict_apply (V : X.affineOpens) (h : V.1 ≤ U.1)
        (v : DirectSum ℕ (fun d ↦ Γ(L.tensorPow d, U.1))) (d : ℕ) :
        restrict V h v d = (L.tensorPow d).presheaf.map (homOfLE h).op (v d) := by
      induction v using DirectSum.induction_on with
      | zero => simp [restrict]
      | of a s =>
        simp only [restrict, DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply]
        by_cases ha : a = d
        · subst a
          simp
        · simp [DirectSum.of_apply, ha]
      | add x y hx hy =>
        rw [map_add]
        change restrict V h x d + restrict V h y d =
          (L.tensorPow d).presheaf.map (homOfLE h).op (x d + y d)
        rw [map_add, hx, hy]
    have restrict_sum (V : X.affineOpens) (h : V.1 ≤ U.1)
        (v : DirectSum ℕ (fun d ↦ Γ(L.tensorPow d, U.1))) :
        sumB V (restrict V h v) = N.presheaf.map (homOfLE h).op (sumB U v) := by
      induction v using DirectSum.induction_on with
      | zero => simp [restrict]
      | of a s =>
        change sumB V (restrict V h (DirectSum.lof (Γ(X, U.1)) ℕ
          (fun d ↦ Γ(L.tensorPow d, U.1)) a s)) = _
        have hr : restrict V h (DirectSum.lof (Γ(X, U.1)) ℕ
            (fun d ↦ Γ(L.tensorPow d, U.1)) a s) =
            DirectSum.lof (Γ(X, V.1)) ℕ (fun d ↦ Γ(L.tensorPow d, V.1)) a
              ((L.tensorPow a).presheaf.map (homOfLE h).op s) :=
          DirectSum.toAddMonoid_of _ _ _
        rw [hr]
        have hv : sumB V (DirectSum.lof (Γ(X, V.1)) ℕ
            (fun d ↦ Γ(L.tensorPow d, V.1)) a
              ((L.tensorPow a).presheaf.map (homOfLE h).op s)) =
            (b a).app V.1 ((L.tensorPow a).presheaf.map (homOfLE h).op s) :=
          DirectSum.toModule_lof _ _ _
        have hu : sumB U (DirectSum.lof (Γ(X, U.1)) ℕ
            (fun d ↦ Γ(L.tensorPow d, U.1)) a s) = (b a).app U.1 s :=
          DirectSum.toModule_lof _ _ _
        rw [hv]
        change (b a).app V.1 ((L.tensorPow a).presheaf.map (homOfLE h).op s) =
          N.presheaf.map (homOfLE h).op (sumB U (DirectSum.lof (Γ(X, U.1)) ℕ
            (fun d ↦ Γ(L.tensorPow d, U.1)) a s))
        rw [hu]
        exact Hom.app_presheaf_map (b a) (homOfLE h) s
      | add x y hx hy => simp only [map_add, hx, hy]
    have : SheafOfModules.IsInvertible.{u, u, u} L :=
      IsInvertible.sheafOfModules_isInvertible L
    intro x y hxy
    ext d
    apply TopCat.Presheaf.IsSheaf.section_ext (L.tensorPow d).isSheaf
    intro z hz
    obtain ⟨V, hzV, hVU, g, hg⟩ := exists_isFreeGenerator L hz
    refine ⟨V.1, hVU, hzV, ?_⟩
    have h := hlocal V g hg (show sumB V (restrict V hVU x) =
        sumB V (restrict V hVU y) by rw [restrict_sum, restrict_sum, hxy])
    exact (restrict_apply V hVU x d).symm.trans
      ((congrArg (fun v ↦ v d) h).trans (restrict_apply V hVU y d))
  -- Invert the affine finite-sum map and extend the resulting maps from the basis.
  have hexists (M : X.Modules) (c : ∀ d : ℕ, L.tensorPow d ⟶ M) :
      ∃ f : commAlgebraSheafModule X.sheaf B ⟶ M, ∀ d, b d ≫ f = c d := by
    let N : X.Modules := commAlgebraSheafModule X.sheaf B
    let sumB (U : X.affineOpens) :=
      DirectSum.toModule (Γ(X, U.1)) ℕ (Γ(N, U.1))
        (fun d ↦ ((b d).val.app (op U.1)).hom)
    have hsurj (U : X.affineOpens) : Function.Surjective (sumB U) := by
      intro z
      have h := hgen U z
      apply (AddSubgroup.closure_le
        (K := (LinearMap.range (sumB U)).toAddSubgroup)).mpr ?_ h
      rintro _ ⟨d, s, rfl⟩
      exact ⟨DirectSum.lof (Γ(X, U.1)) ℕ (fun d ↦ Γ(L.tensorPow d, U.1)) d s,
        DirectSum.toModule_lof _ _ _⟩
    let e (U : X.affineOpens) := LinearEquiv.ofBijective (sumB U) ⟨hinj U, hsurj U⟩
    let localMap (U : X.affineOpens) : Γ(N, U.1) →ₗ[Γ(X, U.1)] Γ(M, U.1) :=
      (DirectSum.toModule (Γ(X, U.1)) ℕ (Γ(M, U.1))
        (fun d ↦ ((c d).val.app (op U.1)).hom)) ∘ₗ (e U).symm.toLinearMap
    have localFac (U : X.affineOpens) (d : ℕ) (s : Γ(L.tensorPow d, U.1)) :
        localMap U ((b d).app U.1 s) = (c d).app U.1 s := by
      have he : e U (DirectSum.lof (Γ(X, U.1)) ℕ
          (fun d ↦ Γ(L.tensorPow d, U.1)) d s) = (b d).app U.1 s :=
        DirectSum.toModule_lof _ _ _
      rw [← he]
      simp only [localMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      exact DirectSum.toModule_lof _ _ _
    have localNat (U V : X.affineOpens) (i : V.1 ⟶ U.1) (z : Γ(N, U.1)) :
        M.presheaf.map i.op (localMap U z) =
          localMap V (N.presheaf.map i.op z) := by
      apply AddMonoidHom.eqOn_closure
        (f := (M.presheaf.map i.op).hom.comp (localMap U).toAddMonoidHom)
        (g := (localMap V).toAddMonoidHom.comp (N.presheaf.map i.op).hom) ?_ (hgen U z)
      rintro _ ⟨d, s, rfl⟩
      change M.presheaf.map i.op (localMap U ((b d).app U.1 s)) =
        localMap V (N.presheaf.map i.op ((b d).app U.1 s))
      rw [localFac, ← Hom.app_presheaf_map, ← Hom.app_presheaf_map, localFac]
    have hbasis : TopologicalSpace.Opens.IsBasis
        (Set.range (fun U : X.affineOpens ↦ U.1)) := by
      simpa only [Subtype.range_coe] using X.isBasis_affineOpens
    let alpha : (CategoryTheory.inducedFunctor (fun U : X.affineOpens ↦ U.1)).op ⋙
        N.presheaf ⟶
        (CategoryTheory.inducedFunctor (fun U : X.affineOpens ↦ U.1)).op ⋙ M.presheaf :=
      { app := fun U ↦ AddCommGrpCat.ofHom (localMap U.unop).toAddMonoidHom
        naturality := by
          intro U V i
          ext z
          exact (localNat U.unop V.unop
            ((CategoryTheory.inducedFunctor (fun U : X.affineOpens ↦ U.1)).map i.unop) z).symm }
    let f := TopCat.Sheaf.restrictHomEquivHom N.presheaf ⟨M.presheaf, M.isSheaf⟩
      hbasis alpha
    have fAffine (U : X.affineOpens) (z : Γ(N, U.1)) :
        f.app (op U.1) z = localMap U z := by
      change (TopCat.Sheaf.restrictHomEquivHom N.presheaf
        ⟨M.presheaf, M.isSheaf⟩ hbasis alpha).app (op U.1) z = _
      rw [TopCat.Sheaf.extend_hom_app]
      rfl
    have fLinear (U : (TopologicalSpace.Opens X)ᵒᵖ)
        (r : X.ringCatSheaf.obj.obj U) (z : N.val.obj U) :
        f.app U (r • z) = r • (show M.val.obj U from f.app U z) := by
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
        (fun i : {V : X.affineOpens // V.1 ≤ U.unop} ↦ i.1.1) U.unop
        (fun i ↦ homOfLE i.2) ?_ _ _ fun i ↦ ?_
      · intro y hy
        obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open hy U.unop.2
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
      · have hf (z : N.val.obj U) :
            M.presheaf.map (homOfLE i.2).op (f.app U z) =
              f.app (op i.1.1) (N.presheaf.map (homOfLE i.2).op z) :=
          (ConcreteCategory.congr_hom (f.naturality (homOfLE i.2).op) z).symm
        rw [hf]
        change f.app (op i.1.1) (N.val.map (homOfLE i.2).op (r • z)) =
          M.val.map (homOfLE i.2).op (r • (show M.val.obj U from f.app U z))
        have hf' : M.val.map (homOfLE i.2).op
            (show M.val.obj U from f.app U z) =
              f.app (op i.1.1) (N.val.map (homOfLE i.2).op z) := hf z
        rw [N.val.map_smul, M.val.map_smul, hf', fAffine, fAffine]
        exact (localMap i.1).map_smul _ _
    let fm : N ⟶ M := ⟨PresheafOfModules.homMk f fLinear⟩
    refine ⟨fm, ?_⟩
    intro d
    refine hom_ext (b d ≫ fm) (c d) fun U ↦ ?_
    ext z
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
      (fun i : {V : X.affineOpens // V.1 ≤ U} ↦ i.1.1) U
      (fun i ↦ homOfLE i.2) ?_ _ _ fun i ↦ ?_
    · intro y hy
      obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
    · rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
      change f.app (op i.1.1) ((b d).app i.1.1 _) = (c d).app i.1.1 _
      rw [fAffine, localFac]
  let desc (t : Cofan (fun d ↦ L.tensorPow d)) :=
    Classical.choose (hexists t.pt t.inj)
  have hfac (t : Cofan (fun d ↦ L.tensorPow d)) (d : ℕ) :
      (Cofan.mk (commAlgebraSheafModule X.sheaf B) b).inj d ≫ desc t = t.inj d :=
    Classical.choose_spec (hexists t.pt t.inj) d
  refine ⟨Cofan.IsColimit.mk _ desc hfac ?_⟩
  intro t m hm
  apply hext t.pt m (desc t)
  intro d
  exact (hm d).trans (hfac t d).symm

end
end AlgebraicGeometry.Scheme.Modules
