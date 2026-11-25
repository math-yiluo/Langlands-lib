/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.CategoryTheory.ImageFiltration
import WeilConjectures.CategoryTheory.FinitePageImageLift
import WeilConjectures.CategoryTheory.FinitePageGradedQuotient
import WeilConjectures.CategoryTheory.HalfPlaneSharpBounds

/-! Canonical finite-page quotient comparisons. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem alpha_iso_nonpositive
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q)) (p q : ℤ) (hp : p ≤ 0) :
    IsIso (X.alpha p q) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, p = i + 2 := ⟨p - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, q = j - 1 := ⟨q + 1, by omega⟩
  have hker : kernelSubobject (X.alpha (i + 2) (j - 1)) = ⊥ := by
    have hz : X.f i j = 0 := (hE i j (by omega)).eq_zero_of_src _
    exact (X.exact_alpha i j).symm.trans (by rw [hz, imageSubobject_zero])
  have : Mono (X.alpha (i + 2) (j - 1)) :=
    Abelian.mono_of_kernel_ι_eq_zero _ (Subobject.mk_eq_bot_iff_zero.mp hker)
  have him : imageSubobject (X.alpha (i + 2) (j - 1)) = ⊤ := by
    have hz : X.g (i + 2 - 1) (j - 1 + 1) = 0 :=
      (hE _ _ (by omega)).eq_zero_of_tgt _
    simpa only [hz, kernelSubobject_zero] using X.exact_g (i + 2) (j - 1)
  apply (Subobject.isIso_iff_mk_eq_top _).mpr
  rwa [imageSubobject_mono] at him

private theorem alphaIter_iso_nonpositive
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q))
    (r : ℕ) (p q : ℤ) (hp : p ≤ 0) : IsIso (X.alphaIter r p q) := by
  induction r generalizing p q with
  | zero => dsimp [BigradedExactCouple.alphaIter]; infer_instance
  | succ r ih =>
    have := alpha_iso_nonpositive X hE p q hp
    have := ih (p - 1) (q + 1) (by omega)
    dsimp [BigradedExactCouple.alphaIter]
    infer_instance

private theorem epi_quotient_comparison
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {T U V : B}
    (k : U ⟶ T) [Mono k] (f : T ⟶ V) [Epi f]
    (hk : kernelSubobject f = Subobject.mk k) :
    ∃ e : V ≅ cokernel k, f ≫ e.hom = cokernel.π k := by
  have hzero : k ≫ f = 0 := by
    apply (kernelSubobject_factors_iff f k).mp
    rw [hk]
    exact Subobject.mk_factors_self k
  have hkill : kernel.ι f ≫ cokernel.π k = 0 := by
    apply (kernelSubobject_factors_iff (cokernel.π k) _).mp
    apply Subobject.factors_of_le _ (P := kernelSubobject f)
    · rw [hk]
      change Subobject.mk k ≤ Subobject.mk (kernel.ι (cokernel.π k))
      exact Subobject.mk_le_mk_of_comm
        (kernel.lift (cokernel.π k) k (cokernel.condition k)) (by simp)
    · exact kernelSubobject_factors f _ (kernel.condition f)
  let e : V ≅ cokernel k :=
    { hom := Abelian.epiDesc f (cokernel.π k) hkill
      inv := cokernel.desc k f hzero
      hom_inv_id := by
        apply (cancel_epi f).1
        simp only [← Category.assoc, Abelian.comp_epiDesc, cokernel.π_desc,
          Category.comp_id]
      inv_hom_id := by
        apply (cancel_epi (cokernel.π k)).1
        simp only [← Category.assoc, cokernel.π_desc, Abelian.comp_epiDesc,
          Category.comp_id] }
  exact ⟨e, Abelian.comp_epiDesc f _ hkill⟩

private theorem transport_filtration_graded
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {T U : B}
    (F : PBCDecreasingFiltration T) (G : PBCDecreasingFiltration U)
    (c : T ⟶ U) [IsIso c] (hG : G = F.image c) (p : ℤ) :
    ∃ (gr : F.gradedPiece p ≅ G.gradedPiece p)
      (s : (F.step p : B) ⟶ (G.step p : B)),
      s ≫ (G.step p).arrow = (F.step p).arrow ≫ c ∧
      s ≫ cokernel.π (Subobject.ofLE (G.step (p + 1)) (G.step p)
          (G.antitone_step (by omega))) =
        cokernel.π (Subobject.ofLE (F.step (p + 1)) (F.step p)
          (F.antitone_step (by omega))) ≫ gr.hom := by
  have hm (i : ℤ) : Subobject.mk ((F.step i).arrow ≫ c) = G.step i := by
    rw [hG]
    dsimp [PBCDecreasingFiltration.image]
    rw [Subobject.exists_iso_map]
    conv_rhs => rw [← Subobject.mk_arrow (F.step i), Subobject.map_mk]
  let e (i : ℤ) : (F.step i : B) ≅ (G.step i : B) :=
    Subobject.isoOfMkEq ((F.step i).arrow ≫ c) (G.step i) (hm i)
  have he (i : ℤ) : (e i).hom ≫ (G.step i).arrow = (F.step i).arrow ≫ c := by
    simp [e]
  have hs : Subobject.ofLE (F.step (p + 1)) (F.step p)
        (F.antitone_step (by omega)) ≫ (e p).hom =
      (e (p + 1)).hom ≫ Subobject.ofLE (G.step (p + 1)) (G.step p)
        (G.antitone_step (by omega)) := by
    apply (cancel_mono (G.step p).arrow).1
    simp only [Category.assoc, he, Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow]
  let gr : F.gradedPiece p ≅ G.gradedPiece p :=
    cokernel.mapIso _ _ (e (p + 1)) (e p) hs
  refine ⟨gr, (e p).hom, he p, ?_⟩
  simp only [gr, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]

private theorem stable_page_comparison
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (L : X.LimitSubobjects) (r : ℕ) (p q : ℤ)
    (hZ : X.cycleBoundaryTower.Z r p q = L.Z p q)
    (hB : X.cycleBoundaryTower.B r p q = L.B p q) :
    ∃ e : X.page (r + 2) p q ≅ X.pageInfinity L p q,
      X.cycleBoundaryTower.projection r p q ≫ e.hom =
        eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : B)) hZ) ≫
          cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
            (X.limitBoundary_le_cycle L p q)) := by
  have := X.cycleBoundaryTower.projection_epi r p q
  obtain ⟨e, he⟩ := epi_quotient_comparison
    (Subobject.ofLE _ _ (X.cycleBoundaryTower.B_le_Z r p q))
    (X.cycleBoundaryTower.projection r p q)
    (X.cycleBoundaryTower.projection_kernel r p q)
  let j : cokernel (Subobject.ofLE _ _ (X.cycleBoundaryTower.B_le_Z r p q)) ≅
      X.pageInfinity L p q :=
    cokernel.mapIso _ _
      (eqToIso (congrArg (fun S : Subobject (X.E p q) ↦ (S : B)) hB))
      (eqToIso (congrArg (fun S : Subobject (X.E p q) ↦ (S : B)) hZ)) (by
        apply (cancel_mono (L.Z p q).arrow).1
        simp only [eqToIso.hom, Category.assoc]
        rw [Subobject.arrow_congr _ _ hZ]
        simp only [Subobject.ofLE_arrow]
        exact (Subobject.arrow_congr _ _ hB).symm)
  have hr : r + 2 - 2 = r := by omega
  refine ⟨(eqToIso (by unfold BigradedExactCouple.page; rw [hr])) ≪≫ e ≪≫ j, ?_⟩
  simp only [Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.id_comp,
    ← Category.assoc, he]
  simp only [j, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc, eqToIso.hom]

/-- Stable finite pages are canonical graded quotients of incoming-alpha images.
Source: Stacks Tags 011R, 011T and 012F, blueprint steps 5--6.
(blueprint: lem-sp-abutment-finite-page-comparison)

Proof: For p>=0 put R=max(p+3,q-a+2),
u=p-R+2 and v=q+R-2. The alpha iterate from (0,p+q) to (u,v) is invertible:
all intervening negative-first-index E terms vanish. Iterating the derived-D
image construction identifies D_(R-2)(u,v) with the incoming p-fold alpha image
under this isomorphism. The induced lift is invertible, and its equation follows
by induction from the given recursive inclusions. The incoming derived alpha
image corresponds to the next filtration step. The target of the derived f map
is zero by the D lower bound. Derived-couple exactness consequently makes g a
cokernel of the next step, inducing psi with the stated quotient equation.
Transport the two adjacent steps along c, giving cStep and the induced graded
isomorphism grc. Stabilization at R identifies cycles and boundaries with L;
the quotient universal property gives stable with its projection equation.
Finally set Theta=grc.symm followed by psi and stable. These arguments also
apply when q<a: both quotient objects vanish, and the same universal properties
supply all maps and equations. -/
theorem abutment_finite_page_comparison
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (hDzero : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hEzero : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (inc : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).D p q ⟶ X.D p q)
    (hinc0 : ∀ p q : ℤ, inc 0 p q = 𝟙 _)
    (hinc : ∀ (r : ℕ) (p q : ℤ), inc (r + 1) p q =
      (X.pageCouple r).derivedDInclusion p q ≫ inc r p q)
    (L : X.LimitSubobjects)
    (hL : ∀ p q : ℤ,
      L.Z p q = X.cycleBoundaryTower.Z
        ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q ∧
      L.B p q = X.cycleBoundaryTower.B
        ((max 2 (max (q - a + 2) (p + 1))).toNat - 2) p q)
    (H : ℤ → B) (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
    (hiso : ∀ n : ℤ, IsIso (c n))
    (FA : ∀ n : ℤ, PBCDecreasingFiltration (X.D 0 n))
    (FH : ∀ n : ℤ, PBCDecreasingFiltration (H n))
    (hFA : ∀ n p : ℤ, 0 ≤ p → (FA n).step p =
      imageSubobject (X.incomingAlphaIter p.toNat 0 n))
    (hFH : ∀ n : ℤ, FH n = (FA n).image (c n)) :
        (∀ (p q : ℤ) (hp : 0 ≤ p),
          ∃ (lambda : X.D 0 (p + q) ⟶
              X.D (p - max (p + 3) (q - a + 2) + 2) (q + max (p + 3) (q - a + 2) - 2))
            (lift : ((FA (p + q)).step p : B) ⟶
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).D
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2))
            (psi : (FA (p + q)).gradedPiece p ≅
              X.page (max (p + 3) (q - a + 2)).toNat p q)
            (grc : (FA (p + q)).gradedPiece p ≅ (FH (p + q)).gradedPiece p)
            (stable : X.page (max (p + 3) (q - a + 2)).toNat p q ≅
              X.pageInfinity L p q)
            (Theta : (FH (p + q)).gradedPiece p ≅ X.pageInfinity L p q)
            (cStep : ((FA (p + q)).step p : B) ⟶ ((FH (p + q)).step p : B))
            (hZ : X.cycleBoundaryTower.Z
                ((max (p + 3) (q - a + 2)).toNat - 2) p q = L.Z p q),
            IsIso lambda ∧
            lambda = X.alphaIter
              (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) ≫
                eqToHom (by congr 1 <;> omega) ∧
            IsIso lift ∧
            lift ≫ inc ((max (p + 3) (q - a + 2)).toNat - 2)
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) =
              ((FA (p + q)).step p).arrow ≫ lambda ∧
            cStep ≫ ((FH (p + q)).step p).arrow =
              ((FA (p + q)).step p).arrow ≫ c (p + q) ∧
            cStep ≫ cokernel.π (Subobject.ofLE ((FH (p + q)).step (p + 1))
                ((FH (p + q)).step p) ((FH (p + q)).antitone_step (by omega))) =
              cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫ grc.hom ∧
            X.cycleBoundaryTower.projection
                ((max (p + 3) (q - a + 2)).toNat - 2) p q ≫ stable.hom =
              eqToHom (congrArg (fun S : Subobject (X.E p q) ↦ (S : B)) hZ) ≫
                cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
                  (X.limitBoundary_le_cycle L p q)) ∧
            cokernel.π (Subobject.ofLE ((FA (p + q)).step (p + 1))
                ((FA (p + q)).step p) ((FA (p + q)).antitone_step (by omega))) ≫
              psi.hom = lift ≫
              (X.pageCouple ((max (p + 3) (q - a + 2)).toNat - 2)).g
                (p - max (p + 3) (q - a + 2) + 2)
                (q + max (p + 3) (q - a + 2) - 2) ≫
              eqToHom (by unfold BigradedExactCouple.page; congr 1 <;> omega) ∧
            Theta = grc.symm ≪≫ psi ≪≫ stable) := by
  intro p q hp
  let lambda : X.D 0 (p + q) ⟶
      X.D (p - max (p + 3) (q - a + 2) + 2)
        (q + max (p + 3) (q - a + 2) - 2) :=
    X.alphaIter (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) ≫
      eqToHom (by congr 1 <;> omega)
  have hlambda : IsIso lambda := by
    have := alphaIter_iso_nonpositive X (fun i j hi ↦ hEzero i j (Or.inl hi))
      (-(p - max (p + 3) (q - a + 2) + 2)).toNat 0 (p + q) le_rfl
    dsimp [lambda]
    infer_instance
  obtain ⟨lift, hlift, hliftinc⟩ :=
    finitePage_image_lift X a inc hinc0 hinc p q hp (FA (p + q))
      (hFA (p + q)) lambda rfl
  obtain ⟨psi, hpsi⟩ :=
    finitePage_graded_quotient X a hDzero inc hinc0 hinc p q hp (FA (p + q))
      (hFA (p + q)) lambda rfl lift hlift hliftinc
  have := hiso (p + q)
  obtain ⟨grc, cStep, hcStep, hgrc⟩ :=
    transport_filtration_graded (FA (p + q)) (FH (p + q)) (c (p + q))
      (hFH (p + q)) p
  have hR : 2 ≤ max (p + 3) (q - a + 2) := by omega
  have hbound : max 2 (max (q - a + 2) (p + 1)) ≤
      ((max (p + 3) (q - a + 2)).toNat : ℤ) := by omega
  obtain ⟨_, _, _, _, hstab, _⟩ := halfPlane_sharp_bounds X a hDzero hEzero
  obtain ⟨hZ0, hB0⟩ := hstab p q (max (p + 3) (q - a + 2)).toNat hbound
  have hZ := hZ0.trans (hL p q).1.symm
  have hB := hB0.trans (hL p q).2.symm
  obtain ⟨stable0, hstable⟩ := stable_page_comparison X L
    ((max (p + 3) (q - a + 2)).toNat - 2) p q hZ hB
  have hpage : (max (p + 3) (q - a + 2)).toNat - 2 + 2 =
      (max (p + 3) (q - a + 2)).toNat := by omega
  let stable : X.page (max (p + 3) (q - a + 2)).toNat p q ≅
      X.pageInfinity L p q :=
    eqToIso (congrArg (fun r ↦ X.page r p q) hpage.symm) ≪≫ stable0
  refine ⟨lambda, lift, psi, grc, stable, grc.symm ≪≫ psi ≪≫ stable, cStep, hZ,
    hlambda, rfl, hlift, hliftinc, hcStep, hgrc, ?_, hpsi, rfl⟩
  simpa only [stable, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.id_comp]
    using hstable

end CategoryTheory
