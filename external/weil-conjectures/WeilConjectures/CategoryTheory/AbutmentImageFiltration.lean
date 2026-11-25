/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
public import WeilConjectures.CategoryTheory.ImageFiltration
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.CategoryTheory.HalfPlaneDiagonalColimits
import WeilConjectures.CategoryTheory.HalfPlaneSharpBounds
import WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence

/-! Transport of a half-plane image filtration along an invertible cocone. -/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem ofLE_isIso_of_eq
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {T : B}
    (S U : Subobject T) (h : S ≤ U) (heq : S = U) : IsIso (Subobject.ofLE S U h) := by
  subst U
  rw [Subobject.ofLE_refl]
  infer_instance

private theorem filtration_ext
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {T : B}
    (F G : PBCDecreasingFiltration T) (h : F.step = G.step) : F = G := by
  cases F
  cases G
  cases h
  rfl

private noncomputable def transportColimit
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℤ) (A : X.AlphaColimit n)
    {H : B} (e : A.obj ≅ H) : X.AlphaColimit n where
  obj := H
  ι p := A.ι p ≫ e.hom
  comm p := by rw [← Category.assoc, A.comm]
  isColimit T f hf := by
    obtain ⟨h, hh, huniq⟩ := A.isColimit T f hf
    refine ⟨e.inv ≫ h, ?_, ?_⟩
    · intro p
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hh p
    · intro h' hh'
      have he : e.hom ≫ h' = h := huniq _ (fun p ↦ by
        simpa only [Category.assoc] using hh' p)
      rw [← he, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def transportGradedIso
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (n : ℤ) (A : X.AlphaColimit n)
    {H : B} (e : A.obj ≅ H) (p : ℤ) :
    (X.imageFiltration n (transportColimit X n A e)).gradedPiece p ≅
      (X.imageFiltration n A).gradedPiece p := by
  let i := imageSubobjectCompIso (A.ι (p + 1)) e.hom
  let k := imageSubobjectCompIso (A.ι p) e.hom
  apply cokernel.mapIso _ _ i k
  dsimp [i, k, BigradedExactCouple.imageFiltration, transportColimit]
  apply (cancel_mono (imageSubobject (A.ι p)).arrow).1
  simp only [Category.assoc, imageSubobjectCompIso_hom_arrow,
    Subobject.ofLE_arrow_assoc]
  erw [Subobject.ofLE_arrow]
  exact (imageSubobjectCompIso_hom_arrow (A.ι (p + 1)) e.hom).symm

set_option backward.isDefEq.respectTransparency false in
private theorem transportGradedIso_comm
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (H : ℤ → B) (e : ∀ n : ℤ, (A n).obj ≅ H n) (p q : ℤ) :
    X.toGradedPiece (fun n ↦ transportColimit X n (A n) (e n)) p q ≫
        (transportGradedIso X (p + q) (A (p + q)) (e (p + q)) p).hom =
      X.toGradedPiece A p q := by
  dsimp [BigradedExactCouple.toGradedPiece, transportGradedIso]
  simp only [Category.assoc, cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
  apply congrArg (fun f ↦ eqToHom (by congr 1; omega) ≫ f)
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (imageSubobject ((A (p + q)).ι p)).arrow).1
  simp only [Category.assoc, imageSubobjectCompIso_hom_arrow,
    imageSubobject_arrow_comp]
  simp [transportColimit]


open BigradedExactCouple in
private theorem finite_inverse_limit
    {B : Type u₂} [Category.{v₂} B] [Abelian B] {T : B} (F : PBCDecreasingFiltration T)
    (m : ℤ) (hm : F.step m = ⊥) : IsInverseLimit F := by
  have hz (p : ℤ) (hp : m ≤ p) : F.step p = ⊥ :=
    le_antisymm (hm ▸ F.antitone_step hp) bot_le
  have hπ (p : ℤ) (hp : m ≤ p) : IsIso (cokernel.π (F.step p).arrow) := by
    apply CokernelCofork.IsColimit.isIso_π
      (CokernelCofork.ofπ _ (cokernel.condition _)) (cokernelIsCokernel _)
    apply Subobject.mk_eq_bot_iff_zero.mp
    simpa only [Subobject.mk_arrow] using hz p hp
  have hcomm (p : ℤ) :
      cokernel.π (F.step (p + 1)).arrow ≫ quotientTransition F p =
        cokernel.π (F.step p).arrow := by
    exact cokernel.π_desc _ _ _
  intro S f hf
  have := hπ m le_rfl
  let h : S ⟶ T := f m ≫ inv (cokernel.π (F.step m).arrow)
  have hbase : h ≫ cokernel.π (F.step m).arrow = f m := by simp [h]
  refine ⟨h, ?_, ?_⟩
  · intro p
    induction p using Int.inductionOn' with
    | b => exact m
    | zero => exact hbase
    | succ p hp ih =>
      have := hπ p hp
      have := hπ (p + 1) (by omega)
      have : IsIso (quotientTransition F p) := by
        have heq : quotientTransition F p =
            inv (cokernel.π (F.step (p + 1)).arrow) ≫ cokernel.π (F.step p).arrow := by
          apply (cancel_epi (cokernel.π (F.step (p + 1)).arrow)).1
          simp [hcomm]
        rw [heq]
        infer_instance
      apply (cancel_mono (quotientTransition F p)).1
      rw [Category.assoc, hcomm, hf, ih]
    | pred p hp ih =>
      have ih' : h ≫ cokernel.π (F.step (p - 1 + 1)).arrow = f (p - 1 + 1) := by
        exact Eq.mp (congrArg (fun j : ℤ ↦ h ≫ cokernel.π (F.step j).arrow = f j)
          (show p = p - 1 + 1 by omega)) ih
      calc
        h ≫ cokernel.π (F.step (p - 1)).arrow =
            h ≫ (cokernel.π (F.step (p - 1 + 1)).arrow ≫
              quotientTransition F (p - 1)) := by rw [hcomm]
        _ = f (p - 1 + 1) ≫ quotientTransition F (p - 1) := by
          rw [← Category.assoc, ih']
        _ = f (p - 1) := hf (p - 1)
  · intro h' hh'
    apply (cancel_mono (cokernel.π (F.step m).arrow)).1
    exact (hh' m).trans hbase.symm

/-- A normalized invertible diagonal cocone transports the finite image filtration
and its convergence to the prescribed abutment.
Source: Stacks Tags 011T, 012F and 012U (3), blueprint steps 5 and 7.
(blueprint: lem-sp-abutment-image-filtration)

Proof: Take the normalized diagonal colimits A supplied by negative-E vanishing.
Factor the prescribed cocone through A using its universal property. Its component
at zero and the normalization identify the factor with eqToHom(hA) followed by c,
so this factor is invertible. Transport A along this isomorphism to obtain AH,
and along eqToHom(hA) to obtain AA with object D(0,n). Define FA and FH to be
the image filtrations of AA and AH. The positive normalization gives the
incoming-alpha image formula for FA; image pushforward gives FH=FA.image(c).
The transported cocone gives the j-image formula. Negative-index cocone maps
are invertible, giving top for p<=0; when p>=n-a+1 the source D(p,n-p) is zero,
giving bottom. These bounds prove finiteness, exhaustiveness and separatedness.
Beyond the bottom bound the cokernel projections are invertible; factor a
compatible quotient cone through one such projection and use integer induction
to prove all its equations. Cancellation there proves uniqueness.
Construct the isomorphism between the transported and original graded pieces
by cokernel.mapIso on the two imageSubobjectCompIso maps. Cancellation of the
image arrows proves the square commutes and that the canonical graded maps
commute with this isomorphism. Half-plane weak convergence for A then gives
weak convergence for AH by invariance of kernels under postcomposition by an
isomorphism. Sharp bounds give regularity, and the preceding filtration and
inverse-limit properties complete convergence. For p<0 both adjacent steps
are top, making their inclusion invertible and its cokernel zero. The canonical
weak-convergence comparison transports this zero-object assertion to E_infinity. -/
theorem abutment_image_filtration
    {B : Type u₂} [Category.{v₂} B] [Abelian B]
    (X : BigradedExactCouple B 0) (a : ℤ)
    (hDzero : ∀ p q : ℤ, q < a → IsZero (X.D p q))
    (hEzero : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (X.E p q))
    (L : X.LimitSubobjects) (H : ℤ → B)
    (j : ∀ n q : ℤ, X.D (n - q) q ⟶ H n)
    (c : ∀ n : ℤ, X.D 0 n ⟶ H n)
    (hc : ∀ n : ℤ, c n = eqToHom (by congr 1; omega) ≫ j n n)
    (hiso : ∀ n : ℤ, IsIso (c n))
    (hcomm : ∀ n p : ℤ,
      X.alphaDiagonal n p ≫ eqToHom (by congr 1; omega) ≫ j n (n - p) =
        eqToHom (by congr 1; omega) ≫ j n (n - (p + 1)))
    (hnorm : ∀ (n p : ℤ) (hp : 0 ≤ p),
      eqToHom (by congr 1 <;> omega) ≫ j n (n - p) =
        X.incomingAlphaIter p.toNat 0 n ≫ c n) :
    ∃ (FA : ∀ n : ℤ, PBCDecreasingFiltration (X.D 0 n))
        (FH : ∀ n : ℤ, PBCDecreasingFiltration (H n)),
        (∀ n p : ℤ, 0 ≤ p → (FA n).step p =
          imageSubobject (X.incomingAlphaIter p.toNat 0 n)) ∧
        (∀ n p : ℤ, p ≤ 0 → (FA n).step p = ⊤) ∧
        (∀ n : ℤ, FH n = (FA n).image (c n)) ∧
        (∀ n p : ℤ, (FH n).step p = imageSubobject (j n (n - p))) ∧
        (∀ n p : ℤ, p ≤ 0 → (FH n).step p = ⊤) ∧
        (∀ n p : ℤ, n - a + 1 ≤ p → (FH n).step p = ⊥) ∧
        (∀ n : ℤ, (FH n).IsFinite ∧ (FH n).IsExhaustive ∧ (FH n).IsSeparated ∧
          BigradedExactCouple.IsInverseLimit (FH n)) ∧
        (∀ p q : ℤ, p < 0 → IsZero ((FH (p + q)).gradedPiece p) ∧
          IsZero (X.pageInfinity L p q)) ∧
        ∃ (AH : ∀ n : ℤ, X.AlphaColimit n) (hAH : ∀ n : ℤ, (AH n).obj = H n),
          (∀ n p : ℤ, (AH n).ι p ≫ eqToHom (hAH n) =
            eqToHom (by congr 1; omega) ≫ j n (n - p)) ∧
          X.ConvergesTo L AH := by
  classical
  let : ∀ n : ℤ, IsIso (c n) := hiso
  obtain ⟨A, hA, hι, hleft⟩ := X.halfPlane_diagonal_colimits
    (fun p q hp ↦ hEzero p q (Or.inl hp))
  let k (n p : ℤ) : X.D p (n - p) ⟶ H n :=
    eqToHom (by congr 1; omega) ≫ j n (n - p)
  have hk : ∀ n p : ℤ, X.alphaDiagonal n p ≫ k n p = k n (p + 1) := hcomm
  choose e he _ using fun n ↦ (A n).isColimit (H n) (k n) (hk n)
  have hec (n : ℤ) : e n = eqToHom (hA n) ≫ c n := by
    have := hleft n 0 le_rfl
    apply (cancel_epi ((A n).ι 0)).1
    rw [he n 0, ← Category.assoc, hι n, hc n]
    dsimp [k]
    simp only [eqToHom_trans_assoc]
    congr! 2 <;> omega
  have hei (n : ℤ) : IsIso (e n) := by rw [hec]; infer_instance
  let eH (n : ℤ) : (A n).obj ≅ H n := @asIso _ _ _ _ (e n) (hei n)
  let eA (n : ℤ) : (A n).obj ≅ X.D 0 n := eqToIso (hA n)
  let AH (n : ℤ) := transportColimit X n (A n) (eH n)
  let AA (n : ℤ) := transportColimit X n (A n) (eA n)
  let FA (n : ℤ) := X.imageFiltration n (AA n)
  let FH (n : ℤ) := X.imageFiltration n (AH n)
  have hAHι (n p : ℤ) : (AH n).ι p = k n p := he n p
  have hAAι (n p : ℤ) : (AA n).ι p ≫ c n = k n p := by
    dsimp [AA, transportColimit, eA]
    rw [Category.assoc, ← hec]
    exact he n p
  have hFA (n p : ℤ) (hp : 0 ≤ p) : (FA n).step p =
      imageSubobject (X.incomingAlphaIter p.toNat 0 n) := by
    lift p to ℕ using hp
    have hn := hnorm n (p : ℤ) (by omega)
    simp only [Int.toNat_natCast] at hn
    have hn' : (AA n).ι (p : ℤ) =
        eqToHom (by congr 1; omega) ≫ X.incomingAlphaIter p 0 n := by
      apply (cancel_mono (c n)).1
      rw [hAAι]
      have hh := congrArg
        (fun f : X.D (0 + (p : ℤ)) (n - p) ⟶ H n ↦
          eqToHom (by simp : X.D (p : ℤ) (n - p) = X.D (0 + (p : ℤ)) (n - p)) ≫ f) hn
      simpa only [k, eqToHom_trans_assoc, Category.assoc] using hh
    change imageSubobject ((AA n).ι (p : ℤ)) = _
    rw [hn', imageSubobject_iso_comp]
    simp only [Int.toNat_natCast]
  have hFAtop (n p : ℤ) (hp : p ≤ 0) : (FA n).step p = ⊤ := by
    have := hleft n p hp
    have : IsIso ((AA n).ι p) := by dsimp [AA, transportColimit]; infer_instance
    change imageSubobject ((AA n).ι p) = ⊤
    rw [imageSubobject_mono]
    exact Subobject.mk_eq_top_of_isIso _
  have hFH (n : ℤ) : FH n = (FA n).image (c n) := by
    apply filtration_ext
    funext p
    dsimp [FH, FA, PBCDecreasingFiltration.image, BigradedExactCouple.imageFiltration]
    rw [Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi (factorThruImageSubobject ((AA n).ι p))]
    simp only [imageSubobject_arrow_comp_assoc, hAAι, hAHι]
  have hFHj (n p : ℤ) : (FH n).step p = imageSubobject (j n (n - p)) := by
    change imageSubobject ((AH n).ι p) = _
    rw [hAHι]
    exact imageSubobject_iso_comp _ _
  have hFHtop (n p : ℤ) (hp : p ≤ 0) : (FH n).step p = ⊤ := by
    have := hleft n p hp
    have : IsIso ((AH n).ι p) := by dsimp [AH, transportColimit]; infer_instance
    change imageSubobject ((AH n).ι p) = ⊤
    rw [imageSubobject_mono]
    exact Subobject.mk_eq_top_of_isIso _
  have hFHbot (n p : ℤ) (hp : n - a + 1 ≤ p) : (FH n).step p = ⊥ := by
    change imageSubobject ((AH n).ι p) = ⊥
    rw [(hDzero p (n - p) (by omega)).eq_zero_of_src ((AH n).ι p),
      imageSubobject_zero]
  have hfinite (n : ℤ) : (FH n).IsFinite :=
    ⟨0, n - a + 1, hFHtop n 0 le_rfl, hFHbot n (n - a + 1) le_rfl⟩
  have hexhaustive (n : ℤ) : (FH n).IsExhaustive := by
    intro S hS
    exact top_unique (hFHtop n 0 le_rfl ▸ hS 0)
  have hseparated (n : ℤ) : (FH n).IsSeparated := by
    intro S hS
    exact bot_unique (hFHbot n (n - a + 1) le_rfl ▸ hS (n - a + 1))
  have hweakA := X.halfPlane_weak_convergence a hDzero hEzero L A hA hι
  have hweak : X.WeaklyConvergesTo L AH := by
    intro p q
    obtain ⟨hp, hg, hk⟩ := hweakA p q
    let gr := transportGradedIso X (p + q) (A (p + q)) (eH (p + q)) p
    have hgr : X.toGradedPiece AH p q ≫ gr.hom = X.toGradedPiece A p q :=
      transportGradedIso_comm X A H eH p q
    have : Epi (X.toGradedPiece A p q) := hg
    have : Epi (X.toGradedPiece AH p q) := by
      have hfac : X.toGradedPiece AH p q = X.toGradedPiece A p q ≫ gr.inv := by
        rw [← hgr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [hfac]
      infer_instance
    refine ⟨hp, inferInstance, ?_⟩
    exact hk.trans (by
      simpa only [hgr] using kernelSubobject_comp_mono (X.toGradedPiece AH p q) gr.hom)
  obtain ⟨_, _, _, _, _, hregular, _⟩ := halfPlane_sharp_bounds X a hDzero hEzero
  have hinverse (n : ℤ) : BigradedExactCouple.IsInverseLimit (FH n) := by
    exact finite_inverse_limit (FH n) (n - a + 1) (hFHbot n _ le_rfl)
  have hnegative (p q : ℤ) (hp : p < 0) :
      IsZero ((FH (p + q)).gradedPiece p) ∧ IsZero (X.pageInfinity L p q) := by
    have hinc : IsIso (Subobject.ofLE ((FH (p + q)).step (p + 1))
        ((FH (p + q)).step p) ((FH (p + q)).antitone_step (by omega))) := by
      have heq : (FH (p + q)).step (p + 1) = (FH (p + q)).step p := by
        rw [hFHtop _ _ (by omega), hFHtop _ _ (by omega)]
      exact ofLE_isIso_of_eq _ _ _ heq
    have hgraded : IsZero ((FH (p + q)).gradedPiece p) := by
      exact isZero_cokernel_of_epi _
    obtain ⟨gr, _⟩ := X.weakConvergence_comparison L AH hweak p q
    exact ⟨hgraded, hgraded.of_iso gr⟩
  refine ⟨FA, FH, hFA, hFAtop, hFH, hFHj, hFHtop, hFHbot,
    fun n ↦ ⟨hfinite n, hexhaustive n, hseparated n, hinverse n⟩,
    hnegative, AH, fun _ ↦ rfl, ?_, ?_⟩
  · intro n p
    simpa only [eqToHom_refl, Category.comp_id] using hAHι n p
  · exact ⟨hregular, ⟨hweak, fun n ↦ ⟨hseparated n, hexhaustive n⟩⟩, hinverse⟩

end CategoryTheory
