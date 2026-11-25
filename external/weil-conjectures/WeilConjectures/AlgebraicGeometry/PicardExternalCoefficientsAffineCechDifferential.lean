/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardExternalCoefficientsAffineCechTerms

/-! # Differential compatibility of normalized external Cech term maps

Source: Stacks Project, Tag 0BED, lemma-kunneth, affine-open paragraph.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-differential).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private lemma sectionUnit_restrict {S T : Scheme.{w}} (p : T ⟶ S)
    (M : T.Modules) (F : S.Modules) (η : F ⟶ (pushforward p).obj M)
    {A A' : S.Opens} {K K' : T.Opens} (hA : A' ≤ A) (hK : K' ≤ K)
    (ha : K ≤ p ⁻¹ᵁ A) (ha' : K' ≤ p ⁻¹ᵁ A') (s : Γ(F, A)) :
    M.presheaf.map (homOfLE ha').op
        (η.val.app (Opposite.op A') (F.presheaf.map (homOfLE hA).op s)) =
      M.presheaf.map (homOfLE hK).op
        (M.presheaf.map (homOfLE ha).op (η.val.app (Opposite.op A) s)) := by
  have hn := Hom.app_presheaf_map η (homOfLE hA) s
  change η.val.app (Opposite.op A') (F.presheaf.map (homOfLE hA).op s) =
    ((pushforward p).obj M).presheaf.map (homOfLE hA).op
      (η.val.app (Opposite.op A) s) at hn
  rw [hn]
  change M.presheaf.map _ (M.presheaf.map _ _) = M.presheaf.map _ (M.presheaf.map _ _)
  simp only [← Functor.map_comp_apply]
  congr 2

private lemma tmulSection_sum_zsmul {S : Scheme.{w}} {M N : S.Modules}
    {A : S.Opens} {α : Type*} (s : Finset α) (c : α → ℤ)
    (a : α → Γ(M, A)) (t : Γ(N, A)) :
    tmulSection (∑ i ∈ s, c i • a i) t = ∑ i ∈ s, c i • tmulSection (a i) t := by
  let h : Γ(M, A) →+ Γ(M ⊗ N, A) :=
    { toFun := fun x ↦ tmulSection x t
      map_zero' := zero_tmulSection t
      map_add' := fun x y ↦ add_tmulSection x y t }
  exact (map_sum h _ s).trans (Finset.sum_congr rfl fun i _ ↦ h.map_zsmul _ _)

private lemma coordinate_d {S : TopCat.{w}} {ι : Type w} {R : Type w} [Ring R]
    (U : ι → TopologicalSpace.Opens S)
    (P : (TopologicalSpace.Opens S)ᵒᵖ ⥤ ModuleCat.{w} R)
    (n : ℕ) (x : ((cechComplexFunctor U).obj P).X n) (y : Fin (n + 2) → ι) :
    TopCat.Presheaf.cechComplexFunctorXAddEquiv U P (n + 1)
        (((cechComplexFunctor U).obj P).d n (n + 1) x) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        P.map (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove)).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U P n x (y ∘ i.succAbove)) := by
  have hh := congrArg (fun a ↦ a x)
    ((TopCat.Presheaf.cechComplexFunctorIso U P).hom.comm n (n + 1))
  exact (congrFun hh.symm y).trans (TopCat.Presheaf.cechComplex_d_apply U _ n _ y)

-- The section identity carries several scalar-restriction instances.
/-- Any degreewise maps with the external pure-tensor section normalization commute
with the Cech differentials. This uses no affine or quasi-coherent hypotheses and
asserts no existence or invertibility of a degreewise comparison.
Source: Stacks Project, Tag 0BED, lemma-kunneth, affine-open Cech calculation;
Tag 01CD, lemma-tensor-product-pullback, and pullback-unit naturality.
(blueprint: lem-sc-picard-external-coefficients-affine-cech-differential).

Proof: Project the proposed differential square to a tuple of length n+2.
The native Cech differential is the finite alternating sum of face restrictions.
On an input a tensor t, normalization expresses each coordinate of the comparison
as the tensor section of the pullback unit applied to a's coordinate and the unit
applied to t. Restriction of tmulSection is tmulSection of the two restrictions.
Naturality of each pullback unit moves the face restriction through that unit.
For the first factor this is the corresponding face restriction of a; for the
second it is the restriction of the same section t on V in either order. Thus
all individual face squares commute, including faces with repeated indices.
Additivity and integer linearity of tensor and section maps identify the finite
alternating sums. Tensor induction extends the identity from a tensor t to every
element of the degree term. Coordinate extensionality gives the square itself.
For a non-adjacent pair both differentials are zero by the complex shape.
The empty index type has zero cochain terms, and all identities hold there too.
No affine hypothesis, finite index hypothesis, or covering condition is used:
the face set is finite independently of the index set. -/
theorem picardAffineCech_normalized_differential
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) {ι : Type w} (U : ι → X.Opens) (V : Y.Opens)
    (e : ∀ n, (picardAffineCechRight f g F G U V).X n ≅
      (picardAffineCechLeft f g F G U V).X n)
    (he : PicardAffineCechNormalized f g F G U V e) :
    ∀ n m, (ComplexShape.up ℕ).Rel n m →
      (e n).hom ≫ (picardAffineCechLeft f g F G U V).d n m =
        (picardAffineCechRight f g F G U V).d n m ≫ (e m).hom := by
  rintro n _ rfl
  apply AddCommGrpCat.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul a t =>
    simp only [AddCommGrpCat.comp_apply]
    have hr : (picardAffineCechRight f g F G U V).d n (n + 1) (a ⊗ₜ[k] t) =
        ((picardAffineCechBase f F U).d n (n + 1) a) ⊗ₜ[k] t := by
      exact ModuleCat.MonoidalCategory.tensorHom_tmul _ _ a t
    rw [hr]
    let W := (pullback.snd f g) ⁻¹ᵁ V
    let E := (externalCupCoefficients f g F G).restrict W.ι
    let U' : ι → W.toScheme.Opens := fun i ↦ W.ι ⁻¹ᵁ ((pullback.fst f g) ⁻¹ᵁ U i)
    apply (TopCat.Presheaf.cechComplexFunctorXAddEquiv U' E.presheafModuleCat (n + 1)).injective
    funext y
    change TopCat.Presheaf.cechComplexFunctorXAddEquiv U' E.presheafModuleCat (n + 1)
      (((cechComplexFunctor U').obj E.presheafModuleCat).d n (n + 1)
        ((e n).hom (a ⊗ₜ[k] t))) y = _
    rw [coordinate_d]
    dsimp only [PicardAffineCechNormalized] at he
    rw [he]
    have hface (i : Fin (n + 2)) :
        TopCat.Presheaf.cechComplexFunctorXAddEquiv U' E.presheafModuleCat n
          ((e n).hom (a ⊗ₜ[k] t)) (y ∘ i.succAbove) =
          picardAffineCechPureSection f g F G U V n (y ∘ i.succAbove) a t :=
      he n a t _
    simp_rw [hface]
    dsimp only [picardAffineCechPureSection]
    have hd := coordinate_d U F.presheafModuleCat n
      (show ((cechComplexFunctor U).obj F.presheafModuleCat).X n from a) y
    change TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat (n + 1)
      ((picardAffineCechBase f F U).d n (n + 1) a) y = _ at hd
    rw [hd]
    simp only [map_sum, map_zsmul]
    let P := (tensorPullback (pullback.fst f g)).obj F
    let Q := (tensorPullback (pullback.snd f g)).obj G
    let J : W.toScheme.Opens := ⨅ l, U' (y l)
    let K : (Limits.pullback f g).Opens := W.ι ''ᵁ J
    let A : X.Opens := ⨅ l, U (y l)
    let η := (Classical.choose (exists_tensorPullbackAdjunction (pullback.fst f g))).unit.app F
    let ηG := (Classical.choose (exists_tensorPullbackAdjunction (pullback.snd f g))).unit.app G
    let tt : Γ(Q, K) := Q.presheaf.map
      (homOfLE ((W.ι.image_mono le_top).trans_eq W.ι_image_top)).op
      (ηG.val.app (Opposite.op V)
        (G.presheaf.map (eqToHom V.ι_image_top.symm).op ((G.restrictAppIso V.ι ⊤).hom t)))
    let hK : K ≤ (pullback.fst f g) ⁻¹ᵁ A := by
      apply (W.ι.image_mono ?_).trans (W.ι.image_preimage_le _)
      apply le_of_eq
      dsimp only [J, U', A]
      apply TopologicalSpace.Opens.ext
      simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage,
        Set.preimage_iInter]
    let ss (i : Fin (n + 2)) : Γ(P, K) := P.presheaf.map (homOfLE hK).op
      (η.val.app (Opposite.op A)
        (F.presheafModuleCat.map
          (homOfLE (TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove)).op
          (TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
            (y ∘ i.succAbove))))
    have hs := tmulSection_sum_zsmul (M := P) (N := Q) (A := K)
      Finset.univ (fun i : Fin (n + 2) ↦ (-1 : ℤ) ^ (i : ℕ)) ss tt
    change _ = ((externalCupCoefficients f g F G).restrictAppIso W.ι J).inv
      (tmulSection (M := P) (N := Q) (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ss i) tt)
    rw [hs]
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    let J' : W.toScheme.Opens := ⨅ l, U' ((y ∘ i.succAbove) l)
    let K' : (Limits.pullback f g).Opens := W.ι ''ᵁ J'
    let A' : X.Opens := ⨅ l, U ((y ∘ i.succAbove) l)
    have hJ : J ≤ J' := TopCat.Presheaf.iInf_le_iInf_comp U' y i.succAbove
    have hKK : K ≤ K' := W.ι.image_mono hJ
    have hAA : A ≤ A' := TopCat.Presheaf.iInf_le_iInf_comp U y i.succAbove
    have hK' : K' ≤ (pullback.fst f g) ⁻¹ᵁ A' := by
      apply (W.ι.image_mono ?_).trans (W.ι.image_preimage_le _)
      apply le_of_eq
      dsimp only [J', U', A']
      apply TopologicalSpace.Opens.ext
      simp only [TopologicalSpace.Opens.coe_iInf, Scheme.Hom.coe_preimage,
        Set.preimage_iInter]
    have hKV' : K' ≤ (pullback.snd f g) ⁻¹ᵁ V :=
      (W.ι.image_mono le_top).trans_eq W.ι_image_top
    let sa := TopCat.Presheaf.cechComplexFunctorXAddEquiv U F.presheafModuleCat n a
      (y ∘ i.succAbove)
    let ta := G.presheaf.map (eqToHom V.ι_image_top.symm).op
      ((G.restrictAppIso V.ι ⊤).hom t)
    change E.presheaf.map (homOfLE hJ).op
      (((externalCupCoefficients f g F G).restrictAppIso W.ι J').inv
        (tmulSection (M := P) (N := Q)
          (P.presheaf.map (homOfLE hK').op (η.val.app (Opposite.op A') sa))
          (Q.presheaf.map (homOfLE hKV').op (ηG.val.app (Opposite.op V) ta)))) =
      ((externalCupCoefficients f g F G).restrictAppIso W.ι J).inv (tmulSection (ss i) tt)
    rw [restrictAppIso_inv_map_apply, tmulSection_map]
    congr 2
    · exact (sectionUnit_restrict (pullback.fst f g) P F η hAA hKK hK' hK sa).symm
    · change Q.presheaf.map _ (Q.presheaf.map _ _) = Q.presheaf.map _ _
      simp only [← Functor.map_comp_apply]
      congr 2


end AlgebraicGeometry.Scheme.Modules
