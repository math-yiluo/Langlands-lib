import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCup
import Langlands.AlgebraicGeometry.CechPrimitive
import Langlands.AbelianScheme.Basic

/-!
# Primitivity of actual `H¹(A, 𝒪_A)` and the coproduct of cup products

For an abelian scheme `A` over a field `K`, with `P = A ⨯ A`, projections `p₁`, `p₂` and
multiplication `m = p₁ * p₂`, this module proves, for the canonical structure-sheaf pullbacks of
`FieldH2ExteriorCoproductComparisonStatement`:

* `pullStructure_mul`: `m^* x = p₁^* x + p₂^* x` on `H¹(A, 𝒪_A)`;
* `pullStructure_cupA`: the pullbacks are compatible with the cup products `cupA` (on `A`) and
  `cupP` (on `P`) computed on chosen covers;
* `pullStructure_mul_cupA`: `m^*(x ∪ y) = p₁^*(x ∪ y) + p₁^* x ∪ p₂^* y - p₁^* y ∪ p₂^* x +
  p₂^*(x ∪ y)`.

It also records two general facts: `AllSeq.cochainSecEquiv`, the `R`-linear identification of
ordered Čech cochains of the structure sheaf with raw families of sections for the `secHom`
algebra structures, and `AllSeq.isAffineOpen_inf_preimage`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

open Langlands.Cohomology Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

section SecHom

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) {I : Type u} (U : I → X.Opens)
  [∀ W : X.Opens, Algebra R Γ(X, W)] (halg : ∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom π W).hom)

/-- Ordered Čech cochains of the structure sheaf as raw families of sections, `R`-linearly for
any algebra structures on sections given by `secHom`. -/
def cochainSecEquiv (p : ℕ) :
    cochain π U (unitModule X) p ≃ₗ[R] (∀ σ : Fin (p + 1) → I, Γ(X, inter U σ)) where
  toFun c := c
  invFun c := c
  map_add' _ _ := rfl
  map_smul' r c := by
    funext σ
    change (show Γ(X, inter U σ) from algC π (inter U σ) r *
      (show (Cech.ab X.presheaf).obj (op (inter U σ)) from c σ)) =
        r • (show Γ(X, inter U σ) from c σ)
    rw [Algebra.smul_def, halg]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

lemma cochainSecEquiv_dCochain (p : ℕ) (c : cochain π U (unitModule X) p) :
    (cochainSecEquiv π U halg (p + 1) (dCochain π U (unitModule X) p c) :
      Cech.C (Cech.ab X.presheaf) U (p + 1)) =
      Cech.d (Cech.ab X.presheaf) U p (cochainSecEquiv π U halg p c) :=
  dCochain_unit π U p c

end SecHom

section Affine

/-- Over a separated base `X ⟶ Spec R`, an affine open of `P` meets the preimage of an affine
open of `X` in an affine open. -/
lemma isAffineOpen_inf_preimage {R : CommRingCat.{u}} {P X : Scheme.{u}} (πX : X ⟶ Spec R)
    [IsSeparated πX] (m : P ⟶ X) {V : P.Opens} (hV : IsAffineOpen V) {W : X.Opens}
    (hW : IsAffineOpen W) : IsAffineOpen (V ⊓ m ⁻¹ᵁ W) := by
  have : IsAffine V := hV
  have : IsAffineHom ((V.ι ≫ m) ≫ πX) := inferInstance
  have : IsAffineHom (V.ι ≫ m) := IsAffineHom.of_comp (V.ι ≫ m) πX
  have h := (hW.preimage (V.ι ≫ m)).image_of_isOpenImmersion V.ι
  rwa [Scheme.Hom.comp_preimage, image_preimage_eq] at h

end Affine

end Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

namespace Langlands.AbelianScheme

open Langlands.Cohomology Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Modules.CechResolution
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open Langlands.AlgebraicGeometry.Picard

variable {K : Type u} [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))

/-- The canonical pullback of structure-sheaf cohomology along `f : Y ⟶ A.X`, followed by the
unit comparison `f^* 𝒪 ≅ 𝒪`, as in `FieldH2ExteriorCoproductComparisonStatement`. -/
abbrev pullStructure {Y : Over (Spec (CommRingCat.of K))} (f : Y ⟶ A.X) (n : ℕ) :
    (relativeCohomology A.X.hom n).obj (SheafOfModules.unit A.X.left.ringCatSheaf) →ₗ[K]
      (relativeCohomology Y.hom n).obj (SheafOfModules.unit Y.left.ringCatSheaf) :=
  (relativeCohomologyPullback f (SheafOfModules.unit A.X.left.ringCatSheaf) n ≫
    (relativeCohomology Y.hom n).map (Langlands.Scheme.Modules.pullbackUnitIso f.left).hom).hom

/-- **Primitivity of `H¹(A, 𝒪_A)`.** For an abelian scheme `A` over a field, with
`P = A ⨯ A`, projections `p₁`, `p₂` and multiplication `m = p₁ * p₂`, the canonical
structure-sheaf pullbacks satisfy `m^* x = p₁^* x + p₂^* x` on `H¹`. -/
theorem pullStructure_mul (x : (relativeCohomology A.X.hom 1).obj
      (SheafOfModules.unit A.X.left.ringCatSheaf)) :
    pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) 1 x =
      pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 x +
        pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 x := by
  classical
  let πX : A.X.left ⟶ Spec (CommRingCat.of K) := A.X.hom
  let P := A.X ⨯ A.X
  let p₁ : P ⟶ A.X := prod.fst
  let p₂ : P ⟶ A.X := prod.snd
  let m : P ⟶ A.X := p₁ * p₂
  have hP : IsPullback p₁.left p₂.left πX πX :=
    Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk _ _) (prodIsProd A.X A.X)
  -- The unit point and the two axes.
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have he : e ≫ πX = 𝟙 _ := Over.w η[A.X]
  let I₁ : A.X ⟶ P := prod.lift (𝟙 A.X) (toUnit A.X ≫ η[A.X])
  let I₂ : A.X ⟶ P := prod.lift (toUnit A.X ≫ η[A.X]) (𝟙 A.X)
  have h₁₁ : I₁.left ≫ p₁.left = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left (prod.lift_fst _ _))
  have h₁₂ : I₁.left ≫ p₂.left = πX ≫ e :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left (prod.lift_snd _ _))
  have h₂₁ : I₂.left ≫ p₁.left = πX ≫ e :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left (prod.lift_fst _ _))
  have h₂₂ : I₂.left ≫ p₂.left = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left (prod.lift_snd _ _))
  have hm₁ : I₁.left ≫ m.left = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left (show I₁ ≫ m = 𝟙 A.X by
      rw [MonObj.comp_mul, prod.lift_fst, prod.lift_snd, ← Hom.one_def, mul_one]))
  have hm₂ : I₂.left ≫ m.left = 𝟙 _ :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left (show I₂ ≫ m = 𝟙 A.X by
      rw [MonObj.comp_mul, prod.lift_fst, prod.lift_snd, ← Hom.one_def, one_mul]))
  -- A finite affine cover of `A`, and the cover of `P` adapted to `p₁`, `p₂` and `m`.
  obtain ⟨I, hI, U, hU, hUU, hcov⟩ := exists_affineCover πX
  have : Fintype I := Fintype.ofFinite I
  have hUtop : ⨆ i, U i = ⊤ := top_le_iff.mp hcov
  have : IsSeparated p₂.left := MorphismProperty.of_isPullback (P := @IsSeparated) hP
    (inferInstance : IsSeparated πX)
  have : IsSeparated P.hom := by
    rw [← Over.w p₂]
    infer_instance
  let W := Cech.primCover p₁.left p₂.left m.left U
  have hWa : ∀ j, IsAffineOpen (W j) := fun j =>
    AllSeq.isAffineOpen_inf_preimage πX m.left (isAffineOpen_prodOpen hP (hU _) (hU _)) (hU _)
  have hWtop : ⨆ j, W j = ⊤ := top_le_iff.mp (Cech.iSup_primCover hcov)
  have hβ₁ : ∀ j, W j ≤ p₁.left ⁻¹ᵁ U ((Prod.fst ∘ Prod.fst) j) :=
    fun _ => inf_le_left.trans inf_le_left
  have hβ₂ : ∀ j, W j ≤ p₂.left ⁻¹ᵁ U ((Prod.snd ∘ Prod.fst) j) :=
    fun _ => inf_le_left.trans inf_le_right
  have hβm : ∀ j, W j ≤ m.left ⁻¹ᵁ U (Prod.snd j) := fun _ => inf_le_right
  -- Write `x` as the class of a Čech cocycle.
  obtain ⟨z, rfl⟩ := AllSeq.canonicalClass_surjective πX U hUtop hU 0 x
  have hz : Cech.d (Cech.ab A.X.left.presheaf) U 1
      ((z : AllSeq.cochain πX U (AllSeq.unitModule A.X.left) 1) :
        Cech.C (Cech.ab A.X.left.presheaf) U 1) = 0 := by
    rw [← AllSeq.dCochain_unit]
    exact z.2
  -- Čech primitivity on `W`.
  obtain ⟨g, hg⟩ := Cech.exists_pull_sub_refine_eq_d (Field.toIsField K) hP
    (surjective_secHom_top πX) m.left e he I₁.left h₁₁ h₁₂ hm₁ I₂.left h₂₁ h₂₂ hm₂ U hU hUU hcov hz
  rw [map_add, Cech.refine_pull, Cech.refine_pull] at hg
  -- The three pullbacks of the class.
  have e₁ := AllSeq.pull_canonicalClass p₁ U W _ hβ₁ hUtop hWtop hU hWa 0 z
  have e₂ := AllSeq.pull_canonicalClass p₂ U W _ hβ₂ hUtop hWtop hU hWa 0 z
  have em := AllSeq.pull_canonicalClass m U W _ hβm hUtop hWtop hU hWa 0 z
  change (relativeCohomologyPullback m _ 1 ≫ _) _ = (relativeCohomologyPullback p₁ _ 1 ≫ _) _ +
    (relativeCohomologyPullback p₂ _ 1 ≫ _) _
  rw [e₁, e₂, em, ← sub_eq_zero, ← sub_sub, ← map_sub, ← map_sub,
    AllSeq.canonicalClass_eq_zero_iff]
  refine ⟨g, ?_⟩
  have h_m := AllSeq.unitCochainMap_eq_pull m U W Prod.snd hβm 1 z
  have h_1 := AllSeq.unitCochainMap_eq_pull p₁ U W _ hβ₁ 1 z
  have h_2 := AllSeq.unitCochainMap_eq_pull p₂ U W _ hβ₂ 1 z
  refine (AllSeq.dCochain_unit P.hom W 0 g).trans (hg.symm.trans ?_)
  rw [sub_add_eq_sub_sub, ← h_m, ← h_1, ← h_2]
  rfl

section Chosen

/-- The index type of a chosen finite affine cover of `A`. -/
def coverIdx : Type u := Classical.choose (exists_affineCover A.X.hom)

instance : Finite (coverIdx A) := (Classical.choose_spec (exists_affineCover A.X.hom)).choose

noncomputable instance : Fintype (coverIdx A) := Fintype.ofFinite _

/-- A chosen finite cover of `A` by affine opens. -/
def cover : coverIdx A → A.X.left.Opens :=
  (Classical.choose_spec (exists_affineCover A.X.hom)).choose_spec.choose

lemma cover_spec : (∀ i, IsAffineOpen (cover A i)) ∧
    (∀ i k, IsAffineOpen (cover A i ⊓ cover A k)) ∧ ⊤ ≤ iSup (cover A) :=
  (Classical.choose_spec (exists_affineCover A.X.hom)).choose_spec.choose_spec

lemma cover_affine (i : coverIdx A) : IsAffineOpen (cover A i) := (cover_spec A).1 i

lemma cover_top : ⨆ i, cover A i = ⊤ := top_le_iff.mp (cover_spec A).2.2

lemma isPullback_prod :
    IsPullback (prod.fst : A.X ⨯ A.X ⟶ A.X).left (prod.snd : A.X ⨯ A.X ⟶ A.X).left
      A.X.hom A.X.hom :=
  Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk _ _) (prodIsProd A.X A.X)

instance isSeparated_prod_hom : IsSeparated (A.X ⨯ A.X).hom := by
  have : IsSeparated (prod.snd : A.X ⨯ A.X ⟶ A.X).left :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_prod A)
      (inferInstance : IsSeparated A.X.hom)
  rw [← Over.w (prod.snd : A.X ⨯ A.X ⟶ A.X)]
  infer_instance

/-- The cover `p₁⁻¹ U a ⊓ p₂⁻¹ U b ⊓ m⁻¹ U c` of `A ⨯ A`, adapted to the two projections and the
multiplication. -/
def productCover : (coverIdx A × coverIdx A) × coverIdx A → (A.X ⨯ A.X).left.Opens :=
  Cech.primCover (prod.fst : A.X ⨯ A.X ⟶ A.X).left (prod.snd : A.X ⨯ A.X ⟶ A.X).left
    ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd).left (cover A)

lemma productCover_affine (j : (coverIdx A × coverIdx A) × coverIdx A) :
    IsAffineOpen (productCover A j) :=
  AllSeq.isAffineOpen_inf_preimage A.X.hom _
    (isAffineOpen_prodOpen (isPullback_prod A) (cover_affine A _) (cover_affine A _))
    (cover_affine A _)

lemma productCover_top : ⨆ j, productCover A j = ⊤ :=
  top_le_iff.mp (Cech.iSup_primCover (cover_spec A).2.2)

lemma productCover_le_fst (j : (coverIdx A × coverIdx A) × coverIdx A) :
    productCover A j ≤ (prod.fst : A.X ⨯ A.X ⟶ A.X).left ⁻¹ᵁ cover A ((Prod.fst ∘ Prod.fst) j) :=
  inf_le_left.trans inf_le_left

lemma productCover_le_snd (j : (coverIdx A × coverIdx A) × coverIdx A) :
    productCover A j ≤ (prod.snd : A.X ⨯ A.X ⟶ A.X).left ⁻¹ᵁ cover A ((Prod.snd ∘ Prod.fst) j) :=
  inf_le_left.trans inf_le_right

lemma productCover_le_mul (j : (coverIdx A × coverIdx A) × coverIdx A) :
    productCover A j ≤
      ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd).left ⁻¹ᵁ cover A (Prod.snd j) :=
  inf_le_right

/-- The cup product `H¹(A, 𝒪_A) × H¹(A, 𝒪_A) ⟶ H²(A, 𝒪_A)`, computed on the chosen cover. -/
def cupA :
    (relativeCohomology A.X.hom 1).obj (SheafOfModules.unit A.X.left.ringCatSheaf) →ₗ[K]
      (relativeCohomology A.X.hom 1).obj (SheafOfModules.unit A.X.left.ringCatSheaf) →ₗ[K]
        (relativeCohomology A.X.hom 2).obj (SheafOfModules.unit A.X.left.ringCatSheaf) :=
  AllSeq.cupCanonical A.X.hom (cover A) (cover_top A) (cover_affine A)

/-- The cup product on `H¹(A ⨯ A, 𝒪)`, computed on the cover `productCover A`. -/
def cupP :
    (relativeCohomology (A.X ⨯ A.X).hom 1).obj
        (SheafOfModules.unit (A.X ⨯ A.X).left.ringCatSheaf) →ₗ[K]
      (relativeCohomology (A.X ⨯ A.X).hom 1).obj
          (SheafOfModules.unit (A.X ⨯ A.X).left.ringCatSheaf) →ₗ[K]
        (relativeCohomology (A.X ⨯ A.X).hom 2).obj
          (SheafOfModules.unit (A.X ⨯ A.X).left.ringCatSheaf) :=
  AllSeq.cupCanonical (A.X ⨯ A.X).hom (productCover A) (productCover_top A)
    (productCover_affine A)

lemma cupA_swap (x y) : cupA A x y = -cupA A y x :=
  AllSeq.cupCanonical_swap _ _ _ _ x y

lemma cupP_swap (x y) : cupP A x y = -cupP A y x :=
  AllSeq.cupCanonical_swap _ _ _ _ x y

/-- Pullback along a map `f : A ⨯ A ⟶ A` adapted to the chosen covers is a ring map in degrees
`1, 1 → 2`. -/
lemma pullStructure_cupA (f : A.X ⨯ A.X ⟶ A.X)
    (β : (coverIdx A × coverIdx A) × coverIdx A → coverIdx A)
    (hβ : ∀ j, productCover A j ≤ f.left ⁻¹ᵁ cover A (β j)) (x y) :
    pullStructure A f 2 (cupA A x y) =
      cupP A (pullStructure A f 1 x) (pullStructure A f 1 y) :=
  AllSeq.pull_cupCanonical f (cover A) (productCover A) β hβ (cover_top A) (productCover_top A)
    (cover_affine A) (productCover_affine A) x y

/-- **The multiplication pullback on a cup of degree-one classes.** With `p₁`, `p₂`, `m` as in
`FieldH2ExteriorCoproductComparisonStatement`,
`m^*(x ∪ y) = p₁^*(x ∪ y) + p₁^* x ∪ p₂^* y - p₁^* y ∪ p₂^* x + p₂^*(x ∪ y)`. -/
theorem pullStructure_mul_cupA (x y) :
    pullStructure A ((prod.fst : A.X ⨯ A.X ⟶ A.X) * prod.snd) 2 (cupA A x y) =
      pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 2 (cupA A x y) +
        cupP A (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 x)
          (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 y) -
        cupP A (pullStructure A (prod.fst : A.X ⨯ A.X ⟶ A.X) 1 y)
          (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 x) +
      pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 2 (cupA A x y) := by
  rw [pullStructure_cupA A _ _ (productCover_le_mul A), pullStructure_mul A x,
    pullStructure_mul A y, pullStructure_cupA A _ _ (productCover_le_fst A),
    pullStructure_cupA A _ _ (productCover_le_snd A)]
  simp only [map_add, LinearMap.add_apply]
  rw [cupP_swap A (pullStructure A (prod.snd : A.X ⨯ A.X ⟶ A.X) 1 x)]
  abel

end Chosen

end Langlands.AbelianScheme
