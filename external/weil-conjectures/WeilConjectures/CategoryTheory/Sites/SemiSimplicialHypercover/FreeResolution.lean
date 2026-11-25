/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Sites.LocallyExact
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Cone

/-!
# The free resolution attached to a hypercover

Let `U` be a semi-simplicial hypercover of a site `(C, J)` and `R` a ring. Write `R[V]` for the
sheafification of the free presheaf of `R`-modules `W ↦ R^{(Hom(W, V))}` on the presheaf
represented by `V`. The alternating sums of the face maps make
`⋯ ⟶ R[U₂] ⟶ R[U₁] ⟶ R[U₀]` a chain complex (`CategoryTheory.SemiSimplicialObject.freeComplex`),
augmented to the constant sheaf `R` (`CategoryTheory.SemiSimplicialObject.freeAugmentation`). The
main result is that this augmented complex is exact: a cycle is locally a boundary, as one sees by
choosing locally a vertex and coning off, inductively over the dimension, the finitely many
simplices involved, using the local lifting property of the hypercover.

Since `Hom(R[V], I) = I(V)`, applying `Hom(-, I)` for an injective sheaf `I` shows that the
cochain complex `C^•(U, I)` of sections of `I` is exact in positive degrees and that its degree
zero cocycles are the global sections of `I`.

## Main statements

- `CategoryTheory.SemiSimplicialObject.IsHypercover.exactAt_freeComplex`: the free complex is
  exact in positive degrees.
- `CategoryTheory.SemiSimplicialObject.IsHypercover.exact_freeAugmentation`,
  `CategoryTheory.SemiSimplicialObject.IsHypercover.epi_freeAugmentation`: it is a resolution of
  the constant sheaf `R`.
- `CategoryTheory.SemiSimplicialObject.IsHypercover.exactAt_cochainComplex_of_injective`: the
  cochain complex of an injective sheaf is exact in positive degrees.
- `CategoryTheory.SemiSimplicialObject.IsHypercover.exact_cochainComplex_zero_of_injective`:
  its degree zero cocycles are the global sections.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [Ring R] [HasSheafify J (ModuleCat.{max u v} R)]

/-- The constant sheaf of `R`-modules with value `R`. -/
noncomputable abbrev constSheaf : Sheaf J (ModuleCat.{max u v} R) :=
  (constantSheaf J (ModuleCat.{max u v} R)).obj (ModuleCat.of R R)

/-- The free presheaf of `R`-modules `W ↦ R^{(Hom(W, V))}` on the presheaf represented by `V`. -/
noncomputable abbrev freeYoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat.{max u v} R :=
  uliftYoneda.{u} ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)

/-- The free sheaf of `R`-modules `R[V]`, the sheafification of `W ↦ R^{(Hom(W, V))}`. -/
noncomputable abbrev freeSheaf : C ⥤ Sheaf J (ModuleCat.{max u v} R) :=
  freeYoneda R ⋙ presheafToSheaf J _

/-- Morphisms `R[V] ⟶ F` from a free sheaf are sections of `F` over `V` (Yoneda, the free module
adjunction and the sheafification adjunction). -/
noncomputable def freeSheafHomEquiv (V : C) (F : Sheaf J (ModuleCat.{max u v} R)) :
    ((freeSheaf J R).obj V ⟶ F) ≃ F.obj.obj (op V) :=
  ((sheafificationAdjunction J _).homEquiv _ _).trans <|
    (((ModuleCat.adj R).whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv

/-- `freeSheafHomEquiv` is natural in the sheaf: postcomposition with `ψ` corresponds to applying
`ψ` to sections. -/
lemma freeSheafHomEquiv_comp (V : C) {F G : Sheaf J (ModuleCat.{max u v} R)}
    (φ : (freeSheaf J R).obj V ⟶ F) (ψ : F ⟶ G) :
    freeSheafHomEquiv J R V G (φ ≫ ψ) = (ψ.hom.app (op V)).hom (freeSheafHomEquiv J R V F φ) := by
  simp only [freeSheafHomEquiv, Equiv.trans_apply]
  rfl

/-- `freeSheafHomEquiv` is natural in the object: precomposition with `R[f]` corresponds to
restriction of sections along `f`. -/
lemma freeSheafHomEquiv_map_comp {V W : C} (f : V ⟶ W) (F : Sheaf J (ModuleCat.{max u v} R))
    (φ : (freeSheaf J R).obj W ⟶ F) :
    freeSheafHomEquiv J R V F ((freeSheaf J R).map f ≫ φ) =
      (F.obj.map f.op).hom (freeSheafHomEquiv J R W F φ) := by
  simp only [freeSheafHomEquiv, Equiv.trans_apply]
  rw [Functor.comp_map]
  erw [(sheafificationAdjunction J _).homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ f.op).symm

/-- The free complex `⋯ ⟶ R[U₂] ⟶ R[U₁] ⟶ R[U₀]` of a semi-simplicial object, with the
alternating sums of the face maps as differentials. -/
noncomputable def freeComplex (U : SemiSimplicialObject C) :
    ChainComplex (Sheaf J (ModuleCat.{max u v} R)) ℕ :=
  ChainComplex.of (fun n ↦ (freeSheaf J R).obj (U.obj n))
    (fun n ↦ ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • (freeSheaf J R).map (U.δ n i))
    (fun n ↦ U.sum_map_δ_comp_sum_map_δ (freeSheaf J R) n)

@[simp]
lemma freeComplex_X (U : SemiSimplicialObject C) (n : ℕ) :
    (U.freeComplex J R).X n = (freeSheaf J R).obj (U.obj n) := rfl

variable {J R} in
/-- The differential of the free complex is the alternating sum of the face maps. -/
lemma freeComplex_d (U : SemiSimplicialObject C) (n : ℕ) :
    (U.freeComplex J R).d (n + 1) n =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • (freeSheaf J R).map (U.δ n i) := by
  simp [freeComplex]

/-- `freeSheafHomEquiv` is additive. -/
lemma freeSheafHomEquiv_add (V : C) (F : Sheaf J (ModuleCat.{max u v} R))
    (φ ψ : (freeSheaf J R).obj V ⟶ F) :
    freeSheafHomEquiv J R V F (φ + ψ) =
      freeSheafHomEquiv J R V F φ + freeSheafHomEquiv J R V F ψ := by
  have h : φ + ψ = biprod.lift φ ψ ≫ (biprod.fst + biprod.snd) := by simp
  rw [h, freeSheafHomEquiv_comp, Sheaf.Hom.add_app, ModuleCat.hom_add, LinearMap.add_apply,
    ← freeSheafHomEquiv_comp, ← freeSheafHomEquiv_comp, biprod.lift_fst, biprod.lift_snd]

/-- `freeSheafHomEquiv` as an additive equivalence. -/
noncomputable def freeSheafHomAddEquiv (V : C) (F : Sheaf J (ModuleCat.{max u v} R)) :
    ((freeSheaf J R).obj V ⟶ F) ≃+ F.obj.obj (op V) where
  __ := freeSheafHomEquiv J R V F
  map_add' := freeSheafHomEquiv_add J R V F

@[simp]
lemma freeSheafHomAddEquiv_apply (V : C) (F : Sheaf J (ModuleCat.{max u v} R))
    (φ : (freeSheaf J R).obj V ⟶ F) :
    freeSheafHomAddEquiv J R V F φ = freeSheafHomEquiv J R V F φ :=
  rfl

lemma freeSheafHomEquiv_zero (V : C) (F : Sheaf J (ModuleCat.{max u v} R)) :
    freeSheafHomEquiv J R V F 0 = 0 :=
  map_zero (freeSheafHomAddEquiv J R V F)

/-- Under `freeSheafHomEquiv`, precomposition with the differential of the free complex
corresponds to the differential of the cochain complex. -/
lemma freeSheafHomEquiv_d_comp (U : SemiSimplicialObject C) (F : Sheaf J (ModuleCat.{max u v} R))
    (q : ℕ) (φ : (U.freeComplex J R).X q ⟶ F) :
    freeSheafHomEquiv J R (U.obj (q + 1)) F ((U.freeComplex J R).d (q + 1) q ≫ φ) =
      (U.cochainDifferential F.obj q).hom (freeSheafHomEquiv J R (U.obj q) F φ) := by
  rw [freeComplex_d, Preadditive.sum_comp, ← freeSheafHomAddEquiv_apply, map_sum,
    cochainDifferential, ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, map_zsmul, freeSheafHomAddEquiv_apply, freeSheafHomEquiv_map_comp,
    ModuleCat.hom_zsmul, LinearMap.smul_apply]

/-- The map of presheaves `R^{(Hom(W, V))} ⟶ R` summing the coefficients. -/
noncomputable def freeYonedaToConst (V : C) :
    (freeYoneda R).obj V ⟶ (Functor.const Cᵒᵖ).obj (ModuleCat.of R R) where
  app _ := ModuleCat.ofHom (Finsupp.linearCombination R (fun _ ↦ (1 : R)))
  naturality _ _ _ := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro a r
    simp [ModuleCat.free]

variable {R} in
/-- The augmentations to the constant presheaf are compatible with the maps of free presheaves. -/
@[reassoc]
lemma freeYoneda_map_comp_freeYonedaToConst {X Y : C} (g : X ⟶ Y) :
    (freeYoneda R).map g ≫ freeYonedaToConst R Y = freeYonedaToConst R X := by
  ext W : 2
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro a r
  simp [freeYonedaToConst, ModuleCat.free]

/-- The augmentation `R[U₀] ⟶ R` to the constant sheaf, induced by the maps of presheaves
`R^{(Hom(W, U₀))} ⟶ R` summing the coefficients. -/
noncomputable def freeAugmentation (U : SemiSimplicialObject C) :
    (U.freeComplex J R).X 0 ⟶ constSheaf J R :=
  (presheafToSheaf J _).map (freeYonedaToConst R (U.obj 0))

lemma freeComplex_d_freeAugmentation (U : SemiSimplicialObject C) :
    (U.freeComplex J R).d 1 0 ≫ U.freeAugmentation J R = 0 := by
  have h (i : Fin 2) : (freeSheaf J R).map (U.δ 0 i) ≫
      (presheafToSheaf J _).map (freeYonedaToConst R (U.obj 0)) =
      (presheafToSheaf J _).map (freeYonedaToConst R (U.obj (0 + 1))) := by
    have := congrArg (presheafToSheaf J _).map
      (freeYoneda_map_comp_freeYonedaToConst (R := R) (U.δ 0 i))
    rw [Functor.map_comp] at this
    exact this
  have h' : (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • (freeSheaf J R).map (U.δ 0 i)) ≫
      (presheafToSheaf J _).map (freeYonedaToConst R (U.obj 0)) = 0 := by
    rw [Preadditive.sum_comp, Fin.sum_univ_two, Preadditive.zsmul_comp,
      Preadditive.zsmul_comp, h, h]
    simp
  rw [freeComplex_d]
  exact h'


section Chains

/-! ### Local exactness of the free complex on sections

The sections over `W` of the free presheaf `R^{(Hom(-, V))}` are the finitely supported
functions `ULift (W ⟶ V) →₀ R`. On chains supported on simplices with a cone
(`CategoryTheory.SemiSimplicialObject.IsCone`), the cone is a contracting homotopy. -/

variable {J}

omit [HasSheafify J (ModuleCat.{max u v} R)]

lemma _root_.Finsupp.linearMap_apply_eq_of_forall_mem_support {S α M : Type*} [Semiring S]
    [AddCommMonoid M] [Module S M] (f g : (α →₀ S) →ₗ[S] M) (c : α →₀ S)
    (h : ∀ a ∈ c.support, f (Finsupp.single a 1) = g (Finsupp.single a 1)) : f c = g c := by
  rw [← Finsupp.sum_single c]
  simp only [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [← mul_one (c a), ← smul_eq_mul, ← Finsupp.smul_single, map_smul, map_smul, h a ha]

variable (U : SemiSimplicialObject C)

/-- The differential of the free complex on sections over `W`. -/
noncomputable def chainD (W : C) (n : ℕ) :
    (ULift.{u} (W ⟶ U.obj (n + 1)) →₀ R) →ₗ[R] (ULift.{u} (W ⟶ U.obj n) →₀ R) :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
    Finsupp.lmapDomain R R (fun σ ↦ ULift.up (σ.down ≫ U.δ n i))

lemma chainD_single (W : C) (n : ℕ) (σ : W ⟶ U.obj (n + 1)) :
    U.chainD R W n (Finsupp.single (ULift.up σ) 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (ULift.up (σ ≫ U.δ n i)) 1 := by
  simp [chainD]

/-- The presheaf version of the differential of the free complex. -/
noncomputable def freeYonedaD (n : ℕ) :
    (freeYoneda R).obj (U.obj (n + 1)) ⟶ (freeYoneda R).obj (U.obj n) :=
  ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • (freeYoneda R).map (U.δ n i)

lemma freeYonedaD_app (n : ℕ) (W : C) :
    ((U.freeYonedaD R n).app (op W)).hom = U.chainD R W n := by
  ext σ
  simp only [freeYonedaD, chainD, NatTrans.app_sum, NatTrans.app_zsmul, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul]
  rfl

lemma freeYonedaD_app_apply (n : ℕ) (W : C) (c : ULift.{u} (W ⟶ U.obj (n + 1)) →₀ R) :
    ((U.freeYonedaD R n).app (op W)).hom c = U.chainD R W n c :=
  LinearMap.congr_fun (U.freeYonedaD_app R n W) c


variable {U} in
/-- The linear extension of a partial map `h` on simplices (`0` where `h` is undefined). -/
noncomputable def coneHomotopy {W W' : C}
    (h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))) (m : ℕ) :
    (ULift.{u} (W ⟶ U.obj m) →₀ R) →ₗ[R] (ULift.{u} (W' ⟶ U.obj (m + 1)) →₀ R) :=
  Finsupp.linearCombination R fun σ ↦ (h m σ.down).elim 0 fun y ↦ Finsupp.single (ULift.up y) 1

variable {U} in
lemma coneHomotopy_single_of_eq {W W' : C}
    {h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))} {m : ℕ} {σ : W ⟶ U.obj m}
    {y : W' ⟶ U.obj (m + 1)} (hy : h m σ = some y) :
    coneHomotopy R h m (Finsupp.single (ULift.up σ) 1) = Finsupp.single (ULift.up y) 1 := by
  simp [coneHomotopy, hy]

variable {U} in
/-- Pullback of chains along `g : W' ⟶ W`. -/
noncomputable def chainPullback {W W' : C} (g : W' ⟶ W) (n : ℕ) :
    (ULift.{u} (W ⟶ U.obj n) →₀ R) →ₗ[R] (ULift.{u} (W' ⟶ U.obj n) →₀ R) :=
  Finsupp.lmapDomain R R fun σ ↦ ULift.up (g ≫ σ.down)

lemma chainD_coneHomotopy_succ {W W' : C} {g : W' ⟶ W} {v : W' ⟶ U.obj 0}
    {h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))} {n : ℕ}
    (c : ULift.{u} (W ⟶ U.obj (n + 1)) →₀ R)
    (hc : ∀ σ ∈ c.support, U.IsCone g v h (n + 1) σ.down) :
    U.chainD R W' (n + 1) (coneHomotopy R h (n + 1) c) =
      coneHomotopy R h n (U.chainD R W n c) +
        ((-1 : ℤ) ^ (n + 2)) • chainPullback R g (n + 1) c := by
  have := Finsupp.linearMap_apply_eq_of_forall_mem_support
    ((U.chainD R W' (n + 1)).comp (coneHomotopy R h (n + 1)))
    ((coneHomotopy R h n).comp (U.chainD R W n) + ((-1 : ℤ) ^ (n + 2)) • chainPullback R g (n + 1))
    c ?_
  · simpa using this
  rintro ⟨σ⟩ hσ
  obtain ⟨y, hy, hlast, hf⟩ := hc _ hσ
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    coneHomotopy_single_of_eq R hy, chainD_single, map_sum, map_zsmul,
    coneHomotopy_single_of_eq R (hf _).1, chainPullback, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Fin.sum_univ_castSucc (n := n + 2), Fin.val_castSucc, Fin.val_last,
    hlast]

variable {U} in
/-- The augmentation on chains: the sum of the coefficients. -/
noncomputable abbrev chainAug (W : C) (n : ℕ) : (ULift.{u} (W ⟶ U.obj n) →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R fun _ ↦ (1 : R)

lemma chainD_coneHomotopy_zero {W W' : C} {g : W' ⟶ W} {v : W' ⟶ U.obj 0}
    {h : ∀ m, (W ⟶ U.obj m) → Option (W' ⟶ U.obj (m + 1))}
    (c : ULift.{u} (W ⟶ U.obj 0) →₀ R)
    (hc : ∀ σ ∈ c.support, U.IsCone g v h 0 σ.down) :
    U.chainD R W' 0 (coneHomotopy R h 0 c) + chainPullback R g 0 c =
      chainAug (U := U) R W 0 c • Finsupp.single (ULift.up v) 1 := by
  have := Finsupp.linearMap_apply_eq_of_forall_mem_support
    ((U.chainD R W' 0).comp (coneHomotopy R h 0) + chainPullback R g 0)
    ((chainAug (U := U) R W 0).smulRight (Finsupp.single (ULift.up v) 1)) c ?_
  · simpa using this
  rintro ⟨σ⟩ hσ
  obtain ⟨y, hy, h₁, h₀⟩ := hc _ hσ
  simp [coneHomotopy_single_of_eq R hy, chainD_single, chainPullback, Fin.sum_univ_two, h₁, h₀]

variable {U} {R}

lemma IsHypercover.imageSieve_freeYonedaD_mem (hU : U.IsHypercover J) (n : ℕ) (W : C)
    (c : ULift.{u} (W ⟶ U.obj (n + 1)) →₀ R) (hc : U.chainD R W n c = 0) :
    Presheaf.imageSieve (U.freeYonedaD R (n + 1)) (C := C) (U := W) c ∈ J W := by
  classical
  refine J.superset_covering ?_ (hU.coneSieve_mem (n + 1) (c.support.image ULift.down))
  rintro W' g ⟨v, h, hcone⟩
  refine ⟨(((-1 : ℤ) ^ n) • coneHomotopy R h (n + 1) c : ULift.{u} (W' ⟶ _) →₀ R), ?_⟩
  change ((U.freeYonedaD R (n + 1)).app (op W')).hom _ = chainPullback R g (n + 1) c
  rw [freeYonedaD_app_apply, map_zsmul, chainD_coneHomotopy_succ R U c
    (fun σ hσ ↦ hcone _ (Finset.mem_image_of_mem _ hσ)), hc, map_zero, zero_add, smul_smul,
    ← pow_add, show n + (n + 2) = 2 * (n + 1) by ring, pow_mul]
  simp

lemma IsHypercover.imageSieve_freeYonedaD_zero_mem (hU : U.IsHypercover J) (W : C)
    (c : ULift.{u} (W ⟶ U.obj 0) →₀ R) (hc : chainAug (U := U) R W 0 c = 0) :
    Presheaf.imageSieve (U.freeYonedaD R 0) (C := C) (U := W) c ∈ J W := by
  classical
  refine J.superset_covering ?_ (hU.coneSieve_mem 0 (c.support.image ULift.down))
  rintro W' g ⟨v, h, hcone⟩
  refine ⟨(-coneHomotopy R h 0 c : ULift.{u} (W' ⟶ _) →₀ R), ?_⟩
  change ((U.freeYonedaD R 0).app (op W')).hom _ = chainPullback R g 0 c
  have := chainD_coneHomotopy_zero R U c (fun σ hσ ↦ hcone _ (Finset.mem_image_of_mem _ hσ))
  rw [hc, zero_smul, add_eq_zero_iff_eq_neg] at this
  rw [freeYonedaD_app_apply, map_neg, this, neg_neg]

end Chains

variable (U : SemiSimplicialObject C)

lemma freeYonedaD_comp (n : ℕ) : U.freeYonedaD R (n + 1) ≫ U.freeYonedaD R n = 0 :=
  U.sum_map_δ_comp_sum_map_δ (freeYoneda R) n

lemma freeYonedaD_comp_freeYonedaToConst :
    U.freeYonedaD R 0 ≫ freeYonedaToConst R (U.obj 0) = 0 := by
  rw [freeYonedaD, Preadditive.sum_comp, Fin.sum_univ_two, Preadditive.zsmul_comp,
    Preadditive.zsmul_comp, freeYoneda_map_comp_freeYonedaToConst,
    freeYoneda_map_comp_freeYonedaToConst]
  simp

/-- The differential of the free complex is the sheafification of the differential of the
complex of free presheaves. -/
lemma map_freeYonedaD (n : ℕ) :
    (presheafToSheaf J _).map (U.freeYonedaD R n) = (U.freeComplex J R).d (n + 1) n := by
  rw [freeComplex_d, freeYonedaD, Functor.map_sum]
  simp only [Functor.map_zsmul]
  rfl

namespace IsHypercover

variable {J R}
variable {U : SemiSimplicialObject C} (hU : U.IsHypercover J)
include hU

variable (R) in
/-- **The free complex of a hypercover is exact in positive degrees** (blueprint
`corollary-cohomology-pro-etale-affine`). -/
theorem exactAt_freeComplex (n : ℕ) :
    (U.freeComplex J R).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  have key := Presheaf.exact_map_presheafToSheaf
    (ShortComplex.mk (U.freeYonedaD R (n + 1)) (U.freeYonedaD R n) (U.freeYonedaD_comp R n))
    fun W c hc ↦ hU.imageSieve_freeYonedaD_mem n W c
      ((U.freeYonedaD_app_apply R n W c).symm.trans hc)
  refine (ShortComplex.exact_iff_of_iso ?_).1 key
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [map_freeYonedaD]) (by simp [map_freeYonedaD])

variable (R) in
/-- The free complex of a hypercover is exact at `R[U₀]`, augmented to the constant sheaf. -/
theorem exact_freeAugmentation :
    (ShortComplex.mk _ _ (U.freeComplex_d_freeAugmentation J R)).Exact := by
  have key := Presheaf.exact_map_presheafToSheaf
    (ShortComplex.mk (U.freeYonedaD R 0) (freeYonedaToConst R (U.obj 0))
      (U.freeYonedaD_comp_freeYonedaToConst R))
    fun W c hc ↦ hU.imageSieve_freeYonedaD_zero_mem W c hc
  refine (ShortComplex.exact_iff_of_iso ?_).1 key
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [map_freeYonedaD]) (by simp [freeAugmentation])

variable (R) in
/-- The augmentation of the free complex of a hypercover is an epimorphism. -/
theorem epi_freeAugmentation : Epi (U.freeAugmentation J R) :=
  Presheaf.epi_map_presheafToSheaf _ fun W r ↦ J.superset_covering
    (fun W' _ hg ↦ ⟨(Finsupp.single (ULift.up (show Nonempty _ from hg).some) r :
        ULift.{u} (W' ⟶ U.obj 0) →₀ R),
      (Finsupp.linearCombination_single R _ _).trans (mul_one (M := R) r)⟩) (hU.coverSieve_mem W)

/-- The cochain complex of an injective sheaf on a hypercover is exact in positive degrees,
elementwise. -/
lemma exists_cochainDifferential_eq_of_injective (I : Sheaf J (ModuleCat.{max u v} R))
    [Injective I] (n : ℕ) (z : I.obj.obj (op (U.obj (n + 1))))
    (hz : (U.cochainDifferential I.obj (n + 1)).hom z = 0) :
    ∃ y, (U.cochainDifferential I.obj n).hom y = z := by
  have hφ : (U.freeComplex J R).d (n + 1 + 1) (n + 1) ≫
      (freeSheafHomEquiv J R (U.obj (n + 1)) I).symm z = 0 := by
    apply (freeSheafHomEquiv J R _ I).injective
    rw [freeSheafHomEquiv_d_comp, Equiv.apply_symm_apply, hz, freeSheafHomEquiv_zero]
  have hex := (HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)).1
    (hU.exactAt_freeComplex R n)
  refine ⟨freeSheafHomEquiv J R _ I (hex.descToInjective _ hφ), ?_⟩
  rw [← freeSheafHomEquiv_d_comp]
  have := hex.comp_descToInjective _ hφ
  rw [HomologicalComplex.shortComplexFunctor'_obj_g] at this
  rw [this, Equiv.apply_symm_apply]

/-- **The cochain complex of an injective sheaf on a hypercover is exact in positive degrees**
(blueprint `corollary-cohomology-pro-etale-affine`). -/
theorem exactAt_cochainComplex_of_injective (I : Sheaf J (ModuleCat.{max u v} R)) [Injective I]
    (n : ℕ) : (U.cochainComplex I.obj).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro z hz
  obtain ⟨y, hy⟩ := hU.exists_cochainDifferential_eq_of_injective I n z (by
    rw [HomologicalComplex.shortComplexFunctor'_obj_g, cochainComplex_d] at hz
    exact hz)
  exact ⟨y, by rw [HomologicalComplex.shortComplexFunctor'_obj_f, cochainComplex_d]; exact hy⟩

omit hU in
variable (R) in
/-- The augmentation `R^{(Hom(-, T))} ⟶ R` is an isomorphism if `T` is a terminal object. -/
lemma isIso_freeYonedaToConst {T : C} (hT : IsTerminal T) :
    IsIso (freeYonedaToConst R T) := by
  have (W : Cᵒᵖ) : IsIso ((freeYonedaToConst R T).app W) := by
    have : Unique (ULift.{u} (W.unop ⟶ T)) :=
      ⟨⟨⟨hT.from _⟩⟩, fun a ↦ ULift.ext (hT.hom_ext _ _)⟩
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ Finsupp.unique_ext ?_, fun r ↦ ⟨Finsupp.single default r, ?_⟩⟩
    · have h₁ := Finsupp.linearCombination_unique (α := ULift.{u} (W.unop ⟶ T)) (R := R) a
        (fun _ ↦ (1 : R))
      have h₂ := Finsupp.linearCombination_unique (α := ULift.{u} (W.unop ⟶ T)) (R := R) b
        (fun _ ↦ (1 : R))
      simp only [smul_eq_mul, mul_one] at h₁ h₂
      exact h₁.symm.trans ((show _ = _ from hab).trans h₂)
    · exact (Finsupp.linearCombination_single R _ _).trans (mul_one (M := R) r)
  exact NatIso.isIso_of_isIso_app _

/-- **The degree zero cocycles of an injective sheaf on a hypercover are its global sections**
(blueprint `corollary-cohomology-pro-etale-affine`): if `T` is a terminal object, the sequence
`0 ⟶ I(T) ⟶ I(U₀) ⟶ I(U₁)` is exact. -/
theorem exact_cochainComplex_zero_of_injective (I : Sheaf J (ModuleCat.{max u v} R))
    [Injective I] {T : C} (hT : IsTerminal T) :
    (ShortComplex.mk (I.obj.map (hT.from (U.obj 0)).op) (U.cochainDifferential I.obj 0)
      (by
        rw [cochainDifferential, Preadditive.comp_sum, Fin.sum_univ_two, Preadditive.comp_zsmul,
          Preadditive.comp_zsmul, ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
          hT.hom_ext (U.δ 0 1 ≫ hT.from _) (U.δ 0 0 ≫ hT.from _)]
        simp)).Exact ∧ Mono (I.obj.map (hT.from (U.obj 0)).op) := by
  have hε : (freeSheaf J R).map (hT.from (U.obj 0)) ≫
      (presheafToSheaf J _).map (freeYonedaToConst R T) = U.freeAugmentation J R := by
    rw [freeAugmentation, ← freeYoneda_map_comp_freeYonedaToConst (hT.from (U.obj 0)),
      Functor.map_comp]
    rfl
  have := hU.epi_freeAugmentation R
  have := isIso_freeYonedaToConst R hT
  constructor
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    have hφ : (U.freeComplex J R).d 1 0 ≫ (freeSheafHomEquiv J R (U.obj 0) I).symm z = 0 := by
      apply (freeSheafHomEquiv J R _ I).injective
      rw [freeSheafHomEquiv_d_comp, Equiv.apply_symm_apply, freeSheafHomEquiv_zero]
      exact hz
    let ψ := (hU.exact_freeAugmentation R).descToInjective _ hφ
    refine ⟨freeSheafHomEquiv J R T I ((presheafToSheaf J _).map (freeYonedaToConst R T) ≫ ψ),
      ?_⟩
    change (I.obj.map (hT.from (U.obj 0)).op).hom _ = z
    rw [← freeSheafHomEquiv_map_comp, ← Category.assoc, hε]
    have := (hU.exact_freeAugmentation R).comp_descToInjective _ hφ
    dsimp only at this
    rw [this, Equiv.apply_symm_apply]
  · rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨φ, rfl⟩ := (freeSheafHomEquiv J R T I).surjective y
    rw [← freeSheafHomEquiv_map_comp, ← freeSheafHomEquiv_zero J R _ I] at hy
    replace hy := (freeSheafHomEquiv J R _ I).injective hy
    have h0 : inv ((presheafToSheaf J _).map (freeYonedaToConst R T)) ≫ φ = 0 := by
      rw [← cancel_epi (U.freeAugmentation J R), ← hε, Category.assoc, IsIso.hom_inv_id_assoc,
        hy, comp_zero]
    rw [← IsIso.hom_inv_id_assoc ((presheafToSheaf J _).map (freeYonedaToConst R T)) φ, h0,
      comp_zero, freeSheafHomEquiv_zero]

end IsHypercover

end CategoryTheory.SemiSimplicialObject
