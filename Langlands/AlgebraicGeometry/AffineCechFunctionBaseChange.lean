import Langlands.AbelianScheme.ArtinianHodgeStructureCohomology
import Langlands.AlgebraicGeometry.AffineCechDeRhamCoverPullback
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Scalar extension of the function Čech complex of a finite affine cover -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct
open Langlands.Cohomology
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter)

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

/-- Make an affine cover from a family of affine opens with union the whole scheme. -/
def affineCoverOfOpens {X : Scheme.{u}} {I : Type u} (V : I → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hc : ⨆ i, V i = ⊤) : Scheme.AffineOpenCover.{u} X := by
  classical
  have hx : ∀ x : X, ∃ i, x ∈ V i := fun x =>
    Opens.mem_iSup.mp (hc.symm ▸ (show x ∈ (⊤ : X.Opens) from trivial))
  exact
    { I₀ := I
      X := fun i => Γ(X, V i)
      f := fun i => (hV i).fromSpec
      idx := fun x => (hx x).choose
      covers := fun x => by
        rw [(hV _).range_fromSpec]
        exact (hx x).choose_spec }

@[simp]
lemma coverOpens_affineCoverOfOpens {X : Scheme.{u}} {I : Type u} (V : I → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hc : ⨆ i, V i = ⊤) (i : I) :
    coverOpens (affineCoverOfOpens V hV hc) i = V i :=
  (hV i).opensRange_fromSpec

open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (K : Type u) [Field K] [Algebra R K]

/-- The projection from the base change to the original scheme. -/
abbrev fibreProjection := pullback.fst f (fibreMap K)

/-- The structural morphism of the actual base change. -/
abbrev fibreStructure := pullback.snd f (fibreMap K)

variable (U : Scheme.AffineOpenCover.{u} X)

private lemma fibreOpens_affine (i : U.I₀) :
    IsAffineOpen (fibreProjection f K ⁻¹ᵁ coverOpens U i) := by
  have : IsAffineHom (fibreMap (R := CommRingCat.of R) K) := isAffineHom_of_isAffine _
  have : IsAffineHom (fibreProjection f K) := MorphismProperty.pullback_fst
    (P := @IsAffineHom) _ _ inferInstance
  exact (isAffineOpen_opensRange (U.f i)).preimage _

private lemma fibreOpens_cover : ⨆ i, fibreProjection f K ⁻¹ᵁ coverOpens U i = ⊤ := by
  rw [← (fibreProjection f K).preimage_iSup, show ⨆ i, coverOpens U i = ⊤ from
    U.openCover.iSup_opensRange, Scheme.Hom.preimage_top]

/-- The indexed affine cover of the fibre by preimages of the original opens. -/
abbrev fibreAffineCover : Scheme.AffineOpenCover.{u} (pullback f (fibreMap K)) :=
  affineCoverOfOpens (fun i => fibreProjection f K ⁻¹ᵁ coverOpens U i)
    (fibreOpens_affine f K U) (fibreOpens_cover f K U)

@[simp]
lemma coverOpens_fibreAffineCover (i : U.I₀) :
    coverOpens (fibreAffineCover f K U) i = fibreProjection f K ⁻¹ᵁ coverOpens U i :=
  coverOpens_affineCoverOfOpens _ (fibreOpens_affine f K U) (fibreOpens_cover f K U) i

instance [Finite U.I₀] : Finite (fibreAffineCover f K U).I₀ := inferInstanceAs (Finite U.I₀)

lemma inter_fibreAffineCover {p : ℕ} (σ : Fin (p + 1) → U.I₀) :
    inter (coverOpens (fibreAffineCover f K U)) σ =
      fibreProjection f K ⁻¹ᵁ inter (coverOpens U) σ := by
  ext x
  change x ∈ inter (coverOpens (fibreAffineCover f K U)) σ ↔
    x ∈ fibreProjection f K ⁻¹ᵁ inter (coverOpens U) σ
  rw [Scheme.Hom.mem_preimage, Cech.mem_inter, Cech.mem_inter]
  simp only [coverOpens_fibreAffineCover, Scheme.Hom.mem_preimage]

private abbrev sectionsOn {T : Type u} [CommRing T] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of T)) (V : Y.Opens) := (sectionAlgebras g).obj (op V)

private def fibreTensorMap (W : X.Opens) :
    CommRingCat.of (K ⊗[R] sectionsOn f W) ⟶
      Γ(pullback f (fibreMap K), fibreProjection f K ⁻¹ᵁ W) := by
  letI (V : X.Opens) : Algebra (CommRingCat.of R) Γ(X, V) :=
    Scheme.TwoAffineOpenCover.algebraOfHom f V
  exact fibreTensor f K (sectionAlgebras_algebraMap f) W

private lemma fibreTensorMap_tmul (W : X.Opens) (a : K) (x : sectionsOn f W) :
    (fibreTensorMap f K W).hom (a ⊗ₜ[R] x) =
      (fibreSec f K W).hom a * ((fibreProjection f K).appLE W _ le_rfl).hom x := by
  let (V : X.Opens) : Algebra (CommRingCat.of R) Γ(X, V) :=
    Scheme.TwoAffineOpenCover.algebraOfHom f V
  exact fibreTensor_tmul f K (sectionAlgebras_algebraMap f) W a x

private lemma isIso_fibreTensor (W : X.Opens) (hW : IsAffineOpen W) :
    IsIso (fibreTensorMap f K W) := by
  let (V : X.Opens) : Algebra (CommRingCat.of R) Γ(X, V) :=
    Scheme.TwoAffineOpenCover.algebraOfHom f V
  change IsIso (fibreTensor f K (sectionAlgebras_algebraMap f) W)
  have h : IsPushout (CommRingCat.ofHom (algebraMap R K))
      (CommRingCat.ofHom (algebraMap R Γ(X, W))) (fibreSec f K W)
      ((fibreProjection f K).appLE W _ le_rfl) := by
    have e : CommRingCat.ofHom (algebraMap R Γ(X, W)) = secHom f W := rfl
    rw [e]
    exact isPushout_fibre f K hW
  let p := CommRingCat.isPushout_tensorProduct R K Γ(X, W)
  have eq : (p.isoIsPushout _ _ h).hom = fibreTensor f K (sectionAlgebras_algebraMap f) W :=
    p.hom_ext (by simp [fibreTensor]) (by simp [fibreTensor])
  rw [← eq]
  infer_instance

/-- The base-changed affine section algebra as a tensor product, allowing
an equal presentation of the inverse-image open. -/
def fibreSectionsEquiv (W : X.Opens) (hW : IsAffineOpen W)
    (V : (pullback f (fibreMap K)).Opens) (e : V = fibreProjection f K ⁻¹ᵁ W) :
    K ⊗[R] sectionsOn f W ≃ₐ[K] sectionsOn (fibreStructure f K) V := by
  let q := fibreTensorMap f K W
  let ρ := (pullback f (fibreMap K)).presheaf.map (homOfLE e.le).op
  haveI : IsIso q := isIso_fibreTensor f K W hW
  haveI : IsIso ρ := by
    dsimp only [ρ]
    subst V
    change IsIso ((pullback f (fibreMap K)).presheaf.map (𝟙 _))
    infer_instance
  refine AlgEquiv.ofBijective { (q ≫ ρ).hom with commutes' := fun k => ?_ }
    (ConcreteCategory.bijective_of_isIso (q ≫ ρ))
  change ρ ((fibreTensorMap f K W).hom (k ⊗ₜ[R] (1 : sectionsOn f W))) =
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (fibreStructure f K).appLE ⊤ V le_top).hom k)
  rw [fibreTensorMap_tmul, map_one, mul_one]
  change (fibreSec f K W ≫ ρ).hom k = _
  dsimp only [fibreSec, ρ]
  rw [Category.assoc, Scheme.Hom.appLE_map]

lemma fibreSectionsEquiv_tmul (W : X.Opens) (hW : IsAffineOpen W)
    (V : (pullback f (fibreMap K)).Opens) (e : V = fibreProjection f K ⁻¹ᵁ W)
    (a : K) (x : sectionsOn f W) :
    fibreSectionsEquiv f K W hW V e (a ⊗ₜ[R] x) =
      a • (show sectionsOn (fibreStructure f K) V from
        ((fibreProjection f K).appLE W V e.le).hom x) := by
  let ρ := (pullback f (fibreMap K)).presheaf.map (homOfLE e.le).op
  change ρ ((fibreTensorMap f K W).hom (a ⊗ₜ[R] x)) = _
  rw [fibreTensorMap_tmul, map_mul]
  rw [Algebra.smul_def]
  congr 1
  · change (fibreSec f K W ≫ ρ).hom a = _
    dsimp only [fibreSec, ρ]
    rw [Category.assoc, Scheme.Hom.appLE_map]
    rfl
  · change ((fibreProjection f K).appLE W _ le_rfl ≫ ρ).hom x = _
    dsimp only [ρ]
    rw [Scheme.Hom.appLE_map]

variable [IsSeparated f] [Finite U.I₀]

/-- Base change of the actual function cochains along a field-valued base map. -/
def fibreFunctionCochainEquiv (p : ℕ) : K ⊗[R] Cochains U (functions f) p ≃ₗ[K]
    Cochains (fibreAffineCover f K U) (functions (fibreStructure f K)) p := by
  classical
  letI := Fintype.ofFinite U.I₀
  let A (σ : Fin (p + 1) → U.I₀) := sectionsOn f (inter (coverOpens U) σ)
  exact (TensorProduct.piRight R K K (fun σ : Fin (p + 1) → U.I₀ => A σ)).trans
    (LinearEquiv.piCongrRight fun σ => (fibreSectionsEquiv f K _
      (isAffineOpen_inter f U σ) _ (inter_fibreAffineCover f K U σ)).toLinearEquiv)

private abbrev fibreCechPull (p : ℕ) :=
  Cech.pull (fibreProjection f K) (coverOpens U) (coverOpens (fibreAffineCover f K U))
    id (fun i => (coverOpens_fibreAffineCover f K U i).le) p

lemma fibreFunctionCochainEquiv_tmul (p : ℕ) (a : K) (c : Cochains U (functions f) p) :
    fibreFunctionCochainEquiv f K U p (a ⊗ₜ[R] c) =
      a • (show Cochains (fibreAffineCover f K U) (functions (fibreStructure f K)) p from
        fibreCechPull f K U p c) := by
  funext σ
  exact fibreSectionsEquiv_tmul f K _ (isAffineOpen_inter f U σ) _
    (inter_fibreAffineCover f K U σ) a (c σ)

/-- Scalar extension of the actual cochains preserves the signed Čech differential. -/
lemma fibreFunctionCochainEquiv_cechD (p : ℕ) (x : K ⊗[R] Cochains U (functions f) p) :
    fibreFunctionCochainEquiv f K U (p + 1) ((cechD U (functions f) p).baseChange K x) =
    cechD (fibreAffineCover f K U) (functions (fibreStructure f K)) p
      (fibreFunctionCochainEquiv f K U p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    rw [LinearMap.baseChange_tmul, fibreFunctionCochainEquiv_tmul, fibreFunctionCochainEquiv_tmul,
      map_smul]
    exact congrArg (a • ·) (Cech.d_pull (fibreProjection f K)
      (fun i => (coverOpens_fibreAffineCover f K U i).le) p c).symm
  | add x y hx hy => simp only [map_add, hx, hy]

omit [IsSeparated f] [Finite U.I₀] in
/-- The same index assignment works after base change in a commuting square. -/
lemma fibreCover_le_preimage
    (a : X ⟶ X) (a' : pullback f (fibreMap K) ⟶ pullback f (fibreMap K))
    (he : a' ≫ fibreProjection f K = fibreProjection f K ≫ a)
    (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ a ⁻¹ᵁ coverOpens U (β i))
    (i : U.I₀) : coverOpens (fibreAffineCover f K U) i ≤
      a' ⁻¹ᵁ coverOpens (fibreAffineCover f K U) (β i) := by
  rw [coverOpens_fibreAffineCover, coverOpens_fibreAffineCover, ← Scheme.Hom.comp_preimage,
    he, Scheme.Hom.comp_preimage]
  exact (fibreProjection f K).preimage_mono (hβ i)

/-- The base-change equivalence of function cochains intertwines pullback
endomorphisms in a commuting square of schemes. -/
lemma fibreFunctionCochainEquiv_pullFunctions
    (a : X ⟶ X) (ha : a ≫ f = f)
    (a' : pullback f (fibreMap K) ⟶ pullback f (fibreMap K))
    (ha' : a' ≫ fibreStructure f K = fibreStructure f K)
    (he : a' ≫ fibreProjection f K = fibreProjection f K ≫ a)
    (β : U.I₀ → U.I₀) (hβ : ∀ i, coverOpens U i ≤ a ⁻¹ᵁ coverOpens U (β i))
    (p : ℕ) (x : K ⊗[R] Cochains U (functions f) p) :
    fibreFunctionCochainEquiv f K U p ((pullFunctions a ha β hβ p).baseChange K x) =
      pullFunctions a' ha' β (fibreCover_le_preimage f K U a a' he β hβ) p
        (fibreFunctionCochainEquiv f K U p x) := by
  induction x using TensorProduct.inductionOn with
  | tmul k c =>
    rw [LinearMap.baseChange_tmul, fibreFunctionCochainEquiv_tmul, fibreFunctionCochainEquiv_tmul,
      map_smul]
    apply congrArg (k • ·)
    let V := coverOpens (fibreAffineCover f K U)
    let hβ' := fibreCover_le_preimage f K U a a' he β hβ
    change fibreCechPull f K U p (Cech.pull a (coverOpens U) (coverOpens U) β hβ p c) =
      Cech.pull a' V V β hβ' p (fibreCechPull f K U p c)
    unfold fibreCechPull
    rw [Cech.pull_comp, Cech.pull_comp]
    funext σ
    rw [Cech.pull_apply, Cech.pull_apply, appLE_congr_hom he]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Langlands.AlgebraicGeometry.AffineCechDeRham
