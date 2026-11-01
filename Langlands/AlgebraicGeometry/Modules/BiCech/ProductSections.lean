import Langlands.AlgebraicGeometry.Modules.BiCech.GlobalSections
import Langlands.AlgebraicGeometry.Modules.BiCech.CupBijective

/-!
# Global sections of the bi-Čech complex of an external tensor product

Let `P` be a fibre product of `πX : X ⟶ Spec R` and `πY : Y ⟶ Spec R` with projections `p₁`,
`p₂` and `πP = p₁ ≫ πX`, let `𝒰`, `𝒱` be ordered affine covers of `X`, `Y`, and let `L`, `M`
be module sheaves on `X`, `Y`. For the bi-cover `prodBiCover p₁ p₂ 𝒰 𝒱` and
`F = p₁^* L ⊗ p₂^* M`, this file provides the `R`-linear maps between the cochains of the
factors and the components of global sections of the bi-Čech terms:

* `cupFam p q`, the cup map on families
  `C^p(𝒰, L) ⊗[R] C^q(𝒱, M) → ∏_{s, t} F(p₁⁻¹ 𝒰.inter s ∩ p₂⁻¹ 𝒱.inter t)`, which is
  bijective when all finite intersections are affine and carry frames;
* `insLin` and `compLin`, the insertion of a bidegree-`(p, q)` family as a global section
  and the extraction of its bidegree-`(p, q)` components.

The cup map turns the Čech differentials of the factors into the differentials `horF`,
`verF` of the bi-Čech complex.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.BiCech

open CechResolution Scheme.Modules OModulePresheaf

variable {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
  {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {πP : P ⟶ Spec R} (hπ : p₁ ≫ πX = πP)
  (hP : IsPullback p₁ p₂ πX πY) (𝒰 : X.OrderedAffineCover) (𝒱 : Y.OrderedAffineCover)
  (L : X.Modules) (M : Y.Modules)

variable (p₁ p₂) in
/-- The bi-cover of a fibre product given by ordered affine covers of the two factors. -/
abbrev prodBiCover : BiCover P := ⟨X, Y, p₁, p₂, 𝒰, 𝒱⟩

section Cup

variable {𝒰 𝒱 L M}

lemma cup_zsmul_left {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    (k : ℤ) (l : Γ(L, U)) (m : Γ(M, V)) : cup hW (k • l) m = k • cup hW l m :=
  map_zsmul (AddMonoidHom.mk' (fun l => cup hW l m) fun l l' => cup_add_left hW l l' m) k l

lemma cup_zsmul_right {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    (k : ℤ) (l : Γ(L, U)) (m : Γ(M, V)) : cup hW l (k • m) = k • cup hW l m :=
  map_zsmul (AddMonoidHom.mk' (fun m => cup hW l m) fun m m' => cup_add_right hW l m m') k m

lemma cup_sum_left {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    {ι : Type*} (S : Finset ι) (l : ι → Γ(L, U)) (m : Γ(M, V)) :
    cup hW (∑ i ∈ S, l i) m = ∑ i ∈ S, cup hW (l i) m :=
  map_sum (AddMonoidHom.mk' (fun l => cup hW l m) fun l l' => cup_add_left hW l l' m) l S

lemma cup_sum_right {U : X.Opens} {V : Y.Opens} {W : P.Opens} (hW : W ≤ p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V)
    {ι : Type*} (S : Finset ι) (l : Γ(L, U)) (m : ι → Γ(M, V)) :
    cup hW l (∑ i ∈ S, m i) = ∑ i ∈ S, cup hW l (m i) :=
  map_sum (AddMonoidHom.mk' (fun m => cup hW l m) fun m m' => cup_add_right hW l m m') m S

end Cup

lemma biOpen_le_prod {p q : ℕ} (s : 𝒰.Idx p) (t : 𝒱.Idx q) :
    biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t ≤ p₁ ⁻¹ᵁ 𝒰.inter s ⊓ p₂ ⁻¹ᵁ 𝒱.inter t :=
  le_refl _

/-- The cup map on families of sections, `C^p(𝒰, L) ⊗ C^q(𝒱, M) → ∏_{s, t} F(biOpen s t)`. -/
def cupFam (p q : ℕ) :
    (ofModules πX L).cochain 𝒰 p ⊗[R] (ofModules πY M).cochain 𝒱 q →ₗ[R]
      ∀ (s : 𝒰.Idx p) (t : 𝒱.Idx q),
        (ofModules πP (extTensor p₁ p₂ L M)).obj (biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t) :=
  LinearMap.pi fun s => LinearMap.pi fun t =>
    (cupLin hπ hP L M (biOpen_le_prod 𝒰 𝒱 s t)) ∘ₗ
      TensorProduct.map (LinearMap.proj s) (LinearMap.proj t)

lemma cupFam_tmul (p q : ℕ) (a : (ofModules πX L).cochain 𝒰 p)
    (b : (ofModules πY M).cochain 𝒱 q) (s : 𝒰.Idx p) (t : 𝒱.Idx q) :
    cupFam hπ hP 𝒰 𝒱 L M p q (a ⊗ₜ b) s t = cup (biOpen_le_prod 𝒰 𝒱 s t) (a s) (b t) := by
  simp only [cupFam, LinearMap.pi_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
    LinearMap.proj_apply]
  exact cupLin_tmul hπ hP L M _ _ _

include hπ hP in
/-- The cup map on families is bijective when all finite intersections of the covers are affine
and carry frames. -/
theorem cupFam_bijective (p q : ℕ) (hU : ∀ s : 𝒰.Idx p, IsAffineOpen (𝒰.inter s))
    (hV : ∀ t : 𝒱.Idx q, IsAffineOpen (𝒱.inter t))
    (hL : ∀ s : 𝒰.Idx p, ∃ e : Γ(L, 𝒰.inter s), IsFrameOn e (𝒰.inter s))
    (hM : ∀ t : 𝒱.Idx q, ∃ e : Γ(M, 𝒱.inter t), IsFrameOn e (𝒱.inter t)) :
    Function.Bijective (cupFam hπ hP 𝒰 𝒱 L M p q) := by
  classical
  let ψ := TensorProduct.piLeft (R := R) (N := (ofModules πY M).cochain 𝒱 q)
      (fun s : 𝒰.Idx p => (ofModules πX L).obj (𝒰.inter s)) ≪≫ₗ
    LinearEquiv.piCongrRight fun s =>
      TensorProduct.piRight (R := R) (S := R) (N := (ofModules πX L).obj (𝒰.inter s))
        (fun t : 𝒱.Idx q => (ofModules πY M).obj (𝒱.inter t))
  have hψ : ∀ x s t, ψ x s t = TensorProduct.map (LinearMap.proj s) (LinearMap.proj t) x := by
    intro x s t
    induction x with
    | tmul a b => simp [ψ]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have e : ⇑(cupFam hπ hP 𝒰 𝒱 L M p q) =
      (fun G s t => cupLin hπ hP L M (biOpen_le_prod 𝒰 𝒱 s t) (G s t)) ∘ ψ := by
    funext x s t
    simp only [Function.comp_apply, hψ]
    rfl
  rw [e]
  refine (Function.Bijective.piMap fun s => Function.Bijective.piMap fun t => ?_).comp
    ψ.bijective
  obtain ⟨e, he⟩ := hL s
  obtain ⟨e', he'⟩ := hM t
  exact cupLin_bijective hπ hP (hU s) (hV t) he he'

section Differentials

variable {𝒰 𝒱 L M}

/-- The Čech differential on families of sections of `L`. -/
def dΓ {p : ℕ} (a : ∀ s : 𝒰.Idx p, Γ(L, 𝒰.inter s)) (s : 𝒰.Idx (p + 1)) : Γ(L, 𝒰.inter s) :=
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    L.presheaf.map (homOfLE (𝒰.inter_le_inter_face s j)).op (a (𝒰.face s j))

lemma d_eq_dΓ {p : ℕ} (a : (ofModules πX L).cochain 𝒰 p) (s : 𝒰.Idx (p + 1)) :
    ((ofModules πX L).d 𝒰 p a s : Γ(L, 𝒰.inter s)) = dΓ (L := L) a s := by
  rw [d_apply]
  rfl

variable (p₁ p₂) in
/-- The cup map on families of sections, at the level of sections. -/
def cupFamFun {p q : ℕ} (a : ∀ s : 𝒰.Idx p, Γ(L, 𝒰.inter s)) (b : ∀ t : 𝒱.Idx q, Γ(M, 𝒱.inter t))
    (s : 𝒰.Idx p) (t : 𝒱.Idx q) :
    Γ(extTensor p₁ p₂ L M, biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t) :=
  cup (biOpen_le_prod 𝒰 𝒱 s t) (a s) (b t)

lemma horF_cupFamFun {p q : ℕ} (a : ∀ s : 𝒰.Idx p, Γ(L, 𝒰.inter s))
    (b : ∀ t : 𝒱.Idx q, Γ(M, 𝒱.inter t)) (s : 𝒰.Idx (p + 1)) (t : 𝒱.Idx q) :
    horF (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (cupFamFun p₁ p₂ a b) s t =
      cupFamFun p₁ p₂ (dΓ a) b s t := by
  unfold horF cupFamFun dΓ
  rw [cup_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cup_zsmul_left, map_cup, cup_map_left]

/-- The Čech differential on families of sections of `M`. -/
def dΓ' {q : ℕ} (b : ∀ t : 𝒱.Idx q, Γ(M, 𝒱.inter t)) (t : 𝒱.Idx (q + 1)) : Γ(M, 𝒱.inter t) :=
  ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    M.presheaf.map (homOfLE (𝒱.inter_le_inter_face t j)).op (b (𝒱.face t j))

lemma d_eq_dΓ' {q : ℕ} (b : (ofModules πY M).cochain 𝒱 q) (t : 𝒱.Idx (q + 1)) :
    ((ofModules πY M).d 𝒱 q b t : Γ(M, 𝒱.inter t)) = dΓ' (M := M) b t := by
  rw [d_apply]
  rfl

lemma verF_cupFamFun {p q : ℕ} (a : ∀ s : 𝒰.Idx p, Γ(L, 𝒰.inter s))
    (b : ∀ t : 𝒱.Idx q, Γ(M, 𝒱.inter t)) (s : 𝒰.Idx p) (t : 𝒱.Idx (q + 1)) :
    verF (𝒲 := prodBiCover p₁ p₂ 𝒰 𝒱) (cupFamFun p₁ p₂ a b) s t =
      cupFamFun p₁ p₂ a (dΓ' b) s t := by
  unfold verF cupFamFun dΓ'
  rw [cup_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cup_zsmul_right, map_cup, cup_map_right]

lemma cupFam_tmul' (p q : ℕ) (a : (ofModules πX L).cochain 𝒰 p)
    (b : (ofModules πY M).cochain 𝒱 q) :
    (cupFam hπ hP 𝒰 𝒱 L M p q (a ⊗ₜ b) :
      ∀ (s : 𝒰.Idx p) (t : 𝒱.Idx q),
        Γ(extTensor p₁ p₂ L M, biOpen (prodBiCover p₁ p₂ 𝒰 𝒱) s t)) = cupFamFun p₁ p₂ a b :=
  funext fun s => funext fun t => cupFam_tmul hπ hP 𝒰 𝒱 L M p q a b s t

end Differentials

end Langlands.AlgebraicGeometry.Modules.BiCech
