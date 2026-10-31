import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Sheaves.LocallySurjective
import Langlands.AlgebraicGeometry.Modules.ClosedImmersionHigherDirectImageVanishingProof

/-!
# Sheaves of sections over an open, and their restriction maps

For an open `W` of a scheme `X` and an `𝒪_X`-module `M`, `sheafOn M W` is the
pushforward along `W ⟶ X` of the restriction of `M` to `W`; its sections over `V`
are the sections of `M` over `W ⊓ V`. This file records the unit `M ⟶ sheafOn M W`,
the restriction maps `sheafOn M W ⟶ sheafOn M W'` for `W' ≤ W`, and elementwise
facts about finite biproducts of `𝒪_X`-modules.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

variable {X : Scheme.{u}}

/-- `X.Modules` is abelian, hence has finite biproducts (Mathlib keeps
`Abelian.hasFiniteBiproducts` a local instance). -/
instance : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts

lemma image_preimage_eq (W V : X.Opens) : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = W ⊓ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

variable (M : X.Modules)

/-- The `𝒪_X`-module `V ↦ M(W ⊓ V)`: the pushforward along `W ⟶ X` of the
restriction of `M` to `W`. -/
def sheafOn (W : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.restrictFunctor W.ι).obj M)

lemma sheafOn_obj (W V : X.Opens) : Γ(sheafOn M W, V) = Γ(M, W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) := rfl

/-- The unit `M ⟶ sheafOn M W`, restricting sections from `V` to `W ⊓ V`. -/
def unit (W : X.Opens) : M ⟶ sheafOn M W :=
  (Scheme.Modules.restrictAdjunction W.ι).unit.app M

lemma unit_app (W V : X.Opens) :
    (unit M W).app V = M.presheaf.map (homOfLE (W.ι.image_preimage_le V)).op := rfl

lemma image_preimage_mono {W W' : X.Opens} (h : W' ≤ W) (V : X.Opens) :
    W'.ι ''ᵁ (W'.ι ⁻¹ᵁ V) ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ V) := by
  rw [image_preimage_eq, image_preimage_eq]
  exact inf_le_inf_right V h

lemma image_preimage_mono_right (W : X.Opens) {V V' : X.Opens} (h : V' ≤ V) :
    W.ι ''ᵁ (W.ι ⁻¹ᵁ V') ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ V) := by
  rw [image_preimage_eq, image_preimage_eq]
  exact inf_le_inf_left W h

lemma sheafOn_map (W : X.Opens) {V V' : X.Opens} (i : V' ⟶ V) :
    (sheafOn M W).presheaf.map i.op =
      M.presheaf.map (homOfLE (image_preimage_mono_right W (leOfHom i))).op := rfl

/-- Scalars act on `Γ(sheafOn M W, V)` through the ring map `Γ(X, V) ⟶ Γ(X, W.ι ''ᵁ W.ι ⁻¹ᵁ V)`. -/
lemma smul_eq (W V : X.Opens) (r : Γ(X, V)) (m : Γ(sheafOn M W, V)) :
    r • m = (M.smul ((W.ι.app V ≫ (W.ι.appIso (W.ι ⁻¹ᵁ V)).inv) r)).hom m := rfl

lemma app_appIso_inv_comp_map {W W' : X.Opens} (h : W' ≤ W) (V : X.Opens) :
    (W.ι.app V ≫ (W.ι.appIso (W.ι ⁻¹ᵁ V)).inv) ≫
        X.presheaf.map (homOfLE (image_preimage_mono h V)).op =
      W'.ι.app V ≫ (W'.ι.appIso (W'.ι ⁻¹ᵁ V)).inv := by
  rw [Scheme.Hom.app_appIso_inv, Scheme.Hom.app_appIso_inv]
  exact (X.presheaf.map_comp _ _).symm

lemma map_smul_appIso {W W' : X.Opens} (h : W' ≤ W) (V : X.Opens) (r : Γ(X, V))
    (m : Γ(M, W.ι ''ᵁ (W.ι ⁻¹ᵁ V))) :
    M.presheaf.map (homOfLE (image_preimage_mono h V)).op
        ((W.ι.app V ≫ (W.ι.appIso (W.ι ⁻¹ᵁ V)).inv) r • m) =
      (W'.ι.app V ≫ (W'.ι.appIso (W'.ι ⁻¹ᵁ V)).inv) r •
        M.presheaf.map (homOfLE (image_preimage_mono h V)).op m := by
  rw [Scheme.Modules.map_smul, ← app_appIso_inv_comp_map h V]
  rfl

lemma map_comp_map {W W' : X.Opens} (h : W' ≤ W) {V V' : X.Opens} (i : V' ≤ V) :
    M.presheaf.map (homOfLE (image_preimage_mono_right W i)).op ≫
        M.presheaf.map (homOfLE (image_preimage_mono h V')).op =
      M.presheaf.map (homOfLE (image_preimage_mono h V)).op ≫
        M.presheaf.map (homOfLE (image_preimage_mono_right W' i)).op := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

variable {M} in
/-- The component over `V` of the restriction map `sheafOn M W ⟶ sheafOn M W'`. -/
def resApp {W W' : X.Opens} (h : W' ≤ W) (V : X.Opens) :
    Γ(sheafOn M W, V) ⟶ Γ(sheafOn M W', V) :=
  M.presheaf.map (homOfLE (image_preimage_mono h V)).op

lemma resApp_smul {W W' : X.Opens} (h : W' ≤ W) (V : X.Opens) (r : Γ(X, V))
    (m : Γ(sheafOn M W, V)) : resApp h V (r • m) = r • resApp h V m :=
  map_smul_appIso M h V r m

variable (X) in
/-- The functor `V ↦ W.ι ''ᵁ W.ι ⁻¹ᵁ V` on opens of `X` (whose value is `W ⊓ V`). -/
def interFunctor (W : X.Opens) : X.Opens ⥤ X.Opens :=
  Opens.map W.ι.base ⋙ W.ι.opensFunctor

/-- The inclusion `interFunctor X W' ⟶ interFunctor X W` for `W' ≤ W`. -/
def interFunctorMap {W W' : X.Opens} (h : W' ≤ W) : interFunctor X W' ⟶ interFunctor X W where
  app V := homOfLE (image_preimage_mono h V)

/-- The abelian-presheaf map underlying `res`. -/
def resPresheaf {W W' : X.Opens} (h : W' ≤ W) :
    (sheafOn M W).presheaf ⟶ (sheafOn M W').presheaf :=
  Functor.whiskerRight (NatTrans.op (interFunctorMap h)) M.presheaf

/-- The restriction map `sheafOn M W ⟶ sheafOn M W'` for `W' ≤ W`, restricting sections
from `W ⊓ V` to `W' ⊓ V`. -/
def res {W W' : X.Opens} (h : W' ≤ W) : sheafOn M W ⟶ sheafOn M W' where
  val := PresheafOfModules.homMk (resPresheaf M h) (fun V r m => resApp_smul M h V.unop r m)

lemma res_app {W W' : X.Opens} (h : W' ≤ W) (V : X.Opens) :
    (res M h).app V = M.presheaf.map (homOfLE (image_preimage_mono h V)).op := rfl

lemma res_refl (W : X.Opens) : res M (le_refl W) = 𝟙 _ := by
  ext V : 1
  rw [res_app, Scheme.Modules.Hom.id_app]
  exact M.presheaf.map_id _

lemma res_comp {W W' W'' : X.Opens} (h : W' ≤ W) (h' : W'' ≤ W') :
    res M h ≫ res M h' = res M (h'.trans h) := by
  ext V : 1
  rw [Scheme.Modules.Hom.comp_app, res_app, res_app, res_app]
  exact (M.presheaf.map_comp _ _).symm

lemma unit_res {W W' : X.Opens} (h : W' ≤ W) : unit M W ≫ res M h = unit M W' := by
  ext V : 1
  rw [Scheme.Modules.Hom.comp_app, res_app, unit_app, unit_app]
  exact (M.presheaf.map_comp _ _).symm

section Elementwise

variable {M N : X.Modules}

/-- Evaluation of morphisms `M ⟶ N` at a section `x` of `M` over `V`, as an additive map. -/
def evalApp (V : X.Opens) (x : Γ(M, V)) : (M ⟶ N) →+ Γ(N, V) where
  toFun φ := φ.app V x
  map_zero' := rfl
  map_add' _ _ := rfl

lemma sum_app_apply {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N)) (V : X.Opens) (x : Γ(M, V)) :
    (∑ i ∈ s, f i).app V x = ∑ i ∈ s, (f i).app V x :=
  map_sum (evalApp V x) f s

lemma zsmul_app_apply (n : ℤ) (f : M ⟶ N) (V : X.Opens) (x : Γ(M, V)) :
    (n • f).app V x = n • f.app V x :=
  map_zsmul (evalApp V x) n f

lemma comp_app_apply {K : X.Modules} (f : M ⟶ N) (g : N ⟶ K) (V : X.Opens) (x : Γ(M, V)) :
    (f ≫ g).app V x = g.app V (f.app V x) := rfl

lemma app_injective_of_mono (f : M ⟶ N) [Mono f] (V : X.Opens) :
    Function.Injective (f.app V) := by
  have : Mono f.mapPresheaf := (Scheme.Modules.toPresheaf X).map_mono f
  have : Mono (f.mapPresheaf.app (op V)) := (NatTrans.mono_iff_mono_app _).1 this _
  exact (AddCommGrpCat.mono_iff_injective _).1 this

lemma mono_of_app_injective (f : M ⟶ N) (h : ∀ V, Function.Injective (f.app V)) : Mono f := by
  refine Preadditive.mono_of_cancel_zero _ fun {K} g hg => ?_
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  exact h V (show (g ≫ f).app V x = ((0 : K ⟶ M) ≫ f).app V x by rw [hg, zero_comp])

variable {ι : Type*} [Fintype ι] (G : ι → X.Modules)

lemma biproduct_eq_sum_app (V : X.Opens) (x : Γ(⨁ G, V)) :
    x = ∑ i, (biproduct.ι G i).app V ((biproduct.π G i).app V x) := by
  have h := congr_arg (fun φ : ⨁ G ⟶ ⨁ G => φ.app V x) (IsBilimit.total (biproduct.isBilimit G))
  dsimp only at h
  rw [sum_app_apply] at h
  exact h.symm

lemma biproduct_ext_app {V : X.Opens} {x y : Γ(⨁ G, V)}
    (h : ∀ i, (biproduct.π G i).app V x = (biproduct.π G i).app V y) : x = y := by
  rw [biproduct_eq_sum_app G V x, biproduct_eq_sum_app G V y]
  simp only [h]

lemma biproduct_π_app_sum_ι_app (V : X.Opens) (y : ∀ i, Γ(G i, V)) (j : ι) :
    (biproduct.π G j).app V (∑ i, (biproduct.ι G i).app V (y i)) = y j := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [← comp_app_apply, biproduct.ι_π_self]
    rfl
  · intro i _ hij
    rw [← comp_app_apply, biproduct.ι_π_ne _ hij]
    rfl
  · intro hj
    exact absurd (Finset.mem_univ j) hj

lemma biproduct_exists_app (V : X.Opens) (y : ∀ i, Γ(G i, V)) :
    ∃ x : Γ(⨁ G, V), ∀ i, (biproduct.π G i).app V x = y i :=
  ⟨_, biproduct_π_app_sum_ι_app G V y⟩

end Elementwise

/-- A short complex of `𝒪_X`-modules is exact if every section of the middle term killed by
the second map is, locally, in the image of the first map. -/
lemma exact_of_locally (S : ShortComplex X.Modules)
    (h : ∀ (V : X.Opens) (c : Γ(S.X₂, V)), S.g.app V c = 0 → ∀ x ∈ V,
      ∃ (W : X.Opens) (hW : W ≤ V), x ∈ W ∧
        ∃ b : Γ(S.X₁, W), S.f.app W b = S.X₂.presheaf.map (homOfLE hW).op c) :
    S.Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  apply ClosedImmersionHigherDirectImageVanishing.epi_of_isLocallySurjective
  rw [TopCat.Presheaf.isLocallySurjective_iff]
  intro V z x hx
  have hz : S.g.app V ((kernel.ι S.g).app V z) = 0 := by
    rw [← comp_app_apply, kernel.condition]
    rfl
  obtain ⟨W, hW, hxW, b, hb⟩ := h V _ hz x hx
  refine ⟨W, hW, ⟨b, app_injective_of_mono (kernel.ι S.g) W ?_⟩, hxW⟩
  change (kernel.lift S.g S.f S.zero ≫ kernel.ι S.g).app W b = _
  rw [kernel.lift_ι, hb]
  exact (ConcreteCategory.congr_hom
    (((kernel.ι S.g).mapPresheaf.naturality (homOfLE hW).op)) z).symm

end Langlands.AlgebraicGeometry.Modules.CechResolution
