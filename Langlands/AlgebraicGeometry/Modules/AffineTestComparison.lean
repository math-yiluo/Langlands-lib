import Langlands.AlgebraicGeometry.Modules.AffineTestRealization
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.Modules.TildePullback
import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceOfFLT

/-! # Pullback and tilde comparisons for realizations of affine test systems

For an affine test system `E` on `S` and a morphism `g : Y ⟶ S`, a morphism of affine test
systems `ν : E ⟶ F` over `g` (bijective on every test) induces an isomorphism
`g^* E.toModules ≅ F.toModules`. For an affine test `a : Spec R ⟶ S` this gives the canonical
frame `a^* E.toModules ≅ (E.obj a)^~`, compatible with coefficient extension.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

namespace AffineTestSystem

open CoherentPresheafRealization (AffBelow)
open Langlands.Scheme.Modules ProperFormalCoherentExistenceOfFLT

variable {S Y Z : Scheme.{u}} (E : AffineTestSystem S)

section Transport

variable {R A : CommRingCat.{u}}

/-- Transport of the module of a test along an equality of tests. -/
def transport {a a' : Spec R ⟶ S} (h : a = a') : E.obj a ≃ₗ[R] E.obj a' := by
  subst h
  exact LinearEquiv.refl R (E.obj a)

@[simp]
lemma transport_rfl {a : Spec R ⟶ S} (x : E.obj a) : E.transport rfl x = x :=
  rfl

lemma map_transport {a a' : Spec R ⟶ S} (e : a = a') (f : R ⟶ A) {b : Spec A ⟶ S}
    (h : Spec.map f ≫ a' = b) (h' : Spec.map f ≫ a = b) (x : E.obj a) :
    E.map f h (E.transport e x) = E.map f h' x := by
  subst e
  rfl

lemma transport_map {b b' : Spec A ⟶ S} (e : b = b') (f : R ⟶ A) {a : Spec R ⟶ S}
    (h : Spec.map f ≫ a = b) (h' : Spec.map f ≫ a = b') (x : E.obj a) :
    E.transport e (E.map f h x) = E.map f h' x := by
  subst e
  rfl

lemma transport_transport {a a' a'' : Spec R ⟶ S} (e : a = a') (e' : a' = a'')
    (x : E.obj a) : E.transport e' (E.transport e x) = E.transport (e.trans e') x := by
  subst e e'
  rfl

/-- Coefficient extension along an isomorphism of rings is bijective. -/
lemma map_bijective_of_isIso (f : R ⟶ A) [IsIso f] {a : Spec R ⟶ S} {b : Spec A ⟶ S}
    (h : Spec.map f ≫ a = b) : Function.Bijective (E.map f h) := by
  have h' : Spec.map (inv f) ≫ b = a := by
    rw [← h, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  refine Function.bijective_iff_has_inverse.mpr ⟨E.map (inv f) h', fun x => ?_, fun y => ?_⟩
  · rw [E.map_comp f (inv f) h h' (by rw [IsIso.hom_inv_id, Spec.map_id, Category.id_comp])]
    exact E.map_eq_self _ (IsIso.hom_inv_id f) _ x
  · rw [E.map_comp (inv f) f h' h (by rw [IsIso.inv_hom_id, Spec.map_id, Category.id_comp])]
    exact E.map_eq_self _ (IsIso.inv_hom_id f) _ y

lemma map_map {B : CommRingCat.{u}} (f : R ⟶ A) (f' : A ⟶ B) {a : Spec R ⟶ S}
    {b : Spec A ⟶ S} {c : Spec B ⟶ S} (hab : Spec.map f ≫ a = b) (hbc : Spec.map f' ≫ b = c)
    (x : E.obj a) :
    E.map f' hbc (E.map f hab x) =
      E.map (f ≫ f') (by rw [Spec.map_comp, Category.assoc, hab, hbc]) x :=
  E.map_comp f f' hab hbc _ x

/-- The coefficient-extension identification on `1 ⊗ x` for a given algebra structure is `map`
along its algebra map. -/
lemma ext_one_tmul [inst : Algebra R A] {a : Spec R ⟶ S} {b : Spec A ⟶ S}
    (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) (x : E.obj a) :
    E.ext h (1 ⊗ₜ x) = E.map (CommRingCat.ofHom (algebraMap R A)) h x := by
  rcases inst with @⟨⟨s⟩, φ, hc, hs⟩
  obtain rfl : s = fun r y => φ r * y := funext fun r => funext fun y => hs r y
  rfl

end Transport

section Pullback

/-- The pullback of an affine test system along `g : Y ⟶ S`: the module of a test `c` of `Y`
is the module of the composite test `c ≫ g`. -/
def pullback (g : Y ⟶ S) : AffineTestSystem Y where
  obj c := E.obj (c ≫ g)
  ext h := E.ext (by rw [← h, Category.assoc])
  ext_comp _ _ _ x := E.ext_comp _ _ _ x

lemma pullback_map (g : Y ⟶ S) {R A : CommRingCat.{u}} (f : R ⟶ A) {c : Spec R ⟶ Y}
    {c' : Spec A ⟶ Y} (h : Spec.map f ≫ c = c') (h' : Spec.map f ≫ c ≫ g = c' ≫ g)
    (x : E.obj (c ≫ g)) : (E.pullback g).map f h x = E.map f h' x :=
  rfl

lemma pullback_map' (g : Y ⟶ S) {R A : CommRingCat.{u}} (f : R ⟶ A) {c : Spec R ⟶ Y}
    {c' : Spec A ⟶ Y} (h : Spec.map f ≫ c = c') (x : E.obj (c ≫ g)) :
    (E.pullback g).map f h x = E.map f (by rw [← h, Category.assoc]) x :=
  rfl

end Pullback

/-- A morphism from an affine test system `E` on `S` to an affine test system `F` on `Y` over
`g : Y ⟶ S`: linear maps `E.obj (c ≫ g) → F.obj c` for all tests `c` of `Y`, compatible with
coefficient extension. -/
structure Hom (E : AffineTestSystem S) (F : AffineTestSystem Y) (g : Y ⟶ S) where
  /-- The component at a test `c` of `Y`. -/
  app : ∀ {R : CommRingCat.{u}} (c : Spec R ⟶ Y), E.obj (c ≫ g) →ₗ[R] F.obj c
  /-- Compatibility with coefficient extension. -/
  naturality : ∀ {R A : CommRingCat.{u}} (f : R ⟶ A) {c : Spec R ⟶ Y} {c' : Spec A ⟶ Y}
    (hc : Spec.map f ≫ c = c') (hE : Spec.map f ≫ c ≫ g = c' ≫ g) (x : E.obj (c ≫ g)),
    app c' (E.map f hE x) = F.map f hc (app c x)

namespace Hom

variable {E} {F : AffineTestSystem Y} {G : AffineTestSystem Z} {g : Y ⟶ S} {k : Z ⟶ Y}

lemma ext' {ν ν' : Hom E F g}
    (h : ∀ {R : CommRingCat.{u}} (c : Spec R ⟶ Y) (x : E.obj (c ≫ g)), ν.app c x = ν'.app c x) :
    ν = ν' := by
  obtain ⟨app, nat⟩ := ν
  obtain ⟨app', nat'⟩ := ν'
  have : @app = @app' := by
    funext R c
    exact LinearMap.ext (h c)
  subst this
  rfl

/-- Composition of morphisms of affine test systems, over the composite morphism. -/
def comp (ν : Hom E F g) (μ : Hom F G k) : Hom E G (k ≫ g) where
  app c := μ.app c ∘ₗ ν.app (c ≫ k) ∘ₗ (E.transport (Category.assoc c k g).symm).toLinearMap
  naturality f c c' hc hE x := by
    have hck : Spec.map f ≫ c ≫ k = c' ≫ k := by rw [← hc, Category.assoc]
    have h1 : Spec.map f ≫ c ≫ k ≫ g = (c' ≫ k) ≫ g := by
      rw [← hc]; simp only [Category.assoc]
    have h2 : Spec.map f ≫ (c ≫ k) ≫ g = (c' ≫ k) ≫ g := by
      rw [← hck]; simp only [Category.assoc]
    change μ.app c' (ν.app (c' ≫ k) (E.transport (Category.assoc c' k g).symm (E.map f hE x))) =
      G.map f hc (μ.app c (ν.app (c ≫ k) (E.transport (Category.assoc c k g).symm x)))
    rw [E.transport_map _ f hE h1, ← E.map_transport (Category.assoc c k g).symm f h2 h1,
      ν.naturality f hck h2, μ.naturality f hc hck]

lemma comp_app (ν : Hom E F g) (μ : Hom F G k) {R : CommRingCat.{u}} (c : Spec R ⟶ Z)
    (x : E.obj (c ≫ k ≫ g)) :
    (ν.comp μ).app c x = μ.app c (ν.app (c ≫ k) (E.transport (Category.assoc c k g).symm x)) :=
  rfl

end Hom

/-- The tautological morphism from `E` to its pullback along `g`. -/
def toPullback (g : Y ⟶ S) : Hom E (E.pullback g) g where
  app _ := LinearMap.id
  naturality _ _ _ _ _ _ := rfl

/-- The identification of the pullback of a pullback with the pullback along the composite,
as a morphism over `k`. -/
def pullbackComp (g : Y ⟶ S) (k : Z ⟶ Y) : Hom (E.pullback g) (E.pullback (k ≫ g)) k where
  app c := (E.transport (Category.assoc c k g)).toLinearMap
  naturality f c c' hc hE x := by
    have h₁ : Spec.map f ≫ (c ≫ k) ≫ g = (c' ≫ k) ≫ g := by
      rw [← hE]; simp only [Category.assoc]
    have h₂ : Spec.map f ≫ (c ≫ k) ≫ g = c' ≫ k ≫ g := by
      rw [← hc]; simp only [Category.assoc]
    have h₃ : Spec.map f ≫ c ≫ k ≫ g = c' ≫ k ≫ g := by
      rw [← hc]; simp only [Category.assoc]
    change E.transport (Category.assoc c' k g) (E.map f h₁ x) =
      E.map f h₃ (E.transport (Category.assoc c k g) x)
    rw [E.transport_map _ f h₁ h₂, E.map_transport _ f h₃ h₂]

lemma pullbackComp_app (g : Y ⟶ S) (k : Z ⟶ Y) {R : CommRingCat.{u}} (c : Spec R ⟶ Z)
    (x : E.obj ((c ≫ k) ≫ g)) :
    (E.pullbackComp g k).app c x = E.transport (Category.assoc c k g) x :=
  rfl

lemma toPullback_comp_pullbackComp (g : Y ⟶ S) (k : Z ⟶ Y) :
    (E.toPullback g).comp (E.pullbackComp g k) = E.toPullback (k ≫ g) := by
  refine Hom.ext' fun c x => ?_
  change E.transport (Category.assoc c k g) (E.transport (Category.assoc c k g).symm x) = x
  rw [E.transport_transport]
  rfl

section Comparison

variable {E} {F : AffineTestSystem Y} {g : Y ⟶ S}

/-- Sections of a realization are determined by their images on all affine opens below. -/
lemma toModules_ext {O : S.Opens} {s t : Γ(E.toModules, O)}
    (h : ∀ V : AffBelow O,
      E.sectionsEquiv V.2.1 (E.toModules.presheaf.map (homOfLE V.2.2).op s) =
        E.sectionsEquiv V.2.1 (E.toModules.presheaf.map (homOfLE V.2.2).op t)) : s = t :=
  BasisHomGluing.eq_of_basis (basis_affineOpens S) s t fun W hW hWO =>
    (E.sectionsEquiv hW).injective (h ⟨W, hW, hWO⟩)

variable (ν : Hom E F g)

/-- The comparison on the charts of affine opens `V ≤ g⁻¹ U`: coefficient extension along
`g.appLE U V h` followed by `ν`. -/
def chartMap {U : S.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : V ≤ g ⁻¹ᵁ U) : E.obj hU.fromSpec →ₛₗ[(g.appLE U V h).hom] F.obj hV.fromSpec :=
  (ν.app hV.fromSpec).comp (E.map (g.appLE U V h) (IsAffineOpen.SpecMap_appLE_fromSpec g hU hV h))

lemma chartMap_apply {U : S.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : V ≤ g ⁻¹ᵁ U) (y : E.obj hU.fromSpec) :
    chartMap ν hU hV h y =
      ν.app hV.fromSpec (E.map (g.appLE U V h) (IsAffineOpen.SpecMap_appLE_fromSpec g hU hV h) y) :=
  rfl

lemma res_chartMap {U : S.Opens} (hU : IsAffineOpen U) {V W : Y.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : V ≤ g ⁻¹ᵁ U) (hWV : W ≤ V) (y : E.obj hU.fromSpec) :
    F.res hV hW hWV (chartMap ν hU hV h y) = chartMap ν hU hW (hWV.trans h) y := by
  have hc : Spec.map (Y.presheaf.map (homOfLE hWV).op) ≫ hV.fromSpec = hW.fromSpec :=
    hV.map_fromSpec hW (homOfLE hWV).op
  have hE : Spec.map (Y.presheaf.map (homOfLE hWV).op) ≫ hV.fromSpec ≫ g = hW.fromSpec ≫ g := by
    rw [← Category.assoc, hc]
  have hac : Spec.map (g.appLE U V h ≫ Y.presheaf.map (homOfLE hWV).op) ≫ hU.fromSpec =
      hW.fromSpec ≫ g := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec g hU hV h,
      ← Category.assoc, hc]
  rw [chartMap_apply, chartMap_apply, res, ← ν.naturality _ hc hE, E.map_comp _ _ _ hE hac]
  exact congrArg _ (E.map_congr (Scheme.Hom.appLE_map _ _ _) _ _ y)

lemma chartMap_res {U U' : S.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hUU' : U' ≤ U)
    {V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ g ⁻¹ᵁ U') (y : E.obj hU.fromSpec) :
    chartMap ν hU' hV h (E.res hU hU' hUU' y) =
      chartMap ν hU hV (h.trans (g.preimage_mono hUU')) y := by
  rw [chartMap_apply, chartMap_apply, res, E.map_comp]
  · exact congrArg _ (E.map_congr (Scheme.Hom.map_appLE _ _ _) _ _ y)
  · rw [Spec.map_comp, Category.assoc, hU.map_fromSpec hU' (homOfLE hUU').op,
      IsAffineOpen.SpecMap_appLE_fromSpec]

/-- The compatible family over the affine opens of `g⁻¹ U` given by `chartMap`. -/
def family {U : S.Opens} (hU : IsAffineOpen U) (y : E.obj hU.fromSpec) : F.compat (g ⁻¹ᵁ U) :=
  ⟨fun V => chartMap ν hU V.2.1 V.2.2 y, fun V W h => res_chartMap ν hU V.2.1 W.2.1 V.2.2 h y⟩

lemma sectionsEquiv_res_ofFamily_family {U : S.Opens} (hU : IsAffineOpen U)
    (y : E.obj hU.fromSpec) {V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ g ⁻¹ᵁ U) :
    F.sectionsEquiv hV (F.toModules.presheaf.map (homOfLE h).op (F.ofFamily (family ν hU y))) =
      chartMap ν hU hV h y :=
  F.sectionsEquiv_res_ofFamily (family ν hU y) ⟨V, hV, h⟩

end Comparison

section Gluing

variable {E} {F : AffineTestSystem Y} {g : Y ⟶ S} (ν : Hom E F g)

lemma presheaf_map_map {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens} (h : V ≤ U)
    (h' : W ≤ V) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h').op (M.presheaf.map (homOfLE h).op s) =
      M.presheaf.map (homOfLE (h'.trans h)).op s := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

/-- The section of `F.toModules` over `g⁻¹ U` attached to a section of `E.toModules` over an
affine open `U`. -/
def thetaFun {U : S.Opens} (hU : IsAffineOpen U) (m : Γ(E.toModules, U)) :
    Γ(F.toModules, g ⁻¹ᵁ U) :=
  F.ofFamily (family ν hU (E.sectionsEquiv hU m))

lemma sectionsEquiv_res_thetaFun {U : S.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : V ≤ g ⁻¹ᵁ U) (m : Γ(E.toModules, U)) :
    F.sectionsEquiv hV (F.toModules.presheaf.map (homOfLE h).op (thetaFun ν hU m)) =
      chartMap ν hU hV h (E.sectionsEquiv hU m) :=
  sectionsEquiv_res_ofFamily_family ν hU _ hV h

lemma thetaFun_add {U : S.Opens} (hU : IsAffineOpen U) (m m' : Γ(E.toModules, U)) :
    thetaFun ν hU (m + m') = thetaFun ν hU m + thetaFun ν hU m' := by
  refine toModules_ext fun V => ?_
  rw [map_add, map_add, sectionsEquiv_res_thetaFun, sectionsEquiv_res_thetaFun,
    sectionsEquiv_res_thetaFun, map_add, map_add]

lemma thetaFun_smul {U : S.Opens} (hU : IsAffineOpen U) (r : Γ(S, U)) (m : Γ(E.toModules, U)) :
    thetaFun ν hU (r • m) = g.app U r • thetaFun ν hU m := by
  refine toModules_ext fun V => ?_
  rw [Scheme.Modules.map_smul, LinearEquiv.map_smul, sectionsEquiv_res_thetaFun,
    sectionsEquiv_res_thetaFun, LinearEquiv.map_smul, LinearMap.map_smulₛₗ]
  rfl

/-- The adjoint of the comparison on an affine open `U` of `S`. -/
def theta (U : S.Opens) (hU : U ∈ S.affineOpens) :
    Γ(E.toModules, U) →ₗ[Γ(S, U)] Γ((Scheme.Modules.pushforward g).obj F.toModules, U) where
  toFun m := thetaFun ν hU m
  map_add' := thetaFun_add ν hU
  map_smul' r m := thetaFun_smul ν hU r m

lemma theta_map (U U' : S.Opens) (hU : U ∈ S.affineOpens) (hU' : U' ∈ S.affineOpens)
    (h : U' ≤ U) (m : Γ(E.toModules, U)) :
    ((Scheme.Modules.pushforward g).obj F.toModules).presheaf.map (homOfLE h).op
        (theta ν U hU m) =
      theta ν U' hU' (E.toModules.presheaf.map (homOfLE h).op m) := by
  change F.toModules.presheaf.map (homOfLE (g.preimage_mono h)).op (thetaFun ν hU m) =
    thetaFun ν hU' (E.toModules.presheaf.map (homOfLE h).op m)
  refine toModules_ext fun V => ?_
  rw [presheaf_map_map, sectionsEquiv_res_thetaFun, sectionsEquiv_res_thetaFun,
    sectionsEquiv_naturality, chartMap_res]

/-- The morphism `E.toModules ⟶ g_* F.toModules` glued from `theta` on affine opens. -/
def psi : E.toModules ⟶ (Scheme.Modules.pushforward g).obj F.toModules :=
  BasisHomGluing.hom (basis_affineOpens S) (theta ν) (theta_map ν)

/-- The comparison morphism `g^* E.toModules ⟶ F.toModules` induced by `ν`. -/
def comparison : (Scheme.Modules.pullback g).obj E.toModules ⟶ F.toModules :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm (psi ν)

lemma comparison_app_sectionPullback {U : S.Opens} (hU : IsAffineOpen U) (m : Γ(E.toModules, U)) :
    (comparison ν).app (g ⁻¹ᵁ U) (sectionPullback g E.toModules U m) = thetaFun ν hU m := by
  rw [← homEquiv_app_apply, comparison, Equiv.apply_symm_apply, psi,
    BasisHomGluing.hom_app_basis _ _ _ U hU]
  rfl

/-- The comparison on a pulled-back section over an affine open `V ≤ g⁻¹ U`, read in the module
of the chart of `V`. -/
lemma sectionsEquiv_comparison_app {U : S.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : V ≤ g ⁻¹ᵁ U) (m : Γ(E.toModules, U)) :
    F.sectionsEquiv hV ((comparison ν).app V (sectionPullbackLE g E.toModules h m)) =
      chartMap ν hU hV h (E.sectionsEquiv hU m) := by
  rw [sectionPullbackLE, ← OpenCoverHomGluing.hom_map_app, comparison_app_sectionPullback ν hU,
    sectionsEquiv_res_thetaFun]

variable {ν}

lemma comparison_app_bijective
    (hν : ∀ {R : CommRingCat.{u}} (c : Spec R ⟶ Y), Function.Bijective (ν.app c))
    {U : S.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ g ⁻¹ᵁ U) :
    Function.Bijective ((comparison ν).app V) := by
  let := (g.appLE U V h).hom.toAlgebra
  have hT := pullbackTensorMap_bijective g E.toModules h hV hU
  let e₁ := extendScalarsAlgebraEquiv Γ(S, U) Γ(Y, V) (ModuleCat.of Γ(S, U) Γ(E.toModules, U))
  let e₂ := (E.sectionsEquiv hU).baseChange Γ(S, U) Γ(Y, V) Γ(E.toModules, U) (E.obj hU.fromSpec)
  let e₃ := E.ext (A := Γ(Y, V)) (IsAffineOpen.SpecMap_appLE_fromSpec g hU hV h)
  have key : ∀ z, F.sectionsEquiv hV ((comparison ν).app V (pullbackTensorMap g E.toModules h z)) =
      ν.app hV.fromSpec (e₃ (e₂ (e₁ z))) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s m =>
      rw [pullbackTensorMap_tmul, Scheme.Modules.Hom.app_smul, LinearEquiv.map_smul,
        sectionsEquiv_comparison_app ν hU hV h, chartMap_apply]
      change _ = ν.app hV.fromSpec (E.ext _ (s ⊗ₜ E.sectionsEquiv hU m))
      rw [E.ext_tmul_toAlgebra (g.appLE U V h), LinearMap.map_smul]
  have hΦ : Function.Bijective (fun z =>
      F.sectionsEquiv hV ((comparison ν).app V (pullbackTensorMap g E.toModules h z))) := by
    rw [funext key]
    exact (hν _).comp (e₃.bijective.comp (e₂.bijective.comp e₁.bijective))
  have h2 : Function.Bijective (F.sectionsEquiv hV ∘ (comparison ν).app V) :=
    (Function.Bijective.of_comp_iff _ hT).mp hΦ
  exact (Function.Bijective.of_comp_iff' (F.sectionsEquiv hV).bijective _).mp h2

/-- The comparison is an isomorphism when `ν` is bijective on every test. -/
theorem isIso_comparison
    (hν : ∀ {R : CommRingCat.{u}} (c : Spec R ⟶ Y), Function.Bijective (ν.app c)) :
    IsIso (comparison ν) := by
  refine isIso_of_bijective_of_basis
    (P := fun V => IsAffineOpen V ∧ ∃ U, IsAffineOpen U ∧ V ≤ g ⁻¹ᵁ U) ?_ _ ?_
  · intro y W hy
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := g.base y) (U := ⊤) trivial
    obtain ⟨V, hV, hyV, hVW⟩ :=
      exists_isAffineOpen_mem_and_subset (x := y) (U := W ⊓ g ⁻¹ᵁ U) ⟨hy, hyU⟩
    exact ⟨V, ⟨hV, U, hU, hVW.trans inf_le_right⟩, hyV, hVW.trans inf_le_left⟩
  · rintro V ⟨hV, U, hU, h⟩
    exact comparison_app_bijective hν hU hV h

end Gluing

section Composition

/-- Morphisms out of a pullback agree if, around every point of the inverse image of every affine
open `U`, they agree on the restricted pulled-back sections of sections over `U`. -/
lemma pullback_hom_ext_local {X : Scheme.{u}} (h : X ⟶ S) {M : S.Modules} {N : X.Modules}
    {f₁ f₂ : (Scheme.Modules.pullback h).obj M ⟶ N}
    (H : ∀ U : S.Opens, IsAffineOpen U → ∀ x ∈ h ⁻¹ᵁ U, ∃ W : X.Opens, x ∈ W ∧
      ∃ hle : W ≤ h ⁻¹ᵁ U, ∀ m : Γ(M, U),
        f₁.app W (sectionPullbackLE h M hle m) = f₂.app W (sectionPullbackLE h M hle m)) :
    f₁ = f₂ := by
  refine pullback_hom_ext_of_basis h (basis_affineOpens S) f₁ f₂ fun U hU m => ?_
  refine BasisHomGluing.eq_of_basis (P := fun W => ∀ hle : W ≤ h ⁻¹ᵁ U,
      f₁.app W (sectionPullbackLE h M hle m) = f₂.app W (sectionPullbackLE h M hle m)) ?_ _ _ ?_
  · intro x O hx
    by_cases hxU : x ∈ h ⁻¹ᵁ U
    · obtain ⟨W, hxW, hle, hW⟩ := H U hU x hxU
      refine ⟨W ⊓ O, fun hle' => ?_, ⟨hxW, hx⟩, inf_le_right⟩
      rw [← map_sectionPullbackLE h M hle (inf_le_left : W ⊓ O ≤ W),
        ← OpenCoverHomGluing.hom_map_app, ← OpenCoverHomGluing.hom_map_app, hW]
    · exact ⟨O, fun hO => absurd (hO hx) hxU, hx, le_rfl⟩
  · intro W hW hWO
    rw [OpenCoverHomGluing.hom_map_app, OpenCoverHomGluing.hom_map_app]
    exact hW hWO

variable {E} {F : AffineTestSystem Y} {G : AffineTestSystem Z} {g : Y ⟶ S} {k : Z ⟶ Y}

lemma chartMap_comp (ν : Hom E F g) (μ : Hom F G k) {U : S.Opens} (hU : IsAffineOpen U)
    {V : Y.Opens} (hV : IsAffineOpen V) {W : Z.Opens} (hW : IsAffineOpen W) (hVU : V ≤ g ⁻¹ᵁ U)
    (hWV : W ≤ k ⁻¹ᵁ V) (hWU : W ≤ (k ≫ g) ⁻¹ᵁ U) (y : E.obj hU.fromSpec) :
    chartMap (ν.comp μ) hU hW hWU y = chartMap μ hV hW hWV (chartMap ν hU hV hVU y) := by
  have hc : Spec.map (k.appLE V W hWV) ≫ hV.fromSpec = hW.fromSpec ≫ k :=
    IsAffineOpen.SpecMap_appLE_fromSpec k hV hW hWV
  have hE : Spec.map (k.appLE V W hWV) ≫ hV.fromSpec ≫ g = (hW.fromSpec ≫ k) ≫ g := by
    rw [← Category.assoc, hc]
  have hac : Spec.map (g.appLE U V hVU ≫ k.appLE V W hWV) ≫ hU.fromSpec =
      (hW.fromSpec ≫ k) ≫ g := by
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec g hU hV hVU,
      ← Category.assoc, hc]
  have h' : Spec.map ((k ≫ g).appLE U W hWU) ≫ hU.fromSpec = (hW.fromSpec ≫ k) ≫ g := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec (k ≫ g) hU hW hWU, Category.assoc]
  rw [chartMap_apply, chartMap_apply, chartMap_apply, ← ν.naturality _ hc hE,
    E.map_comp _ _ _ hE hac, Hom.comp_app, E.transport_map _ _ _ h']
  exact congrArg _ (congrArg _
    (E.map_congr (Scheme.Hom.appLE_comp_appLE k g U V W hVU hWV).symm _ _ y))

/-- The comparison of a composite is the composite of the comparisons. -/
theorem comparison_comp (ν : Hom E F g) (μ : Hom F G k) :
    comparison (ν.comp μ) =
      (Scheme.Modules.pullbackComp k g).inv.app E.toModules ≫
        (Scheme.Modules.pullback k).map (comparison ν) ≫ comparison μ := by
  refine pullback_hom_ext_local (k ≫ g) fun U hU z hz => ?_
  obtain ⟨V, hV, hzV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (x := k.base z) (U := g ⁻¹ᵁ U) hz
  obtain ⟨W, hW, hzW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := k ⁻¹ᵁ V) hzV
  have hWV' : W ≤ k ⁻¹ᵁ V := hWV
  have hVU' : V ≤ g ⁻¹ᵁ U := hVU
  have hWU : W ≤ (k ≫ g) ⁻¹ᵁ U := fun x hx => hVU' (hWV' hx)
  refine ⟨W, hzW, hWU, fun m => (G.sectionsEquiv hW).injective ?_⟩
  rw [sectionsEquiv_comparison_app _ hU hW, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    pullbackComp_inv_sectionPullbackLE k g E.toModules hVU' hWV' hWU]
  erw [pullback_map_sectionPullbackLE k (comparison ν) hWV' (sectionPullbackLE g E.toModules hVU' m)]
  rw [sectionsEquiv_comparison_app μ hV hW hWV',
    sectionsEquiv_comparison_app ν hU hV hVU', chartMap_comp ν μ hU hV hW hVU' hWV' hWU]

end Composition

section Tilde

variable {R : CommRingCat.{u}} (a : Spec R ⟶ S)

lemma specMap_ΓSpecIso_inv_comp :
    Spec.map (Scheme.ΓSpecIso R).inv ≫ a = (isAffineOpen_top (Spec R)).fromSpec ≫ a := by
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

/-- The module of the test `a` as the global sections of the realization of the pullback
system on `Spec R`. -/
def topLinear : E.obj a →ₗ[R] (moduleSpecΓFunctor (R := R)).obj (E.pullback a).toModules where
  toFun x := ((E.pullback a).sectionsEquiv (isAffineOpen_top (Spec R))).symm
    (E.map (Scheme.ΓSpecIso R).inv (specMap_ΓSpecIso_inv_comp a) x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    have h1 := LinearMap.map_smulₛₗ (E.map (Scheme.ΓSpecIso R).inv (specMap_ΓSpecIso_inv_comp a)) r x
    have h2 := ((E.pullback a).sectionsEquiv (isAffineOpen_top (Spec R))).symm.map_smul
      ((Scheme.ΓSpecIso R).inv.hom r)
      (E.map (Scheme.ΓSpecIso R).inv (specMap_ΓSpecIso_inv_comp a) x)
    rw [RingHom.id_apply]
    exact ((congrArg ((E.pullback a).sectionsEquiv (isAffineOpen_top (Spec R))).symm h1).trans
      h2).trans (moduleSpecΓFunctor_smul (E.pullback a).toModules r _).symm

lemma topLinear_bijective : Function.Bijective (E.topLinear a) :=
  ((E.pullback a).sectionsEquiv _).symm.bijective.comp (E.map_bijective_of_isIso _ _)

lemma sectionsEquiv_topLinear (x : E.obj a) :
    (E.pullback a).sectionsEquiv (isAffineOpen_top (Spec R)) (E.topLinear a x) =
      E.map (Scheme.ΓSpecIso R).inv (specMap_ΓSpecIso_inv_comp a) x :=
  LinearEquiv.apply_symm_apply _ _

/-- `topLinear` as a morphism of modules. -/
def topHom : E.obj a ⟶ (moduleSpecΓFunctor (R := R)).obj (E.pullback a).toModules :=
  ModuleCat.ofHom (X := E.obj a) (Y := (moduleSpecΓFunctor (R := R)).obj (E.pullback a).toModules)
    (E.topLinear a)

/-- The comparison `(E.obj a)^~ ⟶ (E.pullback a).toModules` on `Spec R`, adjoint to
`topLinear`. -/
def tildeComparison : tilde (E.obj a) ⟶ (E.pullback a).toModules :=
  ((tilde.adjunction (R := R)).homEquiv _ _).symm (topHom E a)

instance isIso_tildeComparison : IsIso (E.tildeComparison a) := by
  rw [tildeComparison, Adjunction.homEquiv_counit]
  have : IsIso (topHom E a) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (E.topLinear_bijective a)
  have h2 : IsIso ((tilde.adjunction (R := R)).counit.app (E.pullback a).toModules) := by
    change IsIso (Scheme.Modules.fromTildeΓ (E.pullback a).toModules)
    infer_instance
  exact IsIso.comp_isIso

lemma tildeComparison_app_toOpen (x : E.obj a) :
    (E.tildeComparison a).app ⊤ (tilde.toOpen (E.obj a) ⊤ x) = E.topLinear a x := by
  have h := congrArg (fun φ => φ x)
    (((tilde.adjunction (R := R)).homEquiv _ _).apply_symm_apply (topHom E a))
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- The canonical frame `a^* E.toModules ≅ (E.obj a)^~` attached to an affine test
`a : Spec R ⟶ S`. -/
def frame : (Scheme.Modules.pullback a).obj E.toModules ≅ tilde (E.obj a) :=
  haveI := isIso_comparison (ν := E.toPullback a) (fun _ => Function.bijective_id)
  asIso (comparison (E.toPullback a)) ≪≫ (asIso (E.tildeComparison a)).symm

lemma frame_hom_tildeComparison :
    (E.frame a).hom ≫ E.tildeComparison a = comparison (E.toPullback a) := by
  simp [frame]

end Tilde

section Coherence

variable {R A : CommRingCat.{u}} [Algebra R A] (a : Spec R ⟶ S)

/-- The coefficient-extension identification as a morphism of modules over `A`. -/
def extHom {b : Spec A ⟶ S} (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) :
    ModuleCat.of A (A ⊗[R] E.obj a) ⟶ E.obj b :=
  ConcreteCategory.ofHom (C := ModuleCat A) (X := ModuleCat.of A (A ⊗[R] E.obj a)) (Y := E.obj b)
    (E.ext h).toLinearMap

lemma extHom_apply {b : Spec A ⟶ S} (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b)
    (z : A ⊗[R] E.obj a) : E.extHom a h z = E.ext h z :=
  rfl

lemma tildeComparison_app_toOpen_res {b : Spec A ⟶ S} {O : (Spec A).Opens} (x : E.obj b) :
    (E.tildeComparison b).app O (tilde.toOpen (E.obj b) O x) =
      (E.pullback b).toModules.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op (E.topLinear b x) := by
  rw [← tildeComparison_app_toOpen, OpenCoverHomGluing.hom_map_app]
  rfl

lemma ringHom_top_eq {V : (Spec A).Opens}
    (hV : V ≤ Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤) :
    (Scheme.ΓSpecIso R).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R A))).appLE ⊤ V hV =
      CommRingCat.ofHom (algebraMap R A) ≫ (Scheme.ΓSpecIso A).inv ≫
        (Spec A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
  have hn := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R A))
  erw [reassoc_of% hn]
  rfl

lemma tildeSquare_left (m : E.obj a) :
    (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A))
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map (E.tildeComparison a) ≫
        comparison (E.pullbackComp a (Spec.map (CommRingCat.ofHom (algebraMap R A)))))).app ⊤ (tilde.toOpen (E.obj a) ⊤ m) =
      thetaFun (E.pullbackComp a (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (isAffineOpen_top (Spec R)) (E.topLinear a m) := by
  rw [tildePullbackAdjoint, Adjunction.homEquiv_naturality_left, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, tildeComparison_app_toOpen, homEquiv_app_apply,
    comparison_app_sectionPullback]

lemma tildeSquare_right (m : E.obj a) :
    (tildePullbackAdjoint (CommRingCat.ofHom (algebraMap R A))
      ((tildePullbackAlgebraIso R A (E.obj a)).hom ≫
        tilde.map (E.extHom a rfl) ≫ E.tildeComparison (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a))).app ⊤
        (tilde.toOpen (E.obj a) ⊤ m) =
      (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a)).toModules.presheaf.map (homOfLE (le_top : Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤ ≤ ⊤)).op
        (E.topLinear (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a) (E.ext (rfl : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = _) (1 ⊗ₜ m))) := by
  have h1 := tildePullbackAlgebraIso_adjoint_toOpen R A (E.obj a) ⊤ m
  have h2 : ((tilde.map (E.extHom a rfl) ≫ E.tildeComparison (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a)).app (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤))
      (tilde.toOpen (ModuleCat.of A (A ⊗[R] E.obj a)) (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤) (1 ⊗ₜ m)) =
      (E.tildeComparison (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a)).app (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤)
        (tilde.toOpen (E.obj (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a)) (Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤) (E.ext (rfl : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = _) (1 ⊗ₜ m))) := by
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    exact congrArg _ (ConcreteCategory.congr_hom (tilde.toOpen_map_app (E.extHom a rfl) _) _)
  rw [tildePullbackAdjoint, Adjunction.homEquiv_naturality_right, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, ← tildeComparison_app_toOpen_res]
  exact (congrArg (((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
    (tilde.map (E.extHom a rfl) ≫ E.tildeComparison (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a))).app ⊤) h1).trans h2

lemma tildeSquare_sections (m : E.obj a) :
    thetaFun (E.pullbackComp a (Spec.map (CommRingCat.ofHom (algebraMap R A)))) (isAffineOpen_top (Spec R)) (E.topLinear a m) =
      (E.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a)).toModules.presheaf.map (homOfLE (le_top : Spec.map (CommRingCat.ofHom (algebraMap R A)) ⁻¹ᵁ ⊤ ≤ ⊤)).op
        (E.topLinear (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a) (E.ext (rfl : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = _) (1 ⊗ₜ m))) := by
  have hz : E.ext (rfl : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = _) (1 ⊗ₜ m) =
      E.map (CommRingCat.ofHom (algebraMap R A)) rfl m :=
    E.ext_one_tmul rfl m
  rw [hz]
  refine toModules_ext fun V => ?_
  rw [sectionsEquiv_res_thetaFun, presheaf_map_map, sectionsEquiv_naturality _
    (isAffineOpen_top (Spec A)) V.2.1, sectionsEquiv_topLinear, sectionsEquiv_topLinear,
    chartMap_apply, pullbackComp_app, res, pullback_map', pullback_map', E.map_map, E.map_map,
    E.map_map, E.transport_map _ _ _ (by
    rw [Spec.map_comp, Category.assoc, specMap_ΓSpecIso_inv_comp, ← Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec (Spec.map (CommRingCat.ofHom (algebraMap R A))) (isAffineOpen_top (Spec R)) V.2.1 V.2.2,
      Category.assoc])]
  exact E.map_congr (by rw [ringHom_top_eq]; rfl) _ _ m

/-- The comparison with the tilde sheaf commutes with coefficient extension: pulling back the
comparison for `a` along `p : Spec A ⟶ Spec R` corresponds, under `tildePullbackAlgebraIso` and
the identification `A ⊗[R] E.obj a ≃ E.obj (p ≫ a)`, to the comparison for `p ≫ a`. -/
theorem pullback_tildeComparison_comp :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map (E.tildeComparison a) ≫
      comparison (E.pullbackComp a (Spec.map (CommRingCat.ofHom (algebraMap R A)))) =
    (tildePullbackAlgebraIso R A (E.obj a)).hom ≫ tilde.map (E.extHom a rfl) ≫
      E.tildeComparison (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a) := by
  apply tildePullback_hom_ext (CommRingCat.ofHom (algebraMap R A))
  intro m
  rw [tildeSquare_left, tildeSquare_right]
  exact E.tildeSquare_sections a m

/-- **Coherence of the frames.** For an `R`-algebra `A` and tests `a : Spec R ⟶ S`,
`b = Spec A ⟶ Spec R ⟶ S`, the frame for `b` is the pullback of the frame for `a`, followed by
`tildePullbackAlgebraIso` and the coefficient-extension identification `A ⊗[R] E.obj a ≃ E.obj b`,
after the canonical identification `b^* = (Spec A ⟶ Spec R)^* a^*`. -/
theorem frame_hom_eq {b : Spec A ⟶ S}
    (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) :
    (E.frame b).hom =
      ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap R A))) a).app
          E.toModules ≪≫ (Scheme.Modules.pullbackCongr h).app E.toModules).inv ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
          (E.frame a).hom ≫
          (tildePullbackAlgebraIso R A (E.obj a)).hom ≫ tilde.map (E.extHom a h) := by
  subst h
  have hA := comparison_comp (E.toPullback a)
    (E.pullbackComp a (Spec.map (CommRingCat.ofHom (algebraMap R A))))
  rw [toPullback_comp_pullbackComp] at hA
  have hB := E.pullback_tildeComparison_comp (A := A) a
  rw [← cancel_mono (E.tildeComparison _), frame_hom_tildeComparison, hA]
  simp only [Category.assoc]
  rw [← hB, ← Functor.map_comp_assoc, frame_hom_tildeComparison]
  simp [Scheme.Modules.pullbackCongr]

end Coherence

end AffineTestSystem

end Langlands.AlgebraicGeometry.Modules
