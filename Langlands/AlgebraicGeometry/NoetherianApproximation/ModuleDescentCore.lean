import Langlands.AlgebraicGeometry.Modules.CoherentClosure
import Langlands.AlgebraicGeometry.Modules.CechResolution.CechTermDirectImageProof
import Langlands.AlgebraicGeometry.Modules.PullbackAffineSections
import Langlands.AlgebraicGeometry.Modules.FinitePresentationDescent
import Langlands.AlgebraicGeometry.Modules.DirectImageAffineCriterion
import Langlands.AlgebraicGeometry.Modules.BasicOpenHomGluing
import Langlands.AlgebraicGeometry.Modules.FinitePresentationSections
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-! # A finitely presented submodule sheaf of an affine direct image -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore

open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.AffineVanishing

variable {Y : Scheme.{u}}

section Chart

variable (F : Y.Modules) {V : Y.Opens} (hV : IsAffineOpen V)

/-- Sections over an affine open, viewed as global sections of the restriction to its
spectrum. -/
def chart : Γ(F, V) →ₗ[Γ(Y, V)] (moduleSpecΓFunctor (R := Γ(Y, V))).obj
    (F.restrict hV.fromSpec) where
  toFun s := F.presheaf.map (homOfLE (image_fromSpec_le hV ⊤)).op s
  map_add' s t := map_add _ s t
  map_smul' r s := by
    have e1 : F.presheaf.map (homOfLE (image_fromSpec_le hV ⊤)).op (r • s) =
        rres (image_fromSpec_le hV ⊤) r • F.presheaf.map (homOfLE (image_fromSpec_le hV ⊤)).op s :=
      Scheme.Modules.map_smul F (homOfLE (image_fromSpec_le hV ⊤)) r s
    have e2 := Langlands.Scheme.Modules.moduleSpecΓFunctor_smul (F.restrict hV.fromSpec) r
      (F.presheaf.map (homOfLE (image_fromSpec_le hV ⊤)).op s)
    have h := appIso_inv_map_ΓSpecIso_inv hV ⊤ r
    have h1 : (Spec Γ(Y, V)).presheaf.map (⊤ : (Spec Γ(Y, V)).Opens).leTop.op = 𝟙 _ := by
      have : (⊤ : (Spec Γ(Y, V)).Opens).leTop.op = 𝟙 _ := Subsingleton.elim _ _
      rw [this, CategoryTheory.Functor.map_id]
    rw [h1, CategoryTheory.id_apply] at h
    refine e1.trans (Eq.trans ?_ e2.symm)
    change _ = ((hV.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(Y, V)).inv r) •
      (F.presheaf.map (homOfLE (image_fromSpec_le hV ⊤)).op s : Γ(F, hV.fromSpec ''ᵁ ⊤)))
    rw [h]

lemma chart_bijective : Function.Bijective (chart F hV) :=
  Langlands.Scheme.Modules.bijective_map_of_eq F (image_fromSpec_top hV).symm _

end Chart

section Quotient

variable {R : CommRingCat.{u}} (A : (Spec R).Modules) [A.IsQuasicoherent]

lemma inv_fromTildeΓ_app_top (x : (moduleSpecΓFunctor (R := R)).obj A) :
    (inv A.fromTildeΓ).app ⊤ x = tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj A) ⊤ x := by
  have h := ConcreteCategory.congr_hom (Scheme.Modules.toOpen_fromTildeΓ_app A ⊤) x
  have h1 : (homOfLE le_top : (⊤ : (Spec R).Opens) ⟶ ⊤).op = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id] at h
  have h2 : A.fromTildeΓ.app ⊤ (tilde.toOpen ((moduleSpecΓFunctor (R := R)).obj A) ⊤ x) = x := by
    erw [ConcreteCategory.comp_apply] at h
    exact h
  have h3 : ∀ y, (inv A.fromTildeΓ).app ⊤ (A.fromTildeΓ.app ⊤ y) = y := by
    intro y
    change (A.fromTildeΓ ≫ inv A.fromTildeΓ).app ⊤ y = y
    rw [IsIso.hom_inv_id]
    rfl
  conv_lhs => rw [← h2]
  exact h3 _

variable (Q : Submodule R ((moduleSpecΓFunctor (R := R)).obj A))

/-- The associated sheaf of the quotient of the global sections by `Q`. -/
abbrev quotientSheaf : (Spec R).Modules :=
  tilde (ModuleCat.of R (((moduleSpecΓFunctor (R := R)).obj A) ⧸ Q))

/-- The quotient map of global sections. -/
def quotientHom : ModuleCat.of R ((moduleSpecΓFunctor (R := R)).obj A) ⟶
    ModuleCat.of R (((moduleSpecΓFunctor (R := R)).obj A) ⧸ Q) :=
  ModuleCat.ofHom Q.mkQ

/-- The tilde–sections counit, with its source written through `moduleSpecΓFunctor`. -/
def fromTildeΓ' : tilde (ModuleCat.of R ((moduleSpecΓFunctor (R := R)).obj A)) ⟶ A :=
  A.fromTildeΓ

instance : IsIso (fromTildeΓ' A) := inferInstanceAs (IsIso A.fromTildeΓ)

/-- The map from a quasi-coherent sheaf on a spectrum to the sheaf associated to the quotient
of its global sections by `Q`. -/
def quotientMap : A ⟶ quotientSheaf A Q :=
  inv (fromTildeΓ' A) ≫ tilde.map (quotientHom A Q)

lemma quotientMap_app_top (x : (moduleSpecΓFunctor (R := R)).obj A) :
    (quotientMap A Q).app ⊤ x =
      tilde.toOpen (ModuleCat.of R (((moduleSpecΓFunctor (R := R)).obj A) ⧸ Q)) ⊤ (Q.mkQ x) := by
  rw [quotientMap, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [inv_fromTildeΓ_app_top]
  have := ConcreteCategory.congr_hom (tilde.toOpen_map_app (quotientHom A Q) ⊤) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  exact this

lemma quotientMap_app_top_eq_zero_iff (x : (moduleSpecΓFunctor (R := R)).obj A) :
    (quotientMap A Q).app ⊤ x = 0 ↔ x ∈ Q := by
  rw [quotientMap_app_top]
  have hinj : Function.Injective
      (tilde.toOpen (ModuleCat.of R (((moduleSpecΓFunctor (R := R)).obj A) ⧸ Q)) ⊤) :=
    (ConcreteCategory.bijective_of_isIso _).1
  constructor
  · intro h
    have : Q.mkQ x = 0 := hinj (h.trans (map_zero _).symm)
    simpa using this
  · intro h
    have : Q.mkQ x = 0 := by simpa using h
    rw [this, map_zero]

end Quotient

section Restriction

variable {Z : Scheme.{u}}

lemma app_map {A B : Z.Modules} (φ : A ⟶ B) {U W : Z.Opens} (h : U ≤ W) (x : Γ(A, W)) :
    φ.app U (A.presheaf.map (homOfLE h).op x) = B.presheaf.map (homOfLE h).op (φ.app W x) := by
  have := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
  exact this

lemma map_map (A : Z.Modules) {U W O : Z.Opens} (h₁ : U ≤ W) (h₂ : W ≤ O) (x : Γ(A, O)) :
    A.presheaf.map (homOfLE h₁).op (A.presheaf.map (homOfLE h₂).op x) =
      A.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

lemma map_eq_zero_of_eq (A : Z.Modules) {U W : Z.Opens} (h : W = U) (hle : U ≤ W)
    {x : Γ(A, W)} : A.presheaf.map (homOfLE hle).op x = 0 ↔ x = 0 := by
  have hb := Langlands.Scheme.Modules.bijective_map_of_eq A h hle
  constructor
  · intro hx
    exact hb.1 (hx.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

lemma sum_app {A B : Z.Modules} {κ : Type*} (s : Finset κ) (φ : κ → (A ⟶ B)) (W : Z.Opens)
    (x : Γ(A, W)) : (∑ j ∈ s, φ j).app W x = ∑ j ∈ s, (φ j).app W x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    erw [AddCommGrpCat.hom_add_apply]
    rw [ih]

lemma biproduct_app_eq_zero {κ : Type u} [Fintype κ] {B : κ → Z.Modules} {W : Z.Opens}
    (z : Γ(⨁ B, W)) (hz : ∀ j, (biproduct.π B j).app W z = 0) : z = 0 := by
  classical
  have h : (∑ j, biproduct.π B j ≫ biproduct.ι B j).app W z = z := by
    rw [show (∑ j, biproduct.π B j ≫ biproduct.ι B j) = 𝟙 _ from
      IsBilimit.total (biproduct.isBilimit B)]
    rfl
  rw [← h, sum_app]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, hz j, map_zero]

/-- Finite direct sums of quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_biproduct {κ : Type u} [Fintype κ] (B : κ → Z.Modules)
    [∀ j, (B j).IsQuasicoherent] : (⨁ B).IsQuasicoherent := by
  apply QuasicoherentLocal.IsAffineLocallyQuasicoherent.isQuasicoherent
  intro V hV
  have : PreservesBiproduct B (Scheme.Modules.restrictFunctor hV.fromSpec) :=
    preservesBiproduct_of_preservesCoproduct _
  have := Langlands.AlgebraicGeometry.Modules.CechResolution.isQuasicoherent_biproduct_spec
    (fun j => (B j).restrict hV.fromSpec)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Z, V)).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctor hV.fromSpec).mapBiproduct B).symm this

end Restriction

section Algebra

open scoped ChangeOfRings TensorProduct

variable {B R : Type u} [CommRing B] [CommRing R] (φ : B →+* R)
  {Q : ModuleCat.{u} B} {P : ModuleCat.{u} R}
  {n m : ℕ} (t : Fin n → Q) (ρ : Fin m → Fin n → B) (p : Fin n → P)

lemma exists_eq_sum_tmul (ht : Submodule.span B (Set.range t) = ⊤)
    (x : (ModuleCat.extendScalars φ).obj Q) :
    ∃ c : Fin n → R, x = ∑ l, c l ⊗ₜ[B, φ] t l := by
  induction x using TensorProduct.inductionOn with
  | tmul r q =>
    have hq : q ∈ Submodule.span B (Set.range t) := ht ▸ Submodule.mem_top
    obtain ⟨b, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hq
    refine ⟨fun l => φ (b l) * (show R from r), ?_⟩
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← TensorProduct.smul_tmul]
    rfl
  | add x y hx hy =>
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := hy
    exact ⟨c + d, by simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩

lemma tmul_eq_smul_one_tmul (r : R) (b : B) (y : Q) :
    (r * φ b) ⊗ₜ[B, φ] y =
      r • ((1 : R) ⊗ₜ[B, φ] (b • y) : (ModuleCat.extendScalars φ).obj Q) := by
  let : Module B R := Module.compHom R φ
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one, ← TensorProduct.smul_tmul]
  congr 1
  exact mul_comm _ _

lemma bijective_of_relations (Ψ : (ModuleCat.extendScalars φ).obj Q ⟶ P)
    (ht : Submodule.span B (Set.range t) = ⊤) (hρ : ∀ a, ∑ l, ρ a l • t l = 0)
    (hΨ : ∀ (r : R) l, Ψ (r ⊗ₜ[B, φ] t l) = r • p l)
    (hgen : Submodule.span R (Set.range p) = ⊤)
    (hrel : ∀ c : Fin n → R, ∑ l, c l • p l = 0 →
      c ∈ Submodule.span R (Set.range fun a l => φ (ρ a l))) :
    Function.Bijective Ψ := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := exists_eq_sum_tmul φ t ht x
    have hc : ∑ l, c l • p l = 0 := by
      rw [← hx, map_sum]
      exact Finset.sum_congr rfl fun l _ => (hΨ (c l) l).symm
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hrel c hc)
    subst hd
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, TensorProduct.sum_tmul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    simp only [tmul_eq_smul_one_tmul, ← Finset.smul_sum, ← TensorProduct.tmul_sum, hρ a,
      TensorProduct.tmul_zero, smul_zero]
  · have hle : Submodule.span R (Set.range p) ≤ LinearMap.range Ψ.hom := by
      rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact ⟨(1 : R) ⊗ₜ[B, φ] t l, (hΨ 1 l).trans (one_smul R (p l))⟩
    intro y
    have hy : y ∈ LinearMap.range Ψ.hom := hle (hgen ▸ Submodule.mem_top)
    exact hy

end Algebra

section SpecIso

variable {R : CommRingCat.{u}}

/-- A morphism of quasi-coherent sheaves on a spectrum that is bijective on global sections is
an isomorphism. -/
lemma isIso_of_bijective_app_top {A B : (Spec R).Modules} [A.IsQuasicoherent]
    [B.IsQuasicoherent] (φ : A ⟶ B) (h : Function.Bijective (φ.app ⊤)) : IsIso φ := by
  have h1 : IsIso ((moduleSpecΓFunctor (R := R)).map φ) :=
    (ConcreteCategory.isIso_iff_bijective _).2 h
  have h2 : IsIso ((moduleSpecΓFunctor ⋙ tilde.functor R).map φ) :=
    inferInstanceAs (IsIso ((tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map φ)))
  have hnat := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have hB : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := R)).app B) :=
    inferInstanceAs (IsIso B.fromTildeΓ)
  have hA : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := R)).app A) :=
    inferInstanceAs (IsIso A.fromTildeΓ)
  have h3 : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := R)).app A ≫ (𝟭 _).map φ) := by
    rw [← hnat]
    exact IsIso.comp_isIso
  have h4 : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := R)).app A ≫ φ) := h3
  exact IsIso.of_isIso_comp_left ((Scheme.Modules.fromTildeΓNatTrans (R := R)).app A) φ

end SpecIso

section AffineFinitePresentation

/-- On a spectrum, a locally finitely presented module sheaf has finitely presented global
sections. -/
lemma finitePresentation_moduleSpecΓ {R : CommRingCat.{u}} (A : (Spec R).Modules)
    [A.IsFinitePresentation] :
    Module.FinitePresentation R ((moduleSpecΓFunctor (R := R)).obj A) := by
  let N := ModuleCat.of R ((moduleSpecΓFunctor (R := R)).obj A)
  have hloc : ∀ x : Spec R, ∃ r : R, x ∈ PrimeSpectrum.basicOpen r ∧
      Module.FinitePresentation Γ(Spec R, PrimeSpectrum.basicOpen r)
        Γ(tilde N, PrimeSpectrum.basicOpen r) := by
    intro x
    obtain ⟨O, hxO, P, hP⟩ := exists_finitePresentation_restrict A x
    obtain ⟨_, ⟨r, rfl⟩, hxr, hrO⟩ :=
      (Opens.isBasis_iff_nbhd.1 PrimeSpectrum.isBasis_basic_opens) hxO
    have hD : IsAffineOpen (X := Spec R) (PrimeSpectrum.basicOpen r) := IsAffineOpen.Spec_basicOpen r
    let k : Spec Γ(Spec R, PrimeSpectrum.basicOpen r) ⟶ O.toScheme :=
      IsOpenImmersion.lift O.ι hD.fromSpec (by
        rw [Scheme.Opens.range_ι, hD.range_fromSpec]
        exact hrO)
    have hk : k ≫ O.ι = hD.fromSpec := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion k := IsOpenImmersion.of_comp k O.ι
    have := hP
    have hfp := finitePresentation_moduleSpecΓFunctor_of_presentation
      (presentationRestrictOfFac A O.ι k hD.fromSpec hk P)
    have hA : Module.FinitePresentation Γ(Spec R, PrimeSpectrum.basicOpen r)
        Γ(A, PrimeSpectrum.basicOpen r) :=
      Module.FinitePresentation.of_equiv
        (LinearEquiv.ofBijective (chart A hD) (chart_bijective A hD)).symm
    let e : Γ(tilde N, PrimeSpectrum.basicOpen r) →ₗ[Γ(Spec R, PrimeSpectrum.basicOpen r)]
        Γ(A, PrimeSpectrum.basicOpen r) :=
      { toFun := (fromTildeΓ' A).app _
        map_add' := map_add _
        map_smul' := Scheme.Modules.Hom.app_smul _ }
    have he : Function.Bijective e :=
      ConcreteCategory.bijective_of_isIso ((fromTildeΓ' A).app (PrimeSpectrum.basicOpen r))
    exact ⟨r, hxr, Module.FinitePresentation.of_equiv (LinearEquiv.ofBijective e he).symm⟩
  choose r hxr hr using hloc
  let S : Set R := Set.range r
  have hS : Ideal.span S = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    refine top_unique fun x _ => ?_
    exact Opens.mem_iSup.2 ⟨x, hxr x⟩
  have hfp : ∀ g : S, Module.FinitePresentation Γ(Spec R, PrimeSpectrum.basicOpen g.1)
      Γ(tilde N, PrimeSpectrum.basicOpen g.1) := by
    rintro ⟨_, x, rfl⟩
    exact hr x
  have : ∀ g : S, IsLocalizedModule (Submonoid.powers g.1)
      (tilde.toOpen N (PrimeSpectrum.basicOpen g.1)).hom :=
    fun g => inferInstanceAs (IsLocalizedModule.Away g.1 _)
  exact Module.FinitePresentation.of_localizationSpan' S hS
    (Rₚ := fun g => Γ(Spec R, PrimeSpectrum.basicOpen g.1))
    (Mₚ := fun g => Γ(tilde N, PrimeSpectrum.basicOpen g.1))
    (fun g => (tilde.toOpen N (PrimeSpectrum.basicOpen g.1)).hom) hfp

/-- Sections of a locally finitely presented module sheaf over an affine open are finitely
presented. -/
lemma finitePresentation_sections_of_isAffineOpen {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.FinitePresentation Γ(X, U) Γ(M, U) := by
  have h1 : SheafOfModules.isFinitePresentation (Spec Γ(X, U)).ringCatSheaf
      ((Scheme.Modules.pullback hU.fromSpec).obj M) := isFinitePresentation_pullback hU.fromSpec M
  have : (M.restrict hU.fromSpec).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (Spec Γ(X, U)).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app M).symm h1
  have := finitePresentation_moduleSpecΓ (M.restrict hU.fromSpec)
  exact Module.FinitePresentation.of_equiv
    (LinearEquiv.ofBijective (chart M hU) (chart_bijective M hU)).symm

end AffineFinitePresentation

section Construction

variable {X : Scheme.{u}} (q : X ⟶ Y) (M : X.Modules)

/-- The direct image of `M`. -/
abbrev directImage : Y.Modules := (Scheme.Modules.pushforward q).obj M

variable {ι : Type u} (V : ι → Y.Opens) (hV : ∀ i, IsAffineOpen (V i))
  {n : ι → ℕ} (g : ∀ i, Fin (n i) → Γ(directImage q M, V i))

/-- The submodule spanned by the chosen sections over `V i`. -/
def spanSub (i : ι) : Submodule Γ(Y, V i) Γ(directImage q M, V i) :=
  Submodule.span Γ(Y, V i) (Set.range (g i))

/-- The same submodule in the global sections of the restriction to the spectrum. -/
def chartSub (i : ι) : Submodule Γ(Y, V i)
    ((moduleSpecΓFunctor (R := Γ(Y, V i))).obj ((directImage q M).restrict (hV i).fromSpec)) :=
  (spanSub q M V g i).map (chart (directImage q M) (hV i))

lemma chart_mem_chartSub_iff (i : ι) (x : Γ(directImage q M, V i)) :
    chart (directImage q M) (hV i) x ∈ chartSub q M V hV g i ↔ x ∈ spanSub q M V g i := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [(chart_bijective (directImage q M) (hV i)).1 hxy] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

variable [M.IsQuasicoherent] [IsAffineHom q]

instance : (directImage q M).IsQuasicoherent :=
  QuasicoherentLocal.isQuasicoherent_pushforward q M

/-- The target sheaf for index `i`. -/
abbrev target (i : ι) : Y.Modules :=
  (Scheme.Modules.pushforward (hV i).fromSpec).obj
    (quotientSheaf ((directImage q M).restrict (hV i).fromSpec) (chartSub q M V hV g i))

/-- The component map for index `i`. -/
def component (i : ι) : directImage q M ⟶ target q M V hV g i :=
  (Scheme.Modules.restrictAdjunction (hV i).fromSpec).unit.app (directImage q M) ≫
    (Scheme.Modules.pushforward (hV i).fromSpec).map (quotientMap _ (chartSub q M V hV g i))

lemma component_app (i : ι) (W : Y.Opens) (x : Γ(directImage q M, W)) :
    (component q M V hV g i).app W x =
      (quotientMap _ (chartSub q M V hV g i)).app ((hV i).fromSpec ⁻¹ᵁ W)
        ((directImage q M).presheaf.map
          (homOfLE ((hV i).fromSpec.image_preimage_le W)).op x) := rfl

lemma component_self_app_eq_zero_iff (i : ι) (x : Γ(directImage q M, V i)) :
    (component q M V hV g i).app (V i) x = 0 ↔ x ∈ spanSub q M V g i := by
  have hpre : (⊤ : (Spec Γ(Y, V i)).Opens) ≤ (hV i).fromSpec ⁻¹ᵁ V i :=
    (hV i).fromSpec_preimage_self.ge
  have hc : ((directImage q M).restrict (hV i).fromSpec).presheaf.map (homOfLE hpre).op
      ((directImage q M).presheaf.map
        (homOfLE ((hV i).fromSpec.image_preimage_le (V i))).op x) =
      chart (directImage q M) (hV i) x := by
    change (directImage q M).presheaf.map _ ((directImage q M).presheaf.map _ x) =
      (directImage q M).presheaf.map _ x
    rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
    rfl
  rw [component_app, ← map_eq_zero_of_eq _ (hV i).fromSpec_preimage_self hpre, ← app_map, hc,
    quotientMap_app_top_eq_zero_iff, chart_mem_chartSub_iff]

lemma component_app_eq_zero_of_mem (i k : ι)
    (hcross : ∀ y ∈ V i ⊓ V k, ∃ (D : Y.Opens) (hD : D ≤ V i ⊓ V k), y ∈ D ∧ ∀ l,
      (directImage q M).presheaf.map (homOfLE (hD.trans inf_le_right)).op (g k l) ∈
        Submodule.span Γ(Y, D) (Set.range fun m =>
          (directImage q M).presheaf.map (homOfLE (hD.trans inf_le_left)).op (g i m)))
    (s : Γ(directImage q M, V k)) (hs : s ∈ spanSub q M V g k) :
    (component q M V hV g i).app (V k) s = 0 := by
  have heq : (hV i).fromSpec ⁻¹ᵁ (V k ⊓ V i) = (hV i).fromSpec ⁻¹ᵁ (V k) := by
    rw [Scheme.Hom.preimage_inf, (hV i).fromSpec_preimage_self, inf_top_eq]
  have hinj : Function.Injective
      ((target q M V hV g i).presheaf.map (homOfLE (inf_le_left : V k ⊓ V i ≤ V k)).op) :=
    (Langlands.Scheme.Modules.bijective_map_of_eq
      (quotientSheaf ((directImage q M).restrict (hV i).fromSpec) (chartSub q M V hV g i))
      heq.symm ((hV i).fromSpec.preimage_mono inf_le_left)).1
  apply hinj
  rw [map_zero, ← app_map]
  refine Langlands.Scheme.Modules.BasisHomGluing.eq_of_forall_mem _ 0 ?_
  intro y hy
  obtain ⟨D, hD, hyD, hl⟩ := hcross y ⟨hy.2, hy.1⟩
  refine ⟨D, le_inf (hD.trans inf_le_right) (hD.trans inf_le_left), hyD, ?_⟩
  rw [map_zero, ← app_map, map_map]
  have hmem : (directImage q M).presheaf.map (homOfLE (hD.trans inf_le_right)).op s ∈
      Submodule.span Γ(Y, D) (Set.range fun m =>
        (directImage q M).presheaf.map (homOfLE (hD.trans inf_le_left)).op (g i m)) := by
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      exact hl l
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x _ hx =>
      rw [Scheme.Modules.map_smul]
      exact Submodule.smul_mem _ _ hx
  have hkill : ∀ x ∈ Submodule.span Γ(Y, D) (Set.range fun m =>
      (directImage q M).presheaf.map (homOfLE (hD.trans inf_le_left)).op (g i m)),
      (component q M V hV g i).app D x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [app_map, (component_self_app_eq_zero_iff q M V hV g i (g i m)).2
        (Submodule.subset_span ⟨m, rfl⟩), map_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [Scheme.Modules.Hom.app_smul, hx, smul_zero]
  exact hkill _ hmem

/-- The cross condition: over overlaps, the chosen sections over `V k` lie locally in the
span of the restrictions of the chosen sections over `V i`. -/
def CrossCondition : Prop :=
  ∀ i k, ∀ y ∈ V i ⊓ V k, ∃ (D : Y.Opens) (hD : D ≤ V i ⊓ V k), y ∈ D ∧ ∀ l,
    (directImage q M).presheaf.map (homOfLE (hD.trans inf_le_right)).op (g k l) ∈
      Submodule.span Γ(Y, D) (Set.range fun m =>
        (directImage q M).presheaf.map (homOfLE (hD.trans inf_le_left)).op (g i m))

variable [Fintype ι]

/-- The total map to the finite direct sum of the targets. -/
def total : directImage q M ⟶ ⨁ (target q M V hV g) :=
  biproduct.lift (component q M V hV g)

lemma total_app_eq_zero_iff (W : Y.Opens) (x : Γ(directImage q M, W)) :
    (total q M V hV g).app W x = 0 ↔ ∀ i, (component q M V hV g i).app W x = 0 := by
  constructor
  · intro h i
    have : component q M V hV g i = total q M V hV g ≫ biproduct.π _ i :=
      (biproduct.lift_π _ _).symm
    rw [this, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h, map_zero]
  · intro h
    refine biproduct_app_eq_zero _ fun i => ?_
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, total, biproduct.lift_π]
    exact h i

/-- The descended module: the kernel of the total map. -/
def descended : Y.Modules := kernel (total q M V hV g)

/-- The inclusion of the descended module into the direct image. -/
def descendedι : descended q M V hV g ⟶ directImage q M := kernel.ι _

lemma descendedι_app_injective (W : Y.Opens) :
    Function.Injective ((descendedι q M V hV g).app W) :=
  QuasicoherentLocal.kernel_ι_app_injective _ W

lemma descendedι_app_mem (k : ι) (t : Γ(descended q M V hV g, V k)) :
    (descendedι q M V hV g).app (V k) t ∈ spanSub q M V g k := by
  have h := QuasicoherentLocal.app_kernel_ι_app (total q M V hV g) (V k) t
  rw [total_app_eq_zero_iff] at h
  exact (component_self_app_eq_zero_iff q M V hV g k _).1 (h k)

lemma exists_descendedι_app_eq (hcross : CrossCondition q M V g) (k : ι)
    (s : Γ(directImage q M, V k)) (hs : s ∈ spanSub q M V g k) :
    ∃ t, (descendedι q M V hV g).app (V k) t = s :=
  QuasicoherentLocal.exists_kernel_ι_app_eq (total q M V hV g) s
    ((total_app_eq_zero_iff q M V hV g _ s).2 fun i =>
      component_app_eq_zero_of_mem q M V hV g i k (hcross i k) s hs)

lemma isQuasicoherent_descended (hfs : ∀ i, IsAffineHom (hV i).fromSpec) :
    (descended q M V hV g).IsQuasicoherent := by
  have : ∀ i, (target q M V hV g i).IsQuasicoherent := fun i => by
    have := hfs i
    exact QuasicoherentLocal.isQuasicoherent_pushforward _ _
  have := isQuasicoherent_biproduct (target q M V hV g)
  exact QuasicoherentLocal.isQuasicoherent_kernel _

/-- Sections of the descended module as a linear map into the direct image. -/
def descendedιLinear (W : Y.Opens) :
    Γ(descended q M V hV g, W) →ₗ[Γ(Y, W)] Γ(directImage q M, W) where
  toFun := (descendedι q M V hV g).app W
  map_add' := map_add _
  map_smul' := Scheme.Modules.Hom.app_smul _

lemma span_descended_eq_top (k : ι)
    (t : Fin (n k) → Γ(descended q M V hV g, V k))
    (ht : ∀ l, (descendedι q M V hV g).app (V k) (t l) = g k l) :
    Submodule.span Γ(Y, V k) (Set.range t) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hx := descendedι_app_mem q M V hV g k x
  have hrange : Set.range (g k) = (descendedιLinear q M V hV g (V k)) '' Set.range t := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun l => (ht l).symm)
  change (descendedιLinear q M V hV g (V k)) x ∈ Submodule.span Γ(Y, V k) (Set.range (g k)) at hx
  rw [hrange, ← Submodule.map_span] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  rwa [descendedι_app_injective q M V hV g (V k) hxy] at hy

lemma isFinitePresentation_descended (hfs : ∀ i, IsAffineHom (hV i).fromSpec)
    [∀ i, IsNoetherianRing Γ(Y, V i)] (hcov : ∀ y : Y, ∃ i, y ∈ V i)
    (hcross : CrossCondition q M V g) :
    (descended q M V hV g).IsFinitePresentation := by
  have := isQuasicoherent_descended q M V hV g hfs
  apply isFinitePresentation_of_forall_exists_presentation
  intro y
  obtain ⟨k, hyk⟩ := hcov y
  choose t ht using fun l => exists_descendedι_app_eq q M V hV g hcross k (g k l)
    (Submodule.subset_span ⟨l, rfl⟩)
  have hfin : Module.Finite Γ(Y, V k) Γ(descended q M V hV g, V k) :=
    ⟨Submodule.fg_def.2 ⟨Set.range t, Set.finite_range t,
      span_descended_eq_top q M V hV g k t ht⟩⟩
  let G' := (descended q M V hV g).restrict (hV k).fromSpec
  have : Module.Finite Γ(Y, V k) ((moduleSpecΓFunctor (R := Γ(Y, V k))).obj G') :=
    Module.Finite.of_surjective (chart (descended q M V hV g) (hV k))
      (chart_bijective (descended q M V hV g) (hV k)).2
  have : Module.FinitePresentation Γ(Y, V k) ((moduleSpecΓFunctor (R := Γ(Y, V k))).obj G') :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨P, hP⟩ := exists_presentation_tilde ((moduleSpecΓFunctor (R := Γ(Y, V k))).obj G')
  have : P.IsFinite := hP
  have : IsIso (G'.fromTildeΓ : tilde ((moduleSpecΓFunctor (R := Γ(Y, V k))).obj G') ⟶ G') :=
    inferInstance
  obtain ⟨P', hP'⟩ := exists_presentation_opensRange (descended q M V hV g) (hV k).fromSpec
    (P.ofIsIso (G'.fromTildeΓ : tilde ((moduleSpecΓFunctor (R := Γ(Y, V k))).obj G') ⟶ G'))
  refine ⟨(hV k).fromSpec.opensRange, ?_, P', hP'⟩
  rw [(hV k).opensRange_fromSpec]
  exact hyk

/-- The adjoint comparison from the pullback of the descended module to `M`. -/
def comparison : (Scheme.Modules.pullback q).obj (descended q M V hV g) ⟶ M :=
  ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm (descendedι q M V hV g)

lemma comparison_app_sectionPullback (W : Y.Opens) (t : Γ(descended q M V hV g, W)) :
    (comparison q M V hV g).app (q ⁻¹ᵁ W)
      (Langlands.Scheme.Modules.sectionPullback q _ W t) = (descendedι q M V hV g).app W t := by
  have h := Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction q)
    (descended q M V hV g) M (comparison q M V hV g)
  rw [comparison, Equiv.apply_symm_apply] at h
  rw [h]
  rfl

/-- The relation condition over `V k`: the chosen sections generate the sections of `M` over the
preimage, and their relations over the preimage are generated by relations over `V k`. -/
def RelationCondition (k : ι) : Prop :=
  ∃ (m : ℕ) (ρ : Fin m → Fin (n k) → Γ(Y, V k)),
    (∀ a, ∑ l, ρ a l • g k l = 0) ∧
    Submodule.span Γ(X, q ⁻¹ᵁ V k)
        (Set.range fun l => (show Γ(M, q ⁻¹ᵁ V k) from g k l)) = ⊤ ∧
    ∀ c : Fin (n k) → Γ(X, q ⁻¹ᵁ V k), ∑ l, c l • (show Γ(M, q ⁻¹ᵁ V k) from g k l) = 0 →
      c ∈ Submodule.span Γ(X, q ⁻¹ᵁ V k) (Set.range fun a l => q.app (V k) (ρ a l))

open scoped ChangeOfRings TensorProduct in
lemma bijective_comparison_app (hfs : ∀ i, IsAffineHom (hV i).fromSpec)
    (hcross : CrossCondition q M V g) (k : ι) (hrel : RelationCondition q M V g k) :
    Function.Bijective ((comparison q M V hV g).app (q ⁻¹ᵁ V k)) := by
  have := isQuasicoherent_descended q M V hV g hfs
  obtain ⟨m, ρ, hρ, hgen, hrel⟩ := hrel
  choose t ht using fun l => exists_descendedι_app_eq q M V hV g hcross k (g k l)
    (Submodule.subset_span ⟨l, rfl⟩)
  have hU : IsAffineOpen (q ⁻¹ᵁ V k) := (hV k).preimage q
  let Φ := Langlands.Scheme.Modules.pullbackTensorMap q (descended q M V hV g)
    (le_refl (q ⁻¹ᵁ V k))
  have hΦ : Function.Bijective Φ :=
    Langlands.Scheme.Modules.pullbackTensorMap_bijective q _ _ hU (hV k)
  let κL : ModuleCat.of Γ(X, q ⁻¹ᵁ V k)
      Γ((Scheme.Modules.pullback q).obj (descended q M V hV g), q ⁻¹ᵁ V k) ⟶
      ModuleCat.of Γ(X, q ⁻¹ᵁ V k) Γ(M, q ⁻¹ᵁ V k) :=
    ModuleCat.ofHom
      { toFun := (comparison q M V hV g).app (q ⁻¹ᵁ V k)
        map_add' := map_add _
        map_smul' := Scheme.Modules.Hom.app_smul _ }
  have hρ' : ∀ a, ∑ l, ρ a l • t l = 0 := by
    intro a
    apply descendedι_app_injective q M V hV g (V k)
    rw [map_zero, map_sum]
    refine (Finset.sum_congr rfl fun l _ => ?_).trans (hρ a)
    rw [Scheme.Modules.Hom.app_smul, ht l]
  have hΨ : ∀ (r : Γ(X, q ⁻¹ᵁ V k)) l,
      (Φ ≫ κL) (r ⊗ₜ[Γ(Y, V k), (q.appLE (V k) (q ⁻¹ᵁ V k) le_rfl).hom] t l) =
        r • (show Γ(M, q ⁻¹ᵁ V k) from g k l) := by
    intro r l
    rw [ConcreteCategory.comp_apply, Langlands.Scheme.Modules.pullbackTensorMap_tmul]
    change (comparison q M V hV g).app (q ⁻¹ᵁ V k) (r • _) = _
    rw [Scheme.Modules.Hom.app_smul, Langlands.Scheme.Modules.sectionPullbackLE_self,
      comparison_app_sectionPullback, ht l]
  have hrel' : ∀ c : Fin (n k) → Γ(X, q ⁻¹ᵁ V k),
      ∑ l, c l • (show Γ(M, q ⁻¹ᵁ V k) from g k l) = 0 →
      c ∈ Submodule.span Γ(X, q ⁻¹ᵁ V k)
        (Set.range fun a l => (q.appLE (V k) (q ⁻¹ᵁ V k) le_rfl).hom (ρ a l)) := by
    intro c hc
    rw [Scheme.Hom.appLE_eq_app]
    exact hrel c hc
  have hΨb := bijective_of_relations (q.appLE (V k) (q ⁻¹ᵁ V k) le_rfl).hom t ρ
    (fun l => (show Γ(M, q ⁻¹ᵁ V k) from g k l)) (Φ ≫ κL)
    (span_descended_eq_top q M V hV g k t ht) hρ' hΨ hgen hrel'
  exact (Function.Bijective.of_comp_iff κL hΦ).1 hΨb

lemma isIso_comparison (hfs : ∀ i, IsAffineHom (hV i).fromSpec) (hcov : ∀ y : Y, ∃ i, y ∈ V i)
    (hcross : CrossCondition q M V g) (hrel : ∀ k, RelationCondition q M V g k) :
    IsIso (comparison q M V hV g) := by
  have := isQuasicoherent_descended q M V hV g hfs
  apply Langlands.AlgebraicGeometry.Modules.DerivedSections.isIso_of_affineOpenPullbacks
  intro x
  obtain ⟨k, hk⟩ := hcov (q x)
  have hU : IsAffineOpen (q ⁻¹ᵁ V k) := (hV k).preimage q
  refine ⟨_, hU.fromSpec, inferInstance, ?_⟩
  have hx : x ∈ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    exact hk
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, hy, ?_⟩
  rw [← NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec)]
  apply isIso_of_bijective_app_top
  change Function.Bijective ((comparison q M V hV g).app (hU.fromSpec ''ᵁ ⊤))
  rw [image_fromSpec_top hU]
  exact bijective_comparison_app q M V hV g hfs hcross k (hrel k)

/-- **Core descent step.** Let `q : X ⟶ Y` be affine, `M` quasi-coherent on `X`, and `V` a finite
affine open cover of `Y` with noetherian coordinate rings and affine inclusions. Suppose chosen
sections of the direct image over each `V k` satisfy the relation and cross conditions. Then
`M` is the pullback of a finitely presented module on `Y`. -/
theorem exists_isFinitePresentation_pullback_iso (hfs : ∀ i, IsAffineHom (hV i).fromSpec)
    [∀ i, IsNoetherianRing Γ(Y, V i)] (hcov : ∀ y : Y, ∃ i, y ∈ V i)
    (hcross : CrossCondition q M V g) (hrel : ∀ k, RelationCondition q M V g k) :
    ∃ G : Y.Modules, G.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pullback q).obj G ≅ M) := by
  have := isIso_comparison q M V hV g hfs hcov hcross hrel
  exact ⟨descended q M V hV g, isFinitePresentation_descended q M V hV g hfs hcov hcross,
    ⟨asIso (comparison q M V hV g)⟩⟩

end Construction

end Langlands.AlgebraicGeometry.NoetherianApproximation.ModuleDescentCore
