import Langlands.AlgebraicGeometry.Modules.StalkPullback
import Langlands.AlgebraicGeometry.FiberStalkFlatness
import Langlands.Algebra.PrimeLocalizationCriterion
import Langlands.Algebra.LocalApproximationFlatnessPropagation
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules

namespace RelativeFlatnessPullback

/-- Localizing the algebra in a pushout preserves base flatness of a base-changed module. -/
lemma flat_tensor_of_pushout_localization
    (R A B C D : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra.IsPushout R B A C]
    [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A C D] [IsScalarTower B C D]
    (T : Submonoid C) [IsLocalization T D]
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Flat R M] : Module.Flat B (D ⊗[A] M) := by
  have : Module.Flat B (C ⊗[A] M) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange R B A C M)
  have : Module.Flat B (D ⊗[C] (C ⊗[A] M)) :=
    Langlands.Algebra.flat_of_isLocalizedModule_of_flat T
      (TensorProduct.mk C D (C ⊗[A] M) 1)
  exact Module.Flat.of_linearEquiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A C D D M).symm.restrictScalars B)

/-- The affine-section pushout and its two stalk localizations preserve relative flatness. -/
lemma flat_tensor_of_sections
    {R Q B Q' L D : CommRingCat.{u}} {t : R ⟶ Q} {b : R ⟶ B}
    {i : Q ⟶ Q'} {j : B ⟶ Q'} (P : IsPushout t b i j)
    (γ : Q ⟶ L) (δ : Q' ⟶ D) (α : L ⟶ D) (β : B ⟶ D)
    (hα : γ ≫ α = i ≫ δ) (hβ : β = j ≫ δ)
    [IsLocalRing D]
    (V : Submonoid Q) (W : Submonoid Q')
    (hγ : let := γ.hom.toAlgebra; IsLocalization V L)
    (hδ : let := δ.hom.toAlgebra; IsLocalization W D)
    (M : Type u) [AddCommGroup M] [Module L M]
    (hM : let := Module.compHom M (t ≫ γ).hom; Module.Flat R M) :
    let := α.hom.toAlgebra
    let := β.hom.toAlgebra
    Module.Flat B (D ⊗[L] M) := by
  let := t.hom.toAlgebra
  let := b.hom.toAlgebra
  let := i.hom.toAlgebra
  let := j.hom.toAlgebra
  let := (t ≫ i).hom.toAlgebra
  have : IsScalarTower R Q Q' := .of_algebraMap_eq' rfl
  have : IsScalarTower R B Q' := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom P.w)
  have : Algebra.IsPushout R Q B Q' := CommRingCat.isPushout_iff_isPushout.mp P
  let := γ.hom.toAlgebra
  let := (t ≫ γ).hom.toAlgebra
  have : IsScalarTower R Q L := .of_algebraMap_eq' rfl
  let := α.hom.toAlgebra
  let := β.hom.toAlgebra
  let := δ.hom.toAlgebra
  let := ((t ≫ γ) ≫ α).hom.toAlgebra
  have : IsScalarTower R L D := .of_algebraMap_eq' rfl
  have : IsScalarTower R B D := .of_algebraMap_eq' (by
    change ((t ≫ γ) ≫ α).hom = (b ≫ β).hom
    rw [Category.assoc, hα, ← Category.assoc, P.w, Category.assoc, ← hβ])
  have := hγ
  have := hδ
  let F : L ⊗[R] B →ₐ[R] D := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R L D) (IsScalarTower.toAlgHom R B D) (fun _ _ => mul_comm _ _)
  have hFQ : (F.toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (B := B))).comp (algebraMap Q L) =
      (algebraMap Q' D).comp (algebraMap Q Q') := by
    ext q
    change F (algebraMap Q L q ⊗ₜ[R] (1 : B)) = δ (i q)
    simp only [F, Algebra.TensorProduct.lift_tmul, IsScalarTower.toAlgHom_apply,
      map_one, mul_one]
    change α (γ q) = δ (i q)
    exact congrArg (fun k : Q ⟶ D => k q) hα
  have hFB : F.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := R) (A := L)).toRingHom =
      (algebraMap Q' D).comp (algebraMap B Q') := by
    ext q
    change F ((1 : L) ⊗ₜ[R] q) = δ (j q)
    simp only [F, Algebra.TensorProduct.lift_tmul, IsScalarTower.toAlgHom_apply,
      map_one, one_mul]
    change β q = δ (j q)
    exact congrArg (fun k : B ⟶ D => k q) hβ
  let := F.toRingHom.toAlgebra
  have : IsScalarTower L (L ⊗[R] B) D := .of_algebraMap_eq' (by
    ext q
    change α q = F (q ⊗ₜ[R] (1 : B))
    simp [F]
    rfl)
  let : Algebra B (L ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R B (L ⊗[R] B) := inferInstance
  have : IsScalarTower B (L ⊗[R] B) D := .of_algebraMap_eq' (by
    ext q
    change β q = F ((1 : L) ⊗ₜ[R] q)
    simp [F]
    rfl)
  have : Algebra.IsPushout R B L (L ⊗[R] B) :=
    Algebra.IsPushout.symm inferInstance
  have := Langlands.Algebra.isLocalization_atPrime_tensor_of_isPushout_canonical
    V W F.toRingHom hFQ hFB
  let : Module R M := Module.compHom M (t ≫ γ).hom
  have : IsScalarTower R L M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have := hM
  exact flat_tensor_of_pushout_localization R L B (L ⊗[R] B) D
    ((IsLocalRing.maximalIdeal D).comap F.toRingHom).primeCompl M

/-- A relatively flat stalk is flat over sections of any affine base neighbourhood. -/
lemma flat_stalk_of_affine_base {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (hM : IsFlatOver f M) (x : X) (US : S.Opens) (hUS : IsAffineOpen US)
    (hs : f x ∈ US) (UX : X.Opens) (hx : x ∈ UX) (e : UX ≤ f ⁻¹ᵁ US) :
    letI := Module.compHom (stalk M x)
      (f.appLE US UX e ≫ X.presheaf.germ UX x hx).hom
    Module.Flat Γ(S, US) (stalk M x) := by
  rw [← FiberStalkFlatness.germ_stalkMap_eq_appLE_germ f US UX e x hx hs]
  let := (S.presheaf.germ US (f x) hs).hom.toAlgebra
  let := relativeStalkModule f M x
  let : Module Γ(S, US) (stalk M x) :=
    Module.compHom _ (S.presheaf.germ US (f x) hs ≫ f.stalkMap x).hom
  have : IsScalarTower Γ(S, US) (S.presheaf.stalk (f x)) (stalk M x) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have := hUS.isLocalization_stalk ⟨f x, hs⟩
  have : Module.Flat Γ(S, US) (S.presheaf.stalk (f x)) :=
    IsLocalization.flat _ (hUS.primeIdealOf ⟨f x, hs⟩).asIdeal.primeCompl
  have : Module.Flat (S.presheaf.stalk (f x)) (stalk M x) := hM x
  exact Module.Flat.trans Γ(S, US) (S.presheaf.stalk (f x)) (stalk M x)

/-- The actual pullback tensor stalk is flat over the new base local ring. -/
lemma flat_tensor_stalk {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {p : P ⟶ T} (H : IsPullback a p f g)
    (M : X.Modules) (hM : IsFlatOver f M) (z : P) :
    letI := (a.stalkMap z).hom.toAlgebra
    letI := (p.stalkMap z).hom.toAlgebra
    Module.Flat (T.presheaf.stalk (p z))
      (P.presheaf.stalk z ⊗[X.presheaf.stalk (a z)] stalk M (a z)) := by
  let := (a.stalkMap z).hom.toAlgebra
  let := (p.stalkMap z).hom.toAlgebra
  obtain ⟨US, hUS, hs, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := f (a z)) (by simp)
  have hgt : g (p z) ∈ US := by
    rw [← Scheme.Hom.comp_apply, ← H.w, Scheme.Hom.comp_apply]
    exact hs
  obtain ⟨UX, hUX, hx, hXS⟩ :=
    exists_isAffineOpen_mem_and_subset (U := f ⁻¹ᵁ US) (x := a z) hs
  obtain ⟨UT, hUT, ht, hTS⟩ :=
    exists_isAffineOpen_mem_and_subset (U := g ⁻¹ᵁ US) (x := p z) hgt
  have hXS' : UX ≤ f ⁻¹ᵁ US := hXS
  have hTS' : UT ≤ g ⁻¹ᵁ US := hTS
  have : IsAffine _ := hUS
  have : IsAffine _ := hUX
  have : IsAffine _ := hUT
  have hUP : IsAffineOpen (a ⁻¹ᵁ UX ⊓ p ⁻¹ᵁ UT) :=
    IsAffine.of_isIso (Scheme.Hom.isPullback_resLE H hTS' hXS' rfl).isoPullback.hom
  have hz : z ∈ a ⁻¹ᵁ UX ⊓ p ⁻¹ᵁ UT := ⟨hx, ht⟩
  have Q := (isIso_pushoutSection_iff H hTS' hXS' rfl).mp
    (isIso_pushoutSection_of_isAffineOpen H hTS' hXS' rfl hUS hUT hUX)
  have hf := flat_tensor_of_sections Q
    (X.presheaf.germ UX (a z) hx)
    (P.presheaf.germ (a ⁻¹ᵁ UX ⊓ p ⁻¹ᵁ UT) z hz)
    (a.stalkMap z) (T.presheaf.germ UT (p z) ht ≫ p.stalkMap z)
    (FiberStalkFlatness.germ_stalkMap_eq_appLE_germ a UX _ inf_le_left z hz hx)
    (FiberStalkFlatness.germ_stalkMap_eq_appLE_germ p UT _ inf_le_right z hz ht)
    _ _ (hUX.isLocalization_stalk ⟨a z, hx⟩) (hUP.isLocalization_stalk ⟨z, hz⟩)
    (stalk M (a z)) (flat_stalk_of_affine_base f M hM (a z) US hUS hs UX hx hXS')
  let := (T.presheaf.germ UT (p z) ht).hom.toAlgebra
  let := (T.presheaf.germ UT (p z) ht ≫ p.stalkMap z).hom.toAlgebra
  have : IsScalarTower Γ(T, UT) (T.presheaf.stalk (p z)) (P.presheaf.stalk z) :=
    .of_algebraMap_eq' rfl
  have := hUT.isLocalization_stalk ⟨p z, ht⟩
  exact (Module.flat_iff_of_isLocalization (T.presheaf.stalk (p z))
    (hUT.primeIdealOf ⟨p z, ht⟩).asIdeal.primeCompl _).mpr hf

end RelativeFlatnessPullback

/-- Ordinary module pullback in a cartesian scheme square preserves relative stalk flatness. -/
lemma isFlatOver_pullback_of_isPullback {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {p : P ⟶ T} (H : IsPullback a p f g)
    (M : X.Modules) (hM : IsFlatOver f M) :
    IsFlatOver p ((Scheme.Modules.pullback a).obj M) := by
  intro z
  let := (a.stalkMap z).hom.toAlgebra
  let := (p.stalkMap z).hom.toAlgebra
  let := relativeStalkModule p ((Scheme.Modules.pullback a).obj M) z
  have : IsScalarTower (T.presheaf.stalk (p z)) (P.presheaf.stalk z)
      (stalk ((Scheme.Modules.pullback a).obj M) z) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have := RelativeFlatnessPullback.flat_tensor_stalk H M hM z
  exact Module.Flat.of_linearEquiv
    ((StalkPullback.pullbackStalkTensorEquiv a z M).restrictScalars
      (T.presheaf.stalk (p z)))

/-- Ordinary pullback restricted to the full categories of relatively flat modules. -/
def flatPullback {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {p : P ⟶ T} (H : IsPullback a p f g) :
    (isFlatOver f).FullSubcategory ⥤ (isFlatOver p).FullSubcategory :=
  (isFlatOver p).lift ((isFlatOver f).ι ⋙ Scheme.Modules.pullback a)
    (fun M => isFlatOver_pullback_of_isPullback H M.obj M.property)

end Langlands.AlgebraicGeometry.Modules
