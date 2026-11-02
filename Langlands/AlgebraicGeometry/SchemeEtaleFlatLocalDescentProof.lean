import Langlands.CommutativeAlgebra.EtaleFlatLocalDescentProof
import Langlands.AlgebraicGeometry.Modules.RelativeFlatnessPullback
import Langlands.AlgebraicGeometry.StalkEssFinitePresentation
import Langlands.AlgebraicGeometry.SchemeEtaleFlatLocalDescentStatement

/-! # Pointwise etale descent in a flat scheme pullback -/

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry

namespace EtaleFlatLocalDescent

/-- Differential descent for the affine-section pushout with its two actual
stalk localizations. -/
lemma formallyUnramified_of_sections
    {R Q B Q' L D : CommRingCat.{u}} {t : R ⟶ Q} {b : R ⟶ B}
    {i : Q ⟶ Q'} {j : B ⟶ Q'} (P : IsPushout t b i j)
    (γ : Q ⟶ L) (δ : Q' ⟶ D) (α : L ⟶ D) (β : B ⟶ D)
    (hα : γ ≫ α = i ≫ δ) (hβ : β = j ≫ δ)
    [IsLocalRing D]
    (V : Submonoid Q) (W : Submonoid Q')
    (hγ : let := γ.hom.toAlgebra; IsLocalization V L)
    (hδ : let := δ.hom.toAlgebra; IsLocalization W D)
    (hff : let := α.hom.toAlgebra; Module.FaithfullyFlat L D)
    (hur : let := β.hom.toAlgebra; Algebra.FormallyUnramified B D) :
    let := (t ≫ γ).hom.toAlgebra
    Algebra.FormallyUnramified R L := by
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
  have := hff
  have := hur
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
  exact Langlands.CommutativeAlgebra.formallyUnramified_of_localized_baseChange
    R B L (L ⊗[R] B) D
    ((IsLocalRing.maximalIdeal D).comap F.toRingHom).primeCompl

/-- Formal unramifiedness at a pullback point descends when the projection to
the original source is flat. -/
lemma formallyUnramified_stalkMap_of_isPullback
    {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {p : P ⟶ T} (H : IsPullback a p f g)
    [Flat a] (z : P)
    (hur : let := (p.stalkMap z).hom.toAlgebra
      Algebra.FormallyUnramified (T.presheaf.stalk (p z)) (P.presheaf.stalk z)) :
    let := (f.stalkMap (a z)).hom.toAlgebra
    Algebra.FormallyUnramified (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z)) := by
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
  have hff : let := (a.stalkMap z).hom.toAlgebra
      Module.FaithfullyFlat (X.presheaf.stalk (a z)) (P.presheaf.stalk z) := by
    let := (a.stalkMap z).hom.toAlgebra
    have : Module.Flat (X.presheaf.stalk (a z)) (P.presheaf.stalk z) := Flat.stalkMap a z
    exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap a z) (a.toLRSHom.prop z)
  have hur' : let := (T.presheaf.germ UT (p z) ht ≫ p.stalkMap z).hom.toAlgebra
      Algebra.FormallyUnramified Γ(T, UT) (P.presheaf.stalk z) := by
    let := (T.presheaf.germ UT (p z) ht).hom.toAlgebra
    let := (p.stalkMap z).hom.toAlgebra
    let := (T.presheaf.germ UT (p z) ht ≫ p.stalkMap z).hom.toAlgebra
    have : IsScalarTower Γ(T, UT) (T.presheaf.stalk (p z)) (P.presheaf.stalk z) :=
      .of_algebraMap_eq' rfl
    have := hUT.isLocalization_stalk ⟨p z, ht⟩
    have : Algebra.FormallyUnramified Γ(T, UT) (T.presheaf.stalk (p z)) :=
      Algebra.FormallyUnramified.of_isLocalization (hUT.primeIdealOf ⟨p z, ht⟩).asIdeal.primeCompl
    have := hur
    exact Algebra.FormallyUnramified.comp Γ(T, UT) (T.presheaf.stalk (p z)) (P.presheaf.stalk z)
  have h := formallyUnramified_of_sections Q
    (X.presheaf.germ UX (a z) hx)
    (P.presheaf.germ (a ⁻¹ᵁ UX ⊓ p ⁻¹ᵁ UT) z hz)
    (a.stalkMap z) (T.presheaf.germ UT (p z) ht ≫ p.stalkMap z)
    (FiberStalkFlatness.germ_stalkMap_eq_appLE_germ a UX _ inf_le_left z hz hx)
    (FiberStalkFlatness.germ_stalkMap_eq_appLE_germ p UT _ inf_le_right z hz ht)
    _ _ (hUX.isLocalization_stalk ⟨a z, hx⟩) (hUP.isLocalization_stalk ⟨z, hz⟩)
    hff hur'
  rw [← FiberStalkFlatness.germ_stalkMap_eq_appLE_germ f US UX hXS' (a z) hx hs] at h
  let := (S.presheaf.germ US (f (a z)) hs).hom.toAlgebra
  let := (f.stalkMap (a z)).hom.toAlgebra
  let := (S.presheaf.germ US (f (a z)) hs ≫ f.stalkMap (a z)).hom.toAlgebra
  have : IsScalarTower Γ(S, US) (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z)) :=
    .of_algebraMap_eq' rfl
  have := h
  exact Algebra.FormallyUnramified.of_restrictScalars Γ(S, US)
    (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z))

/-- Flatness at a pullback point descends along a flat local stalk map,
provided that the other base morphism is flat. -/
lemma flat_stalkMap_of_isPullback
    {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {p : P ⟶ T} (H : IsPullback a p f g)
    [Flat a] [Flat g] (z : P) (hp : (p.stalkMap z).hom.Flat) :
    (f.stalkMap (a z)).hom.Flat := by
  let := (f.stalkMap (a z)).hom.toAlgebra
  let := (a.stalkMap z).hom.toAlgebra
  let := (f.stalkMap (a z) ≫ a.stalkMap z).hom.toAlgebra
  have : IsScalarTower (S.presheaf.stalk (f (a z)))
      (X.presheaf.stalk (a z)) (P.presheaf.stalk z) := .of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat (X.presheaf.stalk (a z)) (P.presheaf.stalk z) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap a z) (a.toLRSHom.prop z)
  have hflat : ((a ≫ f).stalkMap z).hom.Flat := by
    rw [H.w, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact (Flat.stalkMap g (p z)).comp hp
  rw [Scheme.Hom.stalkMap_comp] at hflat
  have : Module.Flat (S.presheaf.stalk (f (a z))) (P.presheaf.stalk z) := hflat
  exact Langlands.CommutativeAlgebra.flat_of_flat_of_faithfullyFlat
    (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z)) (P.presheaf.stalk z)

/-- The flat local criterion turns descended flatness and differential
vanishing into formal etaleness of the original stalk map. -/
lemma formallyEtale_stalkMap_of_isPullback
    {X S T P : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
    {a : P ⟶ X} {p : P ⟶ T} (H : IsPullback a p f g)
    [Flat a] [Flat g] [LocallyOfFinitePresentation f] (z : P)
    (hp : (p.stalkMap z).hom.Flat)
    (hur : (p.stalkMap z).hom.FormallyUnramified) :
    (f.stalkMap (a z)).hom.FormallyEtale := by
  let := (f.stalkMap (a z)).hom.toAlgebra
  have : IsLocalHom (algebraMap (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z))) :=
    f.toLRSHom.prop (a z)
  have : Module.Flat (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z)) :=
    flat_stalkMap_of_isPullback H z hp
  have : Algebra.FormallyUnramified
      (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z)) :=
    formallyUnramified_stalkMap_of_isPullback H z hur
  exact Langlands.CommutativeAlgebra.formallyEtale_of_flat_of_formallyUnramified_of_essFinitePresentation
    (S.presheaf.stalk (f (a z))) (X.presheaf.stalk (a z))
    (stalkEssFinitePresentation X S f (a z) inferInstance)

end EtaleFlatLocalDescent

/-- The exact pointwise descent proposition for schemes. -/
theorem schemeEtaleFlatLocalDescent : SchemeEtaleFlatLocalDescentStatement.{u} := by
  intro X S T P f g a p H hg hf z hp hur
  have := hg
  have := hf
  have : Flat a := MorphismProperty.of_isPullback (P := @Flat) H.flip hg
  exact EtaleFlatLocalDescent.formallyEtale_stalkMap_of_isPullback H z hp hur

end Langlands.AlgebraicGeometry
