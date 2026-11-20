import Langlands.AlgebraicGeometry.SectionJetNeighborhood
import Langlands.GroupScheme.IdentityJetSeparatedBaseChange
import Langlands.GroupScheme.OpenCellGluing
import Langlands.GroupScheme.FiniteEtaleImage
import Langlands.GroupScheme.HomScheme.AffineTest
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated

/-! # Detection of homomorphism equality on a finite identity jet -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

open Langlands.AlgebraicGeometry (exists_order_of_vanishing_near_section
  fg_ideal_ker_of_locallyOfFinitePresentation)
open Langlands.GroupScheme.HomScheme (baseChange_map_left_fst)

/-- At order `n`, agreement on the identity neighborhood implies equality of the
two fixed homomorphisms after every base change. -/
def DetectsBaseChangeHomEq {S : Scheme.{u}} {K H : GroupScheme S}
    (φ ψ : K ⟶ H) (n : ℕ) : Prop :=
  ∀ (T : Scheme.{u}) (b : T ⟶ S),
    inclusion ((baseChange b).obj K) n ≫ ((baseChange b).map φ).hom.hom.left =
      inclusion ((baseChange b).obj K) n ≫ ((baseChange b).map ψ).hom.hom.left →
    (baseChange b).map φ = (baseChange b).map ψ

private theorem comp_baseChange_eq_iff {S T X : Scheme.{u}} (b : T ⟶ S)
    {K H : GroupScheme S} (φ ψ : K ⟶ H) (a : X ⟶ ((baseChange b).obj K).X.left) :
    a ≫ ((baseChange b).map φ).hom.hom.left = a ≫ ((baseChange b).map ψ).hom.hom.left ↔
      a ≫ pullback.fst K.X.hom b ≫ φ.hom.hom.left =
        a ≫ pullback.fst K.X.hom b ≫ ψ.hom.hom.left := by
  constructor
  · intro h
    simpa only [Category.assoc, baseChange_map_left_fst] using
      congrArg (fun z => z ≫ pullback.fst H.X.hom b) h
  · intro h
    apply pullback.hom_ext
    · simpa only [Category.assoc, baseChange_map_left_fst] using h
    · rw [Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) (((baseChange b).map φ).hom.hom.w.trans
        ((baseChange b).map ψ).hom.hom.w.symm)

set_option maxHeartbeats 950000 in
/-- For two fixed homomorphisms from a smooth separated group over a quasi-compact
base, one identity jet detects equality on every change of base. The source has
geometrically irreducible fibres and the target is separated and locally of finite type. -/
theorem exists_order_detects_baseChange_hom_eq {S : Scheme.{u}} [CompactSpace S]
    {K H : GroupScheme S} [Smooth K.X.hom] [IsSeparated K.X.hom]
    [GeometricallyIrreducible K.X.hom] [IsSeparated H.X.hom] [LocallyOfFiniteType H.X.hom]
    (φ ψ : K ⟶ H) : ∃ n : ℕ, DetectsBaseChangeHomEq φ ψ n := by
  obtain ⟨Z, j, hjClosed, hjFP, hj⟩ :=
    P2MW.S_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated.solution
      H.X.hom K.X.hom φ.hom.hom.left ψ.hom.hom.left φ.hom.hom.w ψ.hom.hom.w
  have : IsClosedImmersion j := hjClosed
  have : LocallyOfFinitePresentation j := hjFP inferInstance
  have : IsClosedImmersion K.identitySection := by
    have : IsClosedImmersion (K.identitySection ≫ K.X.hom) := by
      rw [identitySection_comp]
      infer_instance
    exact IsClosedImmersion.of_comp _ K.X.hom
  obtain ⟨n, hn⟩ := exists_order_of_vanishing_near_section K.X.hom K.identitySection
    K.identitySection_comp j.ker (fg_ideal_ker_of_locallyOfFinitePresentation j)
  refine ⟨n, fun T b hJet => ?_⟩
  let K' := (baseChange b).obj K
  let swap : K'.X.left ≅ pullback b K.X.hom := pullbackSymmetry K.X.hom b
  let p : K'.X.left ⟶ K.X.left := pullback.fst K.X.hom b
  let q := pullback.snd b K.X.hom
  have hswap : swap.inv ≫ p = q := pullbackSymmetry_inv_comp_fst _ _
  obtain ⟨a, ha⟩ := (hj (inclusion K' n ≫ p)).mp (by
    simpa only [Category.assoc] using (comp_baseChange_eq_iff b φ ψ (inclusion K' n)).mp hJet)
  have hKer : j.ker.comap p ≤ ideal K' n := by
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    have hki : (inclusion K' n).ker = ideal K' n := Scheme.IdealSheafData.ker_subschemeι _
    rw [← hki, Scheme.IdealSheafData.map_ker, ← ha]
    exact Scheme.Hom.le_ker_comp _ _
  have hKer' : j.ker.comap q ≤ (K.identitySection.ker ^ (n + 1)).comap q := by
    have h := Scheme.IdealSheafData.comap_mono swap.inv hKer
    change (j.ker.comap p).comap swap.inv ≤ (ideal K' n).comap swap.inv at h
    rw [← ideal_baseChange_of_separated K b n, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hswap] at h
    exact h
  let eT : T ⟶ pullback b K.X.hom := pullback.lift (𝟙 T) (b ≫ K.identitySection)
    (by rw [Category.id_comp, Category.assoc, K.identitySection_comp, Category.comp_id])
  have heT : eT = K'.identitySection ≫ swap.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
      exact (pullback.lift_fst _ _ _).trans K'.identitySection_comp.symm
    · rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
      exact (pullback.lift_snd _ _ _).trans (identitySection_baseChange_fst b K).symm
  choose V hV hJV using hn T b hKer'
  let W : (pullback b K.X.hom).Opens := ⨆ t, V t
  have hW : Set.range eT ⊆ W := by
    rintro _ ⟨t, rfl⟩
    exact (le_iSup V t) (hV t)
  have hEq : W.ι ≫ q ≫ φ.hom.hom.left = W.ι ≫ q ≫ ψ.hom.hom.left := by
    apply Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover V)
    intro t
    change Scheme.homOfLE _ (le_iSup V t) ≫ W.ι ≫ q ≫ φ.hom.hom.left =
      Scheme.homOfLE _ (le_iSup V t) ≫ W.ι ≫ q ≫ ψ.hom.hom.left
    rw [Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]
    simpa only [Category.assoc] using (hj ((V t).ι ≫ q)).mpr
      ⟨IsClosedImmersion.lift j _ (hJV t), IsClosedImmersion.lift_fac j _ (hJV t)⟩
  let A : Over T := Over.mk ((W.ι ≫ swap.inv) ≫ K'.X.hom)
  let k : A ⟶ K'.X := Over.homMk (W.ι ≫ swap.inv) rfl
  have : IsOpenImmersion k.left := inferInstanceAs (IsOpenImmersion (W.ι ≫ swap.inv))
  have heRange : Set.range η[K'.X].left ⊆ Set.range k.left := by
    rintro _ ⟨t, rfl⟩
    refine ⟨⟨eT t, hW (Set.mem_range_self t)⟩, ?_⟩
    change (eT ≫ swap.inv) t = K'.identitySection t
    rw [heT, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let e := FiniteEtaleImage.liftOver k η[K'.X] heRange
  have he : e ≫ k = η[K'.X] := FiniteEtaleImage.liftOver_fac _ _ _
  have : Smooth K'.X.hom := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  have : GeometricallyIrreducible K'.X.hom :=
    MorphismProperty.pullback_snd (P := @GeometricallyIrreducible) _ _ inferInstance
  apply CellGluing.hom_ext_cell e he
  apply Over.OverMorphism.ext
  exact (comp_baseChange_eq_iff b φ ψ k.left).mpr (by
    change (W.ι ≫ swap.inv) ≫ p ≫ φ.hom.hom.left =
      (W.ι ≫ swap.inv) ≫ p ≫ ψ.hom.hom.left
    have hsq {X : Scheme.{u}} (f : K.X.left ⟶ X) : swap.inv ≫ p ≫ f = q ≫ f := by
      rw [← Category.assoc, hswap]
    simpa only [Category.assoc, hsq] using hEq)

end Langlands.GroupScheme.IdentityJet
