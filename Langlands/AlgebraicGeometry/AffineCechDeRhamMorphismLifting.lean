import Langlands.AlgebraicGeometry.AffineCechDeRhamMorphismCorrection

/-! # Global morphisms from compatible corrected affine pullbacks -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq (inter inter_le_apply inter_le_comp)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineCechDeRham

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  {U : Scheme.AffineOpenCover.{u} X} {V : Scheme.AffineOpenCover.{u} Y}

private abbrev singleton {ι : Type u} (i : ι) : Fin 1 → ι := fun _ => i

private lemma singleton_cover (U : Scheme.AffineOpenCover.{u} X) :
    IsOpenCover (fun i => inter (coverOpens U) (singleton i)) := by
  have he (i : U.I₀) : inter (coverOpens U) (singleton i) = coverOpens U i :=
    Langlands.Cohomology.Cech.inter_const_one i
  exact .mk (by simp only [he]; exact U.openCover.iSup_opensRange)

private lemma fromSpec_over {W : X.Opens} (hW : IsAffineOpen W) :
    hW.fromSpec ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R ((sectionAlgebras f).obj (op W)))) := by
  let S := Spec (CommRingCat.of R)
  let T : S.Opens := ⊤
  change hW.fromSpec ≫ f = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE T W le_top)
  rw [Spec.map_comp]
  have e := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top S) hW (U := T) le_top
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  exact e.symm

variable [IsSeparated f] [IsSeparated g] (I : Ideal R)
  (m : quotientReduction f I ⟶ Y) (β : U.I₀ → V.I₀)
  (hβ : ∀ i, quotientReductionMap f I ⁻¹ᵁ coverOpens U i ≤ m ⁻¹ᵁ coverOpens V (β i))

private abbrev chartOpen (U : Scheme.AffineOpenCover.{u} X) {p : ℕ}
    (τ : Fin (p + 1) → U.I₀) := inter (coverOpens U) τ

omit [IsSeparated f] in
include hβ in
private lemma singleton_preimage_le (i : U.I₀) :
    quotientReductionMap f I ⁻¹ᵁ chartOpen U (singleton i) ≤
      m ⁻¹ᵁ chartOpen V (singleton (β i)) := by
  change quotientReductionMap f I ⁻¹ᵁ Langlands.Cohomology.Cech.inter (coverOpens U) (singleton i) ≤
    m ⁻¹ᵁ Langlands.Cohomology.Cech.inter (coverOpens V) (singleton (β i))
  rw [Langlands.Cohomology.Cech.inter_const_one, Langlands.Cohomology.Cech.inter_const_one]
  exact hβ i

private lemma singleton_reduction_cover (U : Scheme.AffineOpenCover.{u} X) {Z : Scheme.{u}}
    (r : Z ⟶ X) : IsOpenCover fun i => r ⁻¹ᵁ chartOpen U (singleton i) := by
  exact (singleton_cover U).comap ⟨r, r.continuous⟩

/-- Compatible algebra maps on the affine tuple intersections glue to a
morphism over the base. If the vertex maps reduce to the given morphism,
so does the glued morphism. -/
theorem exists_lift_of_compatible_sections
    (s : ∀ {p : ℕ} (τ : Fin (p + 1) → U.I₀), Fin (p + 1) →
      tupleSections g V (β ∘ τ) →ₐ[R] tupleSections f U τ)
    (hs : ∀ (τ : Fin 2 → U.I₀) (k : Fin 2),
      (restrictSections f U τ (singleton k)).comp (s (τ ∘ singleton k) 0) =
        (s τ k).comp (restrictSections g V (β ∘ τ) (singleton k)))
    (hp : ∀ τ : Fin 2 → U.I₀, s τ 1 = s τ 0)
    (hr : ∀ i : U.I₀, let r := quotientReductionMap f I
      let W := chartOpen U (singleton i)
      let T := chartOpen V (singleton (β i))
      CommRingCat.ofHom (s (singleton i) 0).toRingHom ≫ r.appLE W (r ⁻¹ᵁ W) le_rfl =
        m.appLE T (r ⁻¹ᵁ W) (singleton_preimage_le I m β hβ i)) :
    ∃ γ : X ⟶ Y, γ ≫ g = f ∧ quotientReductionMap f I ≫ γ = m := by
  let P := Scheme.AffineOpenCover.ofIsOpenCover (fun i => chartOpen U (singleton i))
    (singleton_cover U) (fun i => isAffineOpen_inter f U (singleton i))
  let sourceChart {p : ℕ} (τ : Fin (p + 1) → U.I₀) := isAffineOpen_inter f U τ
  let targetChart {p : ℕ} (τ : Fin (p + 1) → U.I₀) := isAffineOpen_inter g V (β ∘ τ)
  let piece (i : U.I₀) : Spec Γ(X, chartOpen U (singleton i)) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (s (singleton i) 0).toRingHom) ≫ (targetChart (singleton i)).fromSpec
  have hpiece (τ : Fin 2 → U.I₀) (k : Fin 2) :
      Spec.map (CommRingCat.ofHom (restrictSections f U τ (singleton k)).toRingHom) ≫
        piece (τ k) = Spec.map (CommRingCat.ofHom (s τ k).toRingHom) ≫ (targetChart τ).fromSpec := by
    let x₀ := CommRingCat.ofHom (restrictSections f U τ (singleton k)).toRingHom
    let y₀ := CommRingCat.ofHom (restrictSections g V (β ∘ τ) (singleton k)).toRingHom
    let a := CommRingCat.ofHom (s (τ ∘ singleton k) 0).toRingHom
    let b := CommRingCat.ofHom (s τ k).toRingHom
    have hab : a ≫ x₀ = y₀ ≫ b := by
      ext x
      exact DFunLike.congr_fun (hs τ k) x
    change Spec.map x₀ ≫ Spec.map a ≫ (targetChart (τ ∘ singleton k)).fromSpec = _
    rw [← Spec.map_comp_assoc, hab, Spec.map_comp, Category.assoc]
    exact congrArg (Spec.map b ≫ ·)
      (IsAffineOpen.map_fromSpec (targetChart (τ ∘ singleton k)) (targetChart τ)
        (homOfLE (inter_le_comp (β ∘ τ) (singleton k))).op)
  have hglue (i j : U.I₀) :
      pullback.fst (P.f i) (P.f j) ≫ piece i = pullback.snd (P.f i) (P.f j) ≫ piece j := by
    let τ : Fin 2 → U.I₀ := ![i, j]
    have he : chartOpen U τ = chartOpen U (singleton i) ⊓ chartOpen U (singleton j) := by
      change Langlands.Cohomology.Cech.inter (coverOpens U) ![i, j] =
        Langlands.Cohomology.Cech.inter (coverOpens U) (singleton i) ⊓
          Langlands.Cohomology.Cech.inter (coverOpens U) (singleton j)
      rw [Langlands.Cohomology.Cech.inter_two, Langlands.Cohomology.Cech.inter_const_one,
        Langlands.Cohomology.Cech.inter_const_one]
    let a := pullback.fst (P.f i) (P.f j) ≫ P.f i
    have ha : Set.range a ⊆ Set.range (sourceChart τ).fromSpec := by
      rw [IsAffineOpen.range_fromSpec]
      change Set.range a ⊆ (chartOpen U τ : Set X)
      rw [he]
      rintro _ ⟨z, rfl⟩
      change a z ∈ (chartOpen U (singleton i) : Set X) ∧
        a z ∈ (chartOpen U (singleton j) : Set X)
      refine ⟨?_, ?_⟩
      · rw [← IsAffineOpen.range_fromSpec (sourceChart (singleton i))]
        exact ⟨pullback.fst (P.f i) (P.f j) z, rfl⟩
      · rw [← IsAffineOpen.range_fromSpec (sourceChart (singleton j))]
        exact ⟨pullback.snd (P.f i) (P.f j) z,
          congrArg (fun b : pullback (P.f i) (P.f j) ⟶ X => b z) pullback.condition.symm⟩
    let t := IsOpenImmersion.lift (sourceChart τ).fromSpec a ha
    have ht := IsOpenImmersion.lift_fac (sourceChart τ).fromSpec a ha
    have hfst : t ≫ Spec.map (CommRingCat.ofHom (restrictSections f U τ (singleton 0)).toRingHom) =
        pullback.fst (P.f i) (P.f j) := by
      apply (cancel_mono (P.f i)).1
      rw [Category.assoc]
      change t ≫ Spec.map (X.presheaf.map (homOfLE (inter_le_comp τ (singleton 0))).op) ≫
        (sourceChart (singleton i)).fromSpec = _
      rw [IsAffineOpen.map_fromSpec (sourceChart (singleton i)) (sourceChart τ)
        (homOfLE (inter_le_comp τ (singleton 0))).op]
      exact ht
    have hsnd : t ≫ Spec.map (CommRingCat.ofHom (restrictSections f U τ (singleton 1)).toRingHom) =
        pullback.snd (P.f i) (P.f j) := by
      apply (cancel_mono (P.f j)).1
      rw [Category.assoc]
      change t ≫ Spec.map (X.presheaf.map (homOfLE (inter_le_comp τ (singleton 1))).op) ≫
        (sourceChart (singleton j)).fromSpec = _
      rw [IsAffineOpen.map_fromSpec (sourceChart (singleton j)) (sourceChart τ)
        (homOfLE (inter_le_comp τ (singleton 1))).op]
      exact ht.trans pullback.condition
    change _ ≫ piece (τ 0) = _ ≫ piece (τ 1)
    rw [← hfst, ← hsnd, Category.assoc, Category.assoc, hpiece τ 0, hpiece τ 1, hp τ]
  let γ := P.openCover.glueMorphisms piece hglue
  have hγ (i : U.I₀) : (sourceChart (singleton i)).fromSpec ≫ γ = piece i :=
    P.openCover.ι_glueMorphisms piece hglue i
  refine ⟨γ, ?_, ?_⟩
  · apply P.openCover.hom_ext
    intro i
    change U.I₀ at i
    change (sourceChart (singleton i)).fromSpec ≫ γ ≫ g =
      (sourceChart (singleton i)).fromSpec ≫ f
    rw [← Category.assoc, hγ]
    dsimp only [piece]
    rw [Category.assoc, fromSpec_over, fromSpec_over, ← Spec.map_comp]
    apply congrArg Spec.map
    apply ConcreteCategory.hom_ext
    exact (s (singleton i) 0).commutes
  · let r := quotientReductionMap f I
    let Q := Scheme.AffineOpenCover.ofIsOpenCover (fun i => r ⁻¹ᵁ chartOpen U (singleton i))
      (singleton_reduction_cover U r) (fun i => (sourceChart (singleton i)).preimage r)
    apply Q.openCover.hom_ext
    intro i
    change U.I₀ at i
    let W := chartOpen U (singleton i)
    let T := chartOpen V (singleton (β i))
    let W₀ := r ⁻¹ᵁ W
    let hw := (sourceChart (singleton i)).preimage r
    let ht := targetChart (singleton i)
    change hw.fromSpec ≫ r ≫ γ = hw.fromSpec ≫ m
    rw [← Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec r (sourceChart (singleton i))
      hw (U := W) (V := W₀) le_rfl, Category.assoc, hγ]
    dsimp only [piece]
    rw [← Spec.map_comp_assoc, hr i, IsAffineOpen.SpecMap_appLE_fromSpec m ht hw (U := T) (V := W₀)
      (singleton_preimage_le I m β hβ i)]

section Reduction

variable (hI : I * I = ⊥) [Smooth f] [Smooth g] [Finite U.I₀] [Finite V.I₀]
  (hm : m ≫ g = quotientReductionMap f I ≫ f)

omit [IsSeparated g] [Smooth f] [Smooth g] [Finite U.I₀] [Finite V.I₀] in
private lemma localSections_reduce [Surjective (quotientReductionMap f I)]
    (ℓ : ∀ i, (coverOpens U i).toScheme ⟶ Y)
    (hℓ : ∀ i, ℓ i ≫ g = (coverOpens U i).ι ≫ f)
    (hred : ∀ i, (quotientReductionMap f I).resLE (coverOpens U i)
      (quotientReductionMap f I ⁻¹ᵁ coverOpens U i) le_rfl ≫ ℓ i =
        (quotientReductionMap f I ⁻¹ᵁ coverOpens U i).ι ≫ m)
    (i : U.I₀) :
    let r := quotientReductionMap f I
    let W := chartOpen U (singleton i)
    let T := chartOpen V (singleton (β i))
    let L := LocalPullbacks.ofLocalMorphisms r m β ℓ hℓ hred hβ I
      (fun W hW => (quotientReductionMap_appLE f I W hW).2)
    CommRingCat.ofHom (L.sections (singleton i) 0).toRingHom ≫ r.appLE W (r ⁻¹ᵁ W) le_rfl =
      m.appLE T (r ⁻¹ᵁ W) (singleton_preimage_le I m β hβ i) := by
  let r := quotientReductionMap f I
  let W := chartOpen U (singleton i)
  let W₀ := r ⁻¹ᵁ W
  let T := chartOpen V (singleton (β i))
  let A := coverOpens U i
  let e : W ≤ A := inter_le_apply (singleton i) 0
  let q := X.homOfLE e ≫ ℓ i
  have hredW : r.resLE W W₀ le_rfl ≫ q = W₀.ι ≫ m := by
    change r.resLE W W₀ le_rfl ≫ X.homOfLE e ≫ ℓ i = W₀.ι ≫ m
    have hw : r.resLE W W₀ le_rfl ≫ X.homOfLE e =
        (quotientReduction f I).homOfLE (r.preimage_mono e) ≫ r.resLE A (r ⁻¹ᵁ A) le_rfl := by
      rw [Scheme.Hom.resLE_map, Scheme.Hom.map_resLE]
    rw [← Category.assoc, hw, Category.assoc, hred, ← Category.assoc, Scheme.homOfLE_ι]
  have ht := singleton_preimage_le I m β hβ i
  have hW : ⊤ ≤ W₀.ι ⁻¹ᵁ W₀ := by rw [Scheme.Opens.ι_preimage_self]
  have ht' : ⊤ ≤ (W₀.ι ≫ m) ⁻¹ᵁ T := hW.trans (W₀.ι.preimage_mono ht)
  have hs : (r.resLE W W₀ le_rfl).appTop ≫ W₀.topIso.hom =
      W.topIso.hom ≫ r.appLE W W₀ le_rfl := (arrowResLEAppIso r W W₀ le_rfl).hom.w.symm
  change (q.appLE T ⊤ _ ≫ W.topIso.hom) ≫ r.appLE W W₀ le_rfl = m.appLE T W₀ ht
  rw [Category.assoc, ← hs, ← Category.assoc,
    show (r.resLE W W₀ le_rfl).appTop = (r.resLE W W₀ le_rfl).appLE ⊤ ⊤ le_top from
      (r.resLE W W₀ le_rfl).app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]
  have heq {a b : W₀.toScheme ⟶ Y} (hab : a = b)
      (ha : ⊤ ≤ a ⁻¹ᵁ T) (hb : ⊤ ≤ b ⁻¹ᵁ T) : a.appLE T ⊤ ha = b.appLE T ⊤ hb := by
    subst b
    rfl
  rw [heq hredW _ ht', ← Scheme.Hom.appLE_comp_appLE W₀.ι m T W₀ ⊤ ht hW, Category.assoc]
  have hi : W₀.ι.appLE W₀ ⊤ hW = W₀.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv, eqToHom_op]
    rfl
  rw [hi, Iso.inv_hom_id, Category.comp_id]

/-- Hodge preservation gives a lift when compatible closed target forms are
bases on the affine intersections and the reduced source has only constant
functions. -/
theorem exists_lift_of_reductionPullbackH1_maps_hodgeF1 {κ : Type u} [Fintype κ]
    (e : ClosedFormBasis g V κ)
    (hconst : Function.Surjective (pullback.snd f (quotientBaseMap I)).appTop.hom)
    (h : ∀ z ∈ hodgeF1 g V, reductionPullbackH1 f I hI m hm β hβ z ∈ hodgeF1 f U) :
    ∃ γ : X ⟶ Y, γ ≫ g = f ∧ quotientReductionMap f I ≫ γ = m := by
  classical
  let r := quotientReductionMap f I
  let : Surjective r := quotientReductionMap_surjective f I hI
  choose ℓ hℓ hred using fun i : U.I₀ => exists_lift_on_affineOpen f I hI m hm
    (coverOpens U i) (isAffineOpen_opensRange (U.f i))
  let L := LocalPullbacks.ofLocalMorphisms r m β ℓ hℓ hred hβ I
    (fun W hW => (quotientReductionMap_appLE f I W hW).2)
  have heq : reductionPullbackH1 f I hI m hm β hβ = L.pullbackH1 hI :=
    reductionPullbackH1_eq_of_localMorphisms f I hI m hm β hβ ℓ hℓ hred
  rw [heq] at h
  have primitive (k : κ) : ∃ a : C0 f U,
      (∀ σ : Fin 1 → U.I₀, a σ ∈ I.map (algebraMap R (tupleSections f U σ))) ∧
      ∀ τ : Fin 2 → U.I₀, cechD U (functions f) 0 a τ = L.contraction hI τ 1 0 (e.basis (β ∘ τ) k) := by
    obtain ⟨a, ha⟩ := L.exists_functionPrimitive_of_pullback_closedForm_mem_hodgeF1 hI (e.forms k)
      (h _ ⟨e.forms k, rfl⟩)
    have ha' : ∀ τ : Fin 2 → U.I₀,
        cechD U (functions f) 0 a τ ∈ I.map (algebraMap R (tupleSections f U τ)) := by
      intro τ
      rw [ha]
      exact RelativeForms.contractDifferenceOne_mem _ _ hI (L.congruent τ 1 0) _
    obtain ⟨b, hb, hI'⟩ := exists_ideal_primitive_of_cechD_mem f U I hconst a ha'
    exact ⟨b, hI', fun τ => by rw [hb, ha, e.basis_apply (β ∘ τ) 1 k]⟩
  choose a ha hd using primitive
  let s {p : ℕ} (τ : Fin (p + 1) → U.I₀) (i : Fin (p + 1)) :=
    L.correctedSections hI e a ha τ i
  apply exists_lift_of_compatible_sections I m β hβ s
  · exact fun τ j => L.restrict_correctedSections hI e a ha τ (singleton j) 0
  · exact L.correctedSections_eq_of_primitives hI e a ha hd
  · intro i
    let σ := singleton i
    let W := chartOpen U σ
    let W₀ := r ⁻¹ᵁ W
    let ρ := r.appLE W W₀ le_rfl
    change CommRingCat.ofHom (L.correctedSections hI e a ha σ 0).toRingHom ≫ ρ = _
    rw [← localSections_reduce I m β hβ ℓ hℓ hred i]
    ext x
    change ρ.hom (L.correctedSections hI e a ha σ 0 x) = ρ.hom (L.sections σ 0 x)
    have hx := L.sections_sub_correctedSections_mem hI e a ha σ 0 x
    change L.sections σ 0 x - L.correctedSections hI e a ha σ 0 x ∈
      I.map (algebraMap R (tupleSections f U σ)) at hx
    rw [← (quotientReductionMap_appLE f I W (isAffineOpen_inter f U σ)).2] at hx
    change ρ.hom (L.sections σ 0 x - L.correctedSections hI e a ha σ 0 x) = 0 at hx
    exact (sub_eq_zero.mp ((map_sub ρ.hom _ _).symm.trans hx)).symm

end Reduction

end Langlands.AlgebraicGeometry.AffineCechDeRham
