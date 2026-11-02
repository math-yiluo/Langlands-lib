import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisAffineDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeHelpers
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineOpenExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart
import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldSchemePoints
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedDenseAffineOpenReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.LFTAffineOpen

/-! # Affine open charts through field points of a commutative group space

Let `G` be a presheaf of commutative groups on schemes over a field `k` whose underlying
presheaf is an fppf sheaf with closed-immersion diagonal and an etale atlas locally of
finite type. Every point of `G` with values in a finite extension of `k` lies in an affine
open subfunctor. The proof uses the dense affine open statement on a union of translates
over a normal extension, a Galois-stable intersection of translates, and the descent of
invariant affine opens.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open OpenSubfunctorLifting AffineOpenSubfunctors CoproductChart
open Langlands.AlgebraicGeometry.Picard.DualNumberDouble (specOverMap specOverMap_left)


attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange

variable {k : Type u} [Field k]

local notation "𝕊" => Spec (CommRingCat.of k)

/-- Step 1: inside a dense affine open of the union of finitely many translates of an
etale chart, one field point of the chart has all its translates. -/
theorem exists_affine_containing_translates
    (hS1 : SeparatedDenseAffineOpenLFTProp.{u})
    (G : (Over 𝕊)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology 𝕊) (G ⋙ forget AddCommGrpCat))
    (hd : IsClosedImmersion (Limits.diag (G ⋙ forget AddCommGrpCat)))
    (L : Type u) [Field L] [Algebra k L]
    {U₀ : Over 𝕊} [IsAffine U₀.left] [LocallyOfFiniteType U₀.hom] [Nonempty U₀.left]
    (a₀ : (schemeYoneda 𝕊).obj U₀ ⟶ extProd (G ⋙ forget AddCommGrpCat) (specOver k L))
    (ha₀ : IsEtale a₀) {Γ : Type u} [Finite Γ] (gL : G.obj (op (specOver k L)))
    (ψ : Γ → (specOver k L ⟶ specOver k L)) :
    ∃ A : Subfunctor (extProd (G ⋙ forget AddCommGrpCat) (specOver k L)), IsLFTAffineOpen A ∧
      ∃ (L' : Type u) (_ : Field L') (_ : Algebra k L'), FiniteDimensional k L' ∧
        Normal k L' ∧ ∃ ρ : specOver k L' ⟶ U₀, ∀ τ : Γ,
          (translate G (G.map (ψ τ).op gL)).app _ (a₀.app _ ⟨ρ⟩) ∈
            A.obj (op (specOver k L')) := by
  let F := G ⋙ forget AddCommGrpCat
  let Λ := specOver k L
  let P := extProd F Λ
  have hFL : CategoryTheory.Presheaf.IsSheaf (fppfTopology 𝕊) P := extProd.isSheaf hF
  have hdL : IsClosedImmersion (Limits.diag P) := extProd.isClosedImmersion_diag hd
  -- the coproduct chart
  let V := sigmaOver (fun _ : Γ ↦ U₀)
  let codiag : V ⟶ U₀ := sigmaOverDesc (fun _ : Γ ↦ U₀) (fun _ ↦ 𝟙 U₀)
  let z₀ := uliftYonedaEquiv a₀
  let φ : V ⟶ Λ := sigmaOverDesc (fun _ : Γ ↦ U₀) (fun τ ↦ z₀.2.down ≫ ψ τ)
  let bpt : P.obj (op V) :=
    ((show G.obj (op V) from F.map codiag.op z₀.1) + G.map φ.op gL, ULift.up (codiag ≫ z₀.2.down))
  let b : (schemeYoneda 𝕊).obj V ⟶ P := uliftYonedaEquiv.symm bpt
  have hb : ∀ τ, (schemeYoneda 𝕊).map (sigmaOverι (fun _ : Γ ↦ U₀) τ) ≫ b =
      a₀ ≫ translate G (G.map (ψ τ).op gL) := by
    intro τ
    have h1 : (schemeYoneda 𝕊).map (sigmaOverι (fun _ : Γ ↦ U₀) τ) ≫ b =
        uliftYonedaEquiv.symm (P.map (sigmaOverι (fun _ : Γ ↦ U₀) τ).op bpt) := by
      rw [uliftYonedaEquiv_symm_map]
      rfl
    have h2 : a₀ ≫ translate G (G.map (ψ τ).op gL) =
        uliftYonedaEquiv.symm ((translate G (G.map (ψ τ).op gL)).app _ z₀) := by
      rw [← uliftYonedaEquiv_symm_comp, Equiv.symm_apply_apply]
    rw [h1, h2]
    congr 1
    refine Prod.ext ?_ ?_
    · change G.map (sigmaOverι (fun _ : Γ ↦ U₀) τ).op ((show G.obj (op V) from F.map codiag.op z₀.1) +
          G.map φ.op gL) = (show G.obj (op U₀) from z₀.1) + G.map z₀.2.down.op (G.map (ψ τ).op gL)
      rw [map_add]
      congr 1
      · change (G.map codiag.op ≫ G.map (sigmaOverι (fun _ : Γ ↦ U₀) τ).op) z₀.1 = z₀.1
        rw [← G.map_comp, ← op_comp, CoproductChart.ι_desc, op_id, G.map_id]
        rfl
      · change (G.map φ.op ≫ G.map (sigmaOverι (fun _ : Γ ↦ U₀) τ).op) gL =
          (G.map (ψ τ).op ≫ G.map z₀.2.down.op) gL
        rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, CoproductChart.ι_desc]
    · change ULift.up (sigmaOverι (fun _ : Γ ↦ U₀) τ ≫ codiag ≫ z₀.2.down) = z₀.2
      rw [CoproductChart.ι_desc_assoc, Category.id_comp]
  have hbe : IsEtale b := by
    apply isEtale_of_forall_ι _ hdL.representable
    intro τ
    rw [hb τ]
    exact ha₀.comp_iso (translateIso G _)
  -- the sheafified image and the dense affine open
  let Q := (Subfunctor.range b).sheafify (fppfTopology 𝕊)
  have hQsh := OpenSubfunctorImages.sheafify_range_isSheaf b hbe hFL
  let Qs : FppfSheaf 𝕊 := ⟨Q.toFunctor, hQsh⟩
  have hQalg := OpenSubfunctorImages.sheafify_range_isAlgebraicSpace b hbe hFL hdL
  have hQd : IsClosedImmersion (Limits.diag Q.toFunctor) :=
    OpenSubfunctorImages.isClosedImmersion_diag_subfunctor hdL Q
  have hQo : IsOpenImmersion Q.ι := OpenSubfunctorImages.sheafify_range_open b hbe
  let b' := Subfunctor.toRangeSheafify (fppfTopology 𝕊) b
  have hb'e := OpenSubfunctorImages.toRangeSheafify_isEtale b hbe
  have hb's := OpenSubfunctorImages.toRangeSheafify_isSurjective b hbe
  have hVlft : LocallyOfFiniteType V.hom := inferInstance
  obtain ⟨VA, WA, i, p, bb, hVA, hVAlft, hi, hpb, hdense⟩ :=
    hS1 k Qs hQalg hQd V b' hb'e hb's inferInstance hVlft
  let A := Subfunctor.range (i ≫ Q.ι)
  have hA : IsLFTAffineOpen A := isLFTAffineOpen_range hVAlft _ (hi.comp' hQo)
  refine ⟨A, hA, ?_⟩
  -- a closed point of the chart all of whose translates land in `A`
  have hp : _root_.AlgebraicGeometry.IsOpenImmersion p.left := hi.projection b' bb p hpb
  let Ω : Γ → Set U₀.left := fun τ ↦ (sigmaOverι (fun _ : Γ ↦ U₀) τ).left ⁻¹' Set.range p.left
  have hΩo : ∀ τ, IsOpen (Ω τ) := fun τ ↦
    p.left.isOpenEmbedding.isOpen_range.preimage (sigmaOverι (fun _ : Γ ↦ U₀) τ).left.continuous
  have hΩd : ∀ τ, Dense (Ω τ) := fun τ ↦
    hdense.preimage (sigmaOverι (fun _ : Γ ↦ U₀) τ).left.isOpenEmbedding.isOpenMap
  have hΩ : IsOpen (⋂ τ, Ω τ) := isOpen_iInter_of_finite hΩo
  have hΩne : (⋂ τ, Ω τ).Nonempty := (dense_iInter_of_isOpen_finite hΩo hΩd).nonempty
  obtain ⟨w, hwΩ, hw⟩ := FieldSchemePoints.exists_closed_mem_open U₀.hom hΩ hΩne
  let L₂ := U₀.left.residueField w
  let := FieldSchemePoints.residueFieldAlgebra U₀.hom w
  have : FiniteDimensional k L₂ := FieldSchemePoints.residueField_finiteDimensional U₀.hom w hw
  obtain ⟨L', _, _, hL'fin, hL'norm, ⟨ι₂⟩⟩ := exists_finite_normal_extension (k := k) L₂
  refine ⟨L', inferInstance, inferInstance, hL'fin, hL'norm, ?_⟩
  let wpt : specOver k L₂ ⟶ U₀ := Over.homMk (U₀.left.fromSpecResidueField w) (by
    change U₀.left.fromSpecResidueField w ≫ U₀.hom = Spec.map (CommRingCat.ofHom
      (Spec.preimage (U₀.left.fromSpecResidueField w ≫ U₀.hom)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage])
  let ρ : specOver k L' ⟶ U₀ := specOverMap ι₂ ≫ wpt
  refine ⟨ρ, fun τ ↦ ?_⟩
  have hrange : Set.range (ρ ≫ sigmaOverι (fun _ : Γ ↦ U₀) τ).left ⊆ Set.range p.left := by
    rintro _ ⟨y, rfl⟩
    have hy : (specOverMap ι₂ ≫ wpt).left y = w := by
      have : (specOverMap ι₂ ≫ wpt).left y ∈ Set.range (U₀.left.fromSpecResidueField w) :=
        ⟨(specOverMap ι₂).left y, rfl⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have hw' := Set.mem_iInter.mp hwΩ τ
    change (sigmaOverι (fun _ : Γ ↦ U₀) τ).left ((specOverMap ι₂ ≫ wpt).left y) ∈ Set.range p.left
    rw [hy]
    exact hw'
  let l := _root_.AlgebraicGeometry.IsOpenImmersion.lift p.left (ρ ≫ sigmaOverι (fun _ : Γ ↦ U₀) τ).left hrange
  have hl : l ≫ p.left = (ρ ≫ sigmaOverι (fun _ : Γ ↦ U₀) τ).left :=
    _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  let lo : specOver k L' ⟶ WA := Over.homMk l (by
    rw [← Over.w p, ← Category.assoc, hl, Over.w])
  have hlo : lo ≫ p = ρ ≫ sigmaOverι (fun _ : Γ ↦ U₀) τ := Over.OverMorphism.ext hl
  have hval : (translate G (G.map (ψ τ).op gL)).app _ (a₀.app _ ⟨ρ⟩) =
      b.app _ ⟨ρ ≫ sigmaOverι (fun _ : Γ ↦ U₀) τ⟩ := by
    have := congrArg (fun f : (schemeYoneda 𝕊).obj U₀ ⟶ P ↦ f.app (op (specOver k L')) ⟨ρ⟩)
      (hb τ)
    exact this.symm
  rw [hval]
  refine ⟨bb.app _ ⟨lo⟩, ?_⟩
  have hsq := congrArg (fun f : (schemeYoneda 𝕊).obj WA ⟶ Q.toFunctor ↦
    (f.app (op (specOver k L')) ⟨lo⟩).1) hpb.w
  refine hsq.trans ?_
  change b.app _ ⟨lo ≫ p⟩ = _
  rw [hlo]

/-- Step 2: a Galois-stable affine open of `F × Spec L'` containing a given point. -/
theorem exists_galois_stable_affine
    (G : (Over 𝕊)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hd : IsClosedImmersion (Limits.diag (G ⋙ forget AddCommGrpCat)))
    {L : Type u} [Field L] [Algebra k L] [Normal k L]
    {A : Subfunctor (extProd (G ⋙ forget AddCommGrpCat) (specOver k L))} (hA : IsLFTAffineOpen A)
    {L' : Type u} [Field L'] [Algebra k L'] [FiniteDimensional k L'] [Normal k L']
    (j : L →ₐ[k] L') (q' : G.obj (op (specOver k L'))) (gL : G.obj (op (specOver k L)))
    (hmem : ∀ τ : L ≃ₐ[k] L,
      (((show G.obj (op (specOver k L')) from q') +
          G.map (specOverMap j).op (G.map (specOverMap τ.toAlgHom).op gL),
        ULift.up (specOverMap j)) : (extProd (G ⋙ forget AddCommGrpCat) (specOver k L)).obj
          (op (specOver k L'))) ∈ A.obj (op (specOver k L'))) :
    ∃ W : Subfunctor (extProd (G ⋙ forget AddCommGrpCat) (specOver k L')), IsLFTAffineOpen W ∧
      (∀ (σ : L' ≃ₐ[k] L') (T : (Over 𝕊)ᵒᵖ)
        (z : (extProd (G ⋙ forget AddCommGrpCat) (specOver k L')).obj T), z ∈ W.obj T →
          (extProd.mapRight (specOverMap σ.toAlgHom)).app T z ∈ W.obj T) ∧
      (((show (G ⋙ forget AddCommGrpCat).obj (op (specOver k L')) from
          G.map (specOverMap j).op gL), ULift.up (𝟙 _)) :
        (extProd (G ⋙ forget AddCommGrpCat) (specOver k L')).obj (op (specOver k L'))) ∈
          W.obj (op (specOver k L')) := by
  classical
  let F := G ⋙ forget AddCommGrpCat
  let Λ' := specOver k L'
  have hdL' : IsClosedImmersion (Limits.diag (extProd F Λ')) := extProd.isClosedImmersion_diag hd
  let A' := A.preimage (extProd.mapRight (specOverMap j))
  have hA' : IsLFTAffineOpen A' := hA.preimage_mapRight (specOverMap j)
  let e : (L' ≃ₐ[k] L') → (extProd F Λ' ≅ extProd F Λ') := fun σ ↦
    extProd.mapRightIso (specIso σ) ≪≫ translateIso G q'
  let W := ⨅ σ, A'.preimage (e σ).hom
  have hW : IsLFTAffineOpen W := IsLFTAffineOpen.iInf_preimage_iso hdL' (AlgEquiv.refl) e hA'
  have hmemW : ∀ (T : (Over 𝕊)ᵒᵖ) (z : (extProd F Λ').obj T), z ∈ W.obj T ↔
      ∀ σ, (extProd.mapRight (specOverMap j)).app T ((e σ).hom.app T z) ∈ A.obj T := by
    intro T z
    simp only [W, Subfunctor.iInf_obj, Set.mem_iInter]
    rfl
  have he : ∀ σ (T : (Over 𝕊)ᵒᵖ) (z : (extProd F Λ').obj T),
      (e σ).hom.app T z = ((show G.obj T from z.1) + G.map (z.2.down ≫ specOverMap σ.toAlgHom).op q',
        ULift.up (z.2.down ≫ specOverMap σ.toAlgHom)) := fun _ _ _ ↦ rfl
  refine ⟨W, hW, ?_, ?_⟩
  · intro σ₀ T z hz
    rw [hmemW] at hz ⊢
    intro σ
    have hsp : specOverMap (σ.trans σ₀).toAlgHom = specOverMap σ₀.toAlgHom ≫ specOverMap σ.toAlgHom := by
      rw [← specMap_comp]
      rfl
    have heq : (extProd.mapRight (specOverMap j)).app T ((e σ).hom.app T
        ((extProd.mapRight (specOverMap σ₀.toAlgHom)).app T z)) =
        (extProd.mapRight (specOverMap j)).app T ((e (σ.trans σ₀)).hom.app T z) := by
      rw [he, he]
      simp only [extProd.mapRight_app, hsp, Category.assoc]
    rw [heq]
    exact hz (σ.trans σ₀)
  · apply (hmemW _ _).mpr
    intro σ
    obtain ⟨τ, hτ⟩ := exists_restrict j σ
    have h := A.map (specOverMap σ.toAlgHom).op (hmem τ)
    have hkey : specOverMap σ.toAlgHom ≫ specOverMap j ≫ specOverMap τ.toAlgHom = specOverMap j := by
      rw [← specMap_comp, ← specMap_comp]
      congr 1
      ext x
      exact hτ x
    have heq : (extProd.mapRight (specOverMap j)).app _ ((e σ).hom.app _
        (((show (G ⋙ forget AddCommGrpCat).obj (op (specOver k L')) from
          G.map (specOverMap j).op gL), ULift.up (𝟙 _)) :
        (extProd (G ⋙ forget AddCommGrpCat) (specOver k L')).obj (op (specOver k L')))) =
        (extProd F (specOver k L)).map (specOverMap σ.toAlgHom).op
          ((show G.obj (op (specOver k L')) from q') +
            G.map (specOverMap j).op (G.map (specOverMap τ.toAlgHom).op gL), ULift.up (specOverMap j)) := by
      refine Prod.ext ?_ ?_
      · change G.map (specOverMap j).op gL + G.map (𝟙 _ ≫ specOverMap σ.toAlgHom).op q' =
          G.map (specOverMap σ.toAlgHom).op (q' + G.map (specOverMap j).op
            (G.map (specOverMap τ.toAlgHom).op gL))
        rw [map_add, Category.id_comp, add_comm]
        congr 1
        change _ = (G.map (specOverMap τ.toAlgHom).op ≫ G.map (specOverMap j).op ≫
          G.map (specOverMap σ.toAlgHom).op) gL
        rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, Category.assoc, hkey]
      · change ULift.up ((𝟙 _ ≫ specOverMap σ.toAlgHom) ≫ specOverMap j) =
          ULift.up (specOverMap σ.toAlgHom ≫ specOverMap j)
        rw [Category.id_comp]
    rw [heq]
    exact h

/-- Every point of `G` with values in a finite extension of `k` lies in the range of an open
immersion from an affine scheme. -/
theorem exists_open_chart_of_field_point
    (hS1 : SeparatedDenseAffineOpenLFTProp.{u})
    (h03BM : FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement.{u})
    (G : (Over 𝕊)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hF : CategoryTheory.Presheaf.IsSheaf (fppfTopology 𝕊) (G ⋙ forget AddCommGrpCat))
    (hd : IsClosedImmersion (Limits.diag (G ⋙ forget AddCommGrpCat)))
    {U : Over 𝕊} (a : (schemeYoneda 𝕊).obj U ⟶ G ⋙ forget AddCommGrpCat) (ha : IsEtale a)
    [LocallyOfFiniteType U.hom]
    (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K] (t : specOver k K ⟶ U) :
    ∃ (V : Over 𝕊) (b : (schemeYoneda 𝕊).obj V ⟶ G ⋙ forget AddCommGrpCat),
      LocallyOfFiniteType V.hom ∧
      IsOpenImmersion b ∧ (G ⋙ forget AddCommGrpCat).map t.op (uliftYonedaEquiv a) ∈
        (Subfunctor.range b).obj (op (specOver k K)) := by
  classical
  let F := G ⋙ forget AddCommGrpCat
  obtain ⟨L, _, _, hLfin, hLnorm, ⟨ι⟩⟩ := exists_finite_normal_extension (k := k) K
  let Λ := specOver k L
  let g : F.obj (op (specOver k K)) := F.map t.op (uliftYonedaEquiv a)
  let gL : G.obj (op Λ) := G.map (specOverMap ι).op g
  -- an affine open neighbourhood of the image of `t`
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨_, ⟨V₀', hV₀, rfl⟩, huV₀, -⟩ :=
    U.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t.left pt)) isOpen_univ
  let V₀ : U.left.Opens := V₀'
  let U₁ : Over 𝕊 := Over.mk (V₀.ι ≫ U.hom)
  let i₁ : U₁ ⟶ U := Over.homMk V₀.ι
  have : IsAffine U₁.left := hV₀
  have : LocallyOfFiniteType U₁.hom := by
    change LocallyOfFiniteType (V₀.ι ≫ U.hom)
    infer_instance
  let U₀ := U₁ ⨯ Λ
  have : IsAffine U₀.left := isAffine_slice_product U₁ Λ
  have : LocallyOfFiniteType U₀.hom := by
    rw [← Over.w (prod.fst : U₀ ⟶ U₁)]
    have : LocallyOfFiniteType (prod.fst : U₁ ⨯ Λ ⟶ U₁).left :=
      extProd.prod_fst_left (@LocallyOfFiniteType) inferInstance
    infer_instance
  have : Nonempty U₀.left := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨z, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := U₁.hom) (g := Λ.hom)
      (⟨t.left pt, huV₀⟩ : V₀) y (Subsingleton.elim _ _)
    exact ⟨(Over.prodLeftIsoPullback U₁ Λ).inv z⟩
  let a₁ := (schemeYoneda 𝕊).map i₁ ≫ a
  have ha₁ : IsEtale a₁ :=
    (isEtale_map i₁ (by change Etale V₀.ι; infer_instance)).comp ha
  let a₀ : (schemeYoneda 𝕊).obj U₀ ⟶ extProd F Λ :=
    (extProd.yonedaProdIso U₁).hom ≫ extProd.mapLeft a₁
  have ha₀ : IsEtale a₀ := by
    have : IsEtale (extProd.mapLeft (Λ := Λ) a₁) :=
      MorphismProperty.of_isPullback (P := (MorphismProperty.inverseImage (@Etale.{u})
        (Over.forget 𝕊)).relative (schemeYoneda 𝕊)) (extProd.isPullback_mapLeft a₁).flip ha₁
    exact IsEtale.iso_comp _ this
  -- Step 1: an affine open containing all translates of one field point
  obtain ⟨A, hA, L', _, _, hL'fin, hL'norm, ρ, hρ⟩ :=
    exists_affine_containing_translates hS1 G hF hd L a₀ ha₀ (Γ := L ≃ₐ[k] L) gL
      (fun τ ↦ specOverMap τ.toAlgHom)
  let z := a₀.app _ (⟨ρ⟩ : ((schemeYoneda 𝕊).obj U₀).obj (op (specOver k L')))
  obtain ⟨j, hj⟩ := exists_algHom_of_specOver_hom z.2.down
  have hmem : ∀ τ : L ≃ₐ[k] L,
      (((show G.obj (op (specOver k L')) from z.1) +
          G.map (specOverMap j).op (G.map (specOverMap τ.toAlgHom).op gL),
        ULift.up (specOverMap j)) : (extProd F Λ).obj (op (specOver k L'))) ∈
          A.obj (op (specOver k L')) := by
    intro τ
    have hz : z = (z.1, ULift.up (specOverMap j)) := Prod.ext rfl (ULift.ext _ _ hj)
    have h := hρ τ
    change (translate G (G.map (specOverMap τ.toAlgHom).op gL)).app _ z ∈ _ at h
    rw [hz] at h
    exact h
  -- Step 2: a Galois-stable affine open containing the base-changed point
  obtain ⟨W, hW, hstab, hbase⟩ := exists_galois_stable_affine G hd hA j z.1 gL hmem
  have hinv := fst_invariant_of_galois_stable hW.1 hstab
  -- Step 3: descent to `F`
  obtain ⟨hW₀, hpre⟩ := isLFTAffineOpen_universalImage_fst k h03BM hF L' hW hinv
  let W₀ := universalImage (extProd.fst : extProd F (specOver k L') ⟶ F) W
  have hg' : G.map (specOverMap j).op gL ∈ W₀.obj (op (specOver k L')) := by
    have h : (((show F.obj (op (specOver k L')) from G.map (specOverMap j).op gL), ULift.up (𝟙 _)) :
        (extProd F (specOver k L')).obj (op (specOver k L'))) ∈
          (W₀.preimage (extProd.fst : extProd F (specOver k L') ⟶ F)).obj
            (op (specOver k L')) := by
      rw [hpre]
      exact hbase
    exact h
  have : Surjective (specOverMap j ≫ specOverMap ι).left := surjective_specOver_hom _
  have hg : g ∈ W₀.obj (op (specOver k K)) := by
    apply OpenSubfunctorPoints.mem_of_surjective hW₀.1 (specOverMap j ≫ specOverMap ι)
    have : F.map (specOverMap j ≫ specOverMap ι).op g = G.map (specOverMap j).op gL := by
      change (G.map (specOverMap j ≫ specOverMap ι).op) g = (G.map (specOverMap ι).op ≫ G.map (specOverMap j).op) g
      rw [← G.map_comp, ← op_comp]
    rw [this]
    exact hg'
  obtain ⟨M, hM, hMlft, ⟨eM⟩⟩ := hW₀.2
  refine ⟨M, eM.hom ≫ W₀.ι, hMlft, IsOpenImmersion.iso_comp eM hW₀.1, ?_⟩
  refine ⟨eM.inv.app _ ⟨g, hg⟩, ?_⟩
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app eM.inv_hom_id (op (specOver k K)))
    (⟨g, hg⟩ : W₀.toFunctor.obj (op (specOver k K)))
  exact congrArg Subtype.val h

end Langlands.AlgebraicGeometry.AlgebraicSpace
