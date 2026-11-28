import Langlands.AlgebraicGeometry.BirationalGroupLawSolutionUniquenessStatement
import Langlands.AlgebraicGeometry.DenseGroupHomExtension

/-! # Uniqueness of solutions of birational group laws -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

namespace BirationalGroupLaw

open DenseGroupMultiplication
open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {S X : Scheme.{u}} {f : X ⟶ S} {m : BirationalGroupLaw f}

private abbrev overOpen (f : X ⟶ S) (U : X.Opens) : Over S := Over.mk (U.ι ≫ f)

private abbrev openι (f : X ⟶ S) (U : X.Opens) : overOpen f U ⟶ Over.mk f :=
  Over.homMk U.ι rfl

private def embeddingOn (σ : m.Solution) {U : X.Opens} (h : U ≤ σ.domain) :
    overOpen f U ⟶ σ.group.X :=
  Over.homMk (X.homOfLE h ≫ σ.embedding) (by
    rw [Category.assoc, σ.embedding_comp, Scheme.homOfLE_ι_assoc]; rfl)

private instance (σ : m.Solution) {U : X.Opens} (h : U ≤ σ.domain) :
    IsOpenImmersion (embeddingOn σ h).left := by
  have := σ.isOpenImmersion_embedding
  change IsOpenImmersion (X.homOfLE h ≫ σ.embedding)
  infer_instance

private lemma embeddingOn_dense (σ : m.Solution) {U : X.Opens} (h : U ≤ σ.domain)
    (hU : FibreGenerizationDense f U) :
    FibreGenerizationDense σ.group.X.hom (embeddingOn σ h).left.opensRange := by
  have := σ.isOpenImmersion_embedding
  have hdom : FibreGenerizationDense σ.group.X.hom σ.embedding.opensRange := σ.embedding_dense
  change FibreGenerizationDense σ.group.X.hom (X.homOfLE h ≫ σ.embedding).opensRange
  rw [Scheme.Hom.opensRange_comp, Scheme.opensRange_homOfLE]
  apply FibreGenerizationDense.image_open σ.embedding hdom
  rw [σ.embedding_comp]
  exact hU.preimage_flat σ.domain.ι

private lemma smooth_mul [Smooth f] (m : BirationalGroupLaw f) : Smooth m.mul := by
  have := m.isOpenImmersion_leftTranslation
  have hs : leftTranslation f m.domain m.mul m.mul_comp ≫ pullback.snd f f = m.mul :=
    pullback.lift_snd _ _ _
  rw [← hs]
  infer_instance

private theorem exists_hom_on_open [Smooth f] (σ τ : m.Solution) {U : X.Opens}
    (hσ : U ≤ σ.domain) (hτ : U ≤ τ.domain) (hU : FibreGenerizationDense f U) :
    ∃ c : σ.group ⟶ τ.group, embeddingOn σ hσ ≫ c.hom.hom = embeddingOn τ hτ := by
  let A : Over S := Over.mk f
  let B := overOpen f U
  let P := B ⊗ B
  let D := overOpen (A ⊗ A).hom m.domain
  let iD : D ⟶ A ⊗ A := openι (A ⊗ A).hom m.domain
  let pD : D ⟶ A := Over.homMk m.mul m.mul_comp
  let iU := openι f U
  let r : P ⟶ A ⊗ A := iU ⊗ₘ iU
  have : IsOpenImmersion iU.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : IsOpenImmersion iD.left := inferInstanceAs (IsOpenImmersion m.domain.ι)
  have : IsOpenImmersion r.left := isOpenImmersion_tensorHom iU iU
  have : Smooth m.mul := smooth_mul m
  let V := m.mul ⁻¹ᵁ U
  have hV : FibreGenerizationDense (m.domain.ι ≫ pullback.fst f f ≫ f) V := by
    rw [← m.mul_comp]
    exact hU.preimage_flat m.mul
  have hD : FibreGenerizationDense (pullback.fst f f ≫ f) m.domain.ι.opensRange := by
    simpa only [Scheme.Opens.opensRange_ι] using m.domain_dense
  have hDV := FibreGenerizationDense.image_open m.domain.ι hD hV
  let J := r.left ⁻¹ᵁ (m.domain.ι ''ᵁ V)
  let W := overOpen P.hom J
  let j : W ⟶ P := openι P.hom J
  have : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion J.ι)
  have hj : FibreGenerizationDense P.hom j.left.opensRange := by
    change FibreGenerizationDense P.hom J.ι.opensRange
    rw [Scheme.Opens.opensRange_ι, ← Over.w r]
    exact hDV.preimage_flat r.left
  have hsubD : Set.range (j ≫ r).left ⊆ Set.range iD.left := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, -, hv⟩ := w.2
    exact ⟨v, hv⟩
  let d := liftOver iD (j ≫ r) hsubD
  have hd : d ≫ iD = j ≫ r := liftOver_fac _ _ _
  have hd' : d.left ≫ m.domain.ι = J.ι ≫ r.left := congrArg Over.Hom.left hd
  have hsubU : Set.range (d ≫ pD).left ⊆ Set.range iU.left := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨v, hv, hvw⟩ := w.2
    have hw : d.left w = v := m.domain.ι.isOpenEmbedding.injective (by
      exact (congrArg (fun k : W.left ⟶ (A ⊗ A).left => k w) hd').trans hvw.symm)
    change m.mul (d.left w) ∈ Set.range U.ι
    rw [hw, Scheme.Opens.range_ι]
    exact hv
  let z := liftOver iU (d ≫ pD) hsubU
  have hz : z ≫ iU = d ≫ pD := liftOver_fac _ _ _
  let x := j ≫ fst B B
  let y := j ≫ snd B B
  have hx : d.left ≫ m.domain.ι ≫ pullback.fst f f = x.left ≫ U.ι := by
    have hx' : d ≫ iD ≫ fst A A = x ≫ iU := by
      rw [← Category.assoc, hd, Category.assoc]
      change j ≫ (iU ⊗ₘ iU) ≫ fst A A = (j ≫ fst B B) ≫ iU
      rw [tensorHom_fst, Category.assoc]
    exact congrArg Over.Hom.left hx'
  have hy : d.left ≫ m.domain.ι ≫ pullback.snd f f = y.left ≫ U.ι := by
    have hy' : d ≫ iD ≫ snd A A = y ≫ iU := by
      rw [← Category.assoc, hd, Category.assoc]
      change j ≫ (iU ⊗ₘ iU) ≫ snd A A = (j ≫ snd B B) ≫ iU
      rw [tensorHom_snd, Category.assoc]
    exact congrArg Over.Hom.left hy'
  have hz' : z.left ≫ U.ι = d.left ≫ m.mul := congrArg Over.Hom.left hz
  have hmul (ρ : m.Solution) (hle : U ≤ ρ.domain) :
      j ≫ openProduct ρ.group (embeddingOn ρ hle) = z ≫ embeddingOn ρ hle := by
    let a := embeddingOn ρ hle
    have ha : j ≫ (a ⊗ₘ a) = lift (x ≫ a) (y ≫ a) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
    have hp : j ≫ openProduct ρ.group a = lift (x ≫ a) (y ≫ a) ≫ μ[ρ.group.X] := by
      rw [openProduct, ← Category.assoc, ha]
    have hρ := ρ.mul_eq W.left d.left (x.left ≫ X.homOfLE hle) (y.left ≫ X.homOfLE hle)
      (z.left ≫ X.homOfLE hle)
      (by rwa [Category.assoc, Scheme.homOfLE_ι])
      (by rwa [Category.assoc, Scheme.homOfLE_ι])
      (by rw [Category.assoc, Scheme.homOfLE_ι, hz'])
    change j ≫ openProduct ρ.group a = z ≫ a
    rw [hp]
    exact Over.OverMorphism.ext hρ.symm
  have := σ.smooth
  have := τ.isSeparated
  exact exists_hom_of_compatible_products (embeddingOn σ hσ) (embeddingOn τ hτ)
    (embeddingOn_dense σ hσ hU) j hj z (hmul σ hσ) (hmul τ hτ)

private theorem hom_ext_on_open (σ τ : m.Solution) {U : X.Opens} (h : U ≤ σ.domain)
    (hU : FibreGenerizationDense f U) (a b : σ.group ⟶ τ.group)
    (he : embeddingOn σ h ≫ a.hom.hom = embeddingOn σ h ≫ b.hom.hom) : a = b := by
  have := σ.smooth
  have := τ.isSeparated
  have : IsSchemeTheoreticallyDominant (embeddingOn σ h).left :=
    (embeddingOn_dense σ h hU).schematicallyDominant σ.group.X.hom (embeddingOn σ h).left
  exact Grp.hom_ext _ _ (overHom_ext_of_schematicallyDominant (embeddingOn σ h) he)

private theorem compatible_iff (σ τ : m.Solution) (c : σ.group ⟶ τ.group) :
    (∀ (T : Scheme.{u}) (x : T ⟶ σ.domain.toScheme) (y : T ⟶ τ.domain.toScheme),
        x ≫ σ.domain.ι = y ≫ τ.domain.ι → x ≫ σ.embedding ≫ c.hom.hom.left = y ≫ τ.embedding) ↔
      embeddingOn σ (U := σ.domain ⊓ τ.domain) inf_le_left ≫ c.hom.hom =
        embeddingOn τ inf_le_right := by
  let U := σ.domain ⊓ τ.domain
  let i : U.toScheme ⟶ σ.domain.toScheme := X.homOfLE inf_le_left
  let j : U.toScheme ⟶ τ.domain.toScheme := X.homOfLE inf_le_right
  have hi : i ≫ σ.domain.ι = U.ι := Scheme.homOfLE_ι _ _
  have hj : j ≫ τ.domain.ι = U.ι := Scheme.homOfLE_ι _ _
  constructor
  · intro h
    apply Over.OverMorphism.ext
    change (i ≫ σ.embedding) ≫ c.hom.hom.left = j ≫ τ.embedding
    simpa only [Category.assoc] using h U.toScheme i j (hi.trans hj.symm)
  · intro h T x y hxy
    have hr : Set.range (x ≫ σ.domain.ι) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      refine ⟨(x z).2, ?_⟩
      rw [hxy]
      exact (y z).2
    let v := IsOpenImmersion.lift U.ι (x ≫ σ.domain.ι) hr
    have hv : v ≫ U.ι = x ≫ σ.domain.ι := IsOpenImmersion.lift_fac _ _ _
    have hvi : v ≫ i = x := (cancel_mono σ.domain.ι).mp (by rw [Category.assoc, hi, hv])
    have hvj : v ≫ j = y := (cancel_mono τ.domain.ι).mp (by rw [Category.assoc, hj, hv, hxy])
    have h' : (i ≫ σ.embedding) ≫ c.hom.hom.left = j ≫ τ.embedding := congrArg Over.Hom.left h
    simpa only [← Category.assoc, hvi, hvj] using congrArg (v ≫ ·) h'

end BirationalGroupLaw

/-- BLR §5.1, Proposition 3. Solutions of a birational group law have a unique
isomorphism compatible with the two embeddings on their common open. -/
theorem birationalGroupLawSolutionUniqueness : BirationalGroupLawSolutionUniquenessStatement.{u} := by
  intro S X f hf _ _ _ _ m σ τ
  let U := σ.domain ⊓ τ.domain
  have hU : FibreGenerizationDense f U := σ.domain_dense.inf τ.domain_dense
  let a := BirationalGroupLaw.embeddingOn σ (U := U) inf_le_left
  let b := BirationalGroupLaw.embeddingOn τ (U := U) inf_le_right
  obtain ⟨c, hc⟩ := BirationalGroupLaw.exists_hom_on_open σ τ inf_le_left inf_le_right hU
  obtain ⟨d, hd⟩ := BirationalGroupLaw.exists_hom_on_open τ σ inf_le_right inf_le_left hU
  have hcd : c ≫ d = 𝟙 σ.group := by
    apply BirationalGroupLaw.hom_ext_on_open σ σ inf_le_left hU
    change a ≫ c.hom.hom ≫ d.hom.hom = a ≫ 𝟙 σ.group.X
    rw [← Category.assoc, hc, hd, Category.comp_id]
  have hdc : d ≫ c = 𝟙 τ.group := by
    apply BirationalGroupLaw.hom_ext_on_open τ τ inf_le_right hU
    change b ≫ d.hom.hom ≫ c.hom.hom = b ≫ 𝟙 τ.group.X
    rw [← Category.assoc, hd, hc, Category.comp_id]
  let e : σ.group ≅ τ.group := ⟨c, d, hcd, hdc⟩
  refine ⟨e, (BirationalGroupLaw.compatible_iff σ τ c).mpr hc, ?_⟩
  intro e' he'
  apply Iso.ext
  exact BirationalGroupLaw.hom_ext_on_open σ τ inf_le_left hU e'.hom c
    (((BirationalGroupLaw.compatible_iff σ τ e'.hom).mp he').trans hc.symm)

end Langlands.AlgebraicGeometry
