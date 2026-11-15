import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseProof
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingRepr
import Mathlib.AlgebraicGeometry.ValuativeCriterion

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace ArtinianBase

/-- A scheme covered by open immersions from discrete schemes is discrete. -/
lemma discreteTopology_of_cover {Y : Scheme.{u}} {ι : Type*} (X : ι → Scheme.{u})
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsOpenImmersion (f i)) (hX : ∀ i, DiscreteTopology (X i))
    (hcov : ∀ y, ∃ i, y ∈ Set.range (f i)) : DiscreteTopology Y := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro y
  obtain ⟨i, x, rfl⟩ := hcov y
  have := (f i).isOpenEmbedding.isOpenMap {x} (isOpen_discrete _)
  rwa [Set.image_singleton] at this

/-- Valuative lifts into a discrete scheme are unique: a lift `Spec V ⟶ Y` is constant (every
point of `Spec V` specializes to the closed point), so two lifts with the same restriction to
`Spec K` land in a common affine open `Spec B`, where they are given by ring maps `B → V`
that agree after composing with the injection `V → K`. -/
lemma valuativeUniqueness_of_discrete {Y S : Scheme.{u}} (q : Y ⟶ S) [DiscreteTopology Y] :
    ValuativeCriterion.Uniqueness q := by
  intro Sq
  refine ⟨fun l₁ l₂ ↦ ?_⟩
  have hconst : ∀ (l : Spec (CommRingCat.of Sq.R) ⟶ Y) (x : Spec (CommRingCat.of Sq.R)),
      l x = l (closedPoint Sq.R) := fun l x ↦
    ((specializes_closedPoint (R := Sq.R) x).map l.continuous).eq
  let ι : Spec (CommRingCat.of Sq.K) ⟶ Spec (CommRingCat.of Sq.R) :=
    Spec.map (CommRingCat.ofHom (algebraMap Sq.R Sq.K))
  have h₁ : ι ≫ l₁.l = ι ≫ l₂.l := l₁.fac_left.trans l₂.fac_left.symm
  have hy : l₂.l (closedPoint Sq.R) = l₁.l (closedPoint Sq.R) := by
    rw [← hconst l₁.l (ι (closedPoint Sq.K)), ← hconst l₂.l (ι (closedPoint Sq.K))]
    have := congrArg (fun g ↦ g (closedPoint Sq.K)) h₁
    exact this.symm
  let 𝒰 := Y.affineOpenCover
  let y := l₁.l (closedPoint Sq.R)
  have hr : ∀ l : Spec (CommRingCat.of Sq.R) ⟶ Y, l (closedPoint Sq.R) = y →
      Set.range l ⊆ Set.range (𝒰.f (𝒰.idx y)) := by
    rintro l hl _ ⟨x, rfl⟩
    rw [hconst, hl]
    exact 𝒰.covers y
  obtain ⟨m₁, hm₁⟩ : ∃ m, m ≫ 𝒰.f (𝒰.idx y) = l₁.l :=
    ⟨_, IsOpenImmersion.lift_fac _ _ (hr _ rfl)⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m, m ≫ 𝒰.f (𝒰.idx y) = l₂.l :=
    ⟨_, IsOpenImmersion.lift_fac _ _ (hr _ hy)⟩
  have e1 : ι ≫ m₁ = ι ≫ m₂ := by
    rw [← cancel_mono (𝒰.f (𝒰.idx y)), Category.assoc, Category.assoc, hm₁, hm₂, h₁]
  have hm : m₁ = m₂ := by
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂] at e1 ⊢
    rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e1
    congr 1
    ext b
    apply IsFractionRing.injective Sq.R Sq.K
    exact congrArg (fun g ↦ g.hom b) e1
  exact CommSq.LiftStruct.ext (by rw [← hm₁, ← hm₂, hm])

end ArtinianBase

open ArtinianBase Charts

/-- **Step 1 of Murre's Case I.** Over a local artinian base `Spec R`, every presheaf
satisfying Murre's conditions is represented by a separated, locally of finite type, formally
unramified scheme. -/
theorem murreArtinianBase : MurreArtinianBaseStatement.{u, v} := by
  intro R _ _ F hF
  obtain ⟨hS, hZ, hFF, h2, h3, h4, h5, -, -, -⟩ := hF
  have hSm : ∀ T : Over (Spec R), Small.{u} (F.obj (op T)) := hS
  have hft : ∀ i : ChartIdx F, Algebra.FiniteType R (PRing i.1.1 i.1.2.1) := fun i ↦
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R _) Ideal.Quotient.mk_surjective
  obtain ⟨Y, q, e, hLFT, hopen, hcover⟩ := ChartGluing.murreChartGluing (Spec R) F hS hZ hFF h2
    h3 (ChartIdx F) (fun i ↦ ovR R (PRing i.1.1 i.1.2.1)) (fun i ↦ i.1.elem)
    (fun i ↦ Charts.locallyOfFiniteType_ovR _) (fun i ↦ i.2.2.2.1) (fun i ↦ i.2.2.2.2) (by
      intro K _ f η
      let : Algebra R K := (Spec.preimage f).hom.toAlgebra
      let iK : Over.mk f ≅ ovR R K := Over.isoMk (Iso.refl _) (by
        rw [Iso.refl_hom, Category.id_comp]
        change Spec.map (CommRingCat.ofHom (Spec.preimage f).hom) = f
        rw [CommRingCat.ofHom_hom]
        exact Spec.map_preimage f)
      obtain ⟨i, ρ, hρ⟩ := exists_fac_field hZ hFF h2 h3 h4 h5 (F.map iK.inv.op η)
      refine ⟨i, iK.hom ≫ homR ρ, ?_⟩
      rw [op_comp, Functor.map_comp_apply]
      change F.map iK.hom.op (res ρ i.1.elem) = η
      rw [hρ, ← Functor.map_comp_apply, ← op_comp, iK.hom_inv_id, op_id, Functor.map_id_apply])
  have hdisc : DiscreteTopology Y := by
    refine discreteTopology_of_cover (fun i : ChartIdx F ↦ (ovR R (PRing i.1.1 i.1.2.1)).left)
      (fun i ↦ (e.homEquiv.symm i.1.elem).left) hopen (fun i ↦ ?_) hcover
    have := i.2.2.1
    exact inferInstanceAs (DiscreteTopology (PrimeSpectrum (PRing i.1.1 i.1.2.1)))
  refine ⟨Y, q, ⟨e⟩, IsSeparated.of_valuativeCriterion q (valuativeUniqueness_of_discrete q),
    hLFT, ?_⟩
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers (ChartIdx F)
    (fun i ↦ (ovR R (PRing i.1.1 i.1.2.1)).left) (fun i ↦ (e.homEquiv.symm i.1.elem).left)
    (fun y ↦ by
      obtain ⟨i, x, hx⟩ := hcover y
      exact ⟨i, x, hx⟩) hopen
  have : IsZariskiLocalAtSource @FormallyUnramified.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover 𝒰 (fun i ↦ ?_)
  have hw : (e.homEquiv.symm i.1.elem).left ≫ q = (ovR R (PRing i.1.1 i.1.2.1)).hom :=
    Over.w (e.homEquiv.symm i.1.elem)
  change FormallyUnramified ((e.homEquiv.symm i.1.elem).left ≫ q)
  rw [hw]
  have := i.2.1
  exact Charts.formallyUnramified_ovR _

end Langlands.AlgebraicGeometry.UnramifiedFunctor
