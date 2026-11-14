import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps

/-! # Base change of Murre's conditions: the pointwise conditions and the sheaf conditions -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace BaseChange

variable {S S' : Scheme.{u}} (g : S' ⟶ S) (F : (Over S)ᵒᵖ ⥤ Type v)

section Transport

variable {A : Type u} [CommRing A] (f : Spec (CommRingCat.of A) ⟶ S')

/-- The image of `Spec B ⟶ Spec A ⟶ S'` under `Over.map g` is `Spec B ⟶ Spec A ⟶ S`. -/
def mapAlgebraOverIso (B : Type u) [CommRing B] [Algebra A B] :
    (Over.map g).obj (algebraOver f B) ≅ algebraOver (f ≫ g) B :=
  Over.isoMk (Iso.refl _) (by simp)

/-- The values of the base change at `Spec B` are the values of `F` at `Spec B ⟶ S`. -/
def equiv (B : Type u) [CommRing B] [Algebra A B] :
    (baseChange g F).obj (op (algebraOver f B)) ≃ F.obj (op (algebraOver (f ≫ g) B)) :=
  (F.mapIso (mapAlgebraOverIso g f B).symm.op).toEquiv

lemma equiv_apply (B : Type u) [CommRing B] [Algebra A B]
    (x : (baseChange g F).obj (op (algebraOver f B))) :
    equiv g F f B x = F.map (mapAlgebraOverIso g f B).inv.op x := rfl

lemma equiv_map {B C : Type u} [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]
    (φ : B →ₐ[A] C) (x : (baseChange g F).obj (op (algebraOver f B))) :
    equiv g F f C ((baseChange g F).map (algHomOver f φ).op x) =
      F.map (algHomOver (f ≫ g) φ).op (equiv g F f B x) := by
  have hc : (mapAlgebraOverIso g f C).inv ≫ (Over.map g).map (algHomOver f φ) =
      algHomOver (f ≫ g) φ ≫ (mapAlgebraOverIso g f B).inv := by
    ext
    simp [mapAlgebraOverIso, algHomOver]
  calc equiv g F f C ((baseChange g F).map (algHomOver f φ).op x)
      = F.map (((Over.map g).map (algHomOver f φ)).op ≫ (mapAlgebraOverIso g f C).inv.op) x :=
        (F.map_comp_apply _ _ x).symm
    _ = F.map ((mapAlgebraOverIso g f B).inv.op ≫ (algHomOver (f ≫ g) φ).op) x := by
        rw [← op_comp, hc, op_comp]
    _ = F.map (algHomOver (f ≫ g) φ).op (equiv g F f B x) := F.map_comp_apply _ _ x

lemma equiv_base (B : Type u) [CommRing B] [Algebra A B]
    (x : (baseChange g F).obj (op (Over.mk f))) :
    equiv g F f B ((baseChange g F).map (algebraOverBase f B).op x) =
      F.map (algebraOverBase (f ≫ g) B).op x := by
  have hc : (mapAlgebraOverIso g f B).inv ≫ (Over.map g).map (algebraOverBase f B) =
      algebraOverBase (f ≫ g) B := by
    ext
    simp [mapAlgebraOverIso, algebraOverBase]
  calc equiv g F f B ((baseChange g F).map (algebraOverBase f B).op x)
      = F.map (((Over.map g).map (algebraOverBase f B)).op ≫ (mapAlgebraOverIso g f B).inv.op)
          x := (F.map_comp_apply _ _ x).symm
    _ = F.map (algebraOverBase (f ≫ g) B).op x := by rw [← op_comp, hc]

variable {g F f}

lemma equiv_restrictQuotient {I : Ideal A} (B : Type u) [CommRing B] [Algebra A B]
    (ξ' : (baseChange g F).obj (op (algebraOver f (A ⧸ I)))) :
    equiv g F f _ (restrictQuotient B ξ') = restrictQuotient (f := f ≫ g) B (equiv g F f _ ξ') :=
  equiv_map g F f _ ξ'

lemma liftsTo_iff {I : Ideal A} (B : Type u) [CommRing B] [Algebra A B]
    (ξ' : (baseChange g F).obj (op (algebraOver f (A ⧸ I)))) :
    LiftsTo B ξ' ↔ LiftsTo (f := f ≫ g) B (equiv g F f _ ξ') := by
  constructor
  · rintro ⟨η, hη⟩
    exact ⟨equiv g F f B η, by rw [← equiv_map, hη, equiv_restrictQuotient]⟩
  · rintro ⟨η, hη⟩
    refine ⟨(equiv g F f B).symm η, (equiv g F f _).injective ?_⟩
    rw [equiv_map, Equiv.apply_symm_apply, hη, equiv_restrictQuotient]

lemma noLargerLift_iff {I : Ideal A} (B : Type u) [CommRing B] [Algebra A B]
    (ξ' : (baseChange g F).obj (op (algebraOver f (A ⧸ I)))) :
    NoLargerLift B ξ' ↔ NoLargerLift (f := f ≫ g) B (equiv g F f _ ξ') := by
  constructor
  · intro h J hJ η hη
    refine h J hJ ((equiv g F f _).symm η) ((equiv g F f _).injective ?_)
    rw [equiv_map, Equiv.apply_symm_apply, hη, equiv_restrictQuotient]
  · intro h J hJ η hη
    refine h J hJ (equiv g F f _ η) ?_
    rw [← equiv_map, hη, equiv_restrictQuotient]

end Transport

theorem smallValues (h : SmallValues F) : SmallValues (baseChange g F) :=
  fun T ↦ h ((Over.map g).obj T)

theorem nilpotentInjective (h : NilpotentInjective F) : NilpotentInjective (baseChange g F) := by
  intro A _ _ _ I hI f x y hxy
  apply h A I hI (f ≫ g)
  have := congrArg (equiv g F f _) hxy
  rwa [equiv_base, equiv_base] at this

theorem valuativeSeparation (h : ValuativeSeparation F) :
    ValuativeSeparation (baseChange g F) := by
  intro V _ _ _ f x y hxy
  apply h V (f ≫ g)
  have := congrArg (equiv g F f _) hxy
  rwa [equiv_base, equiv_base] at this

theorem adicLimits (h : AdicLimits F) : AdicLimits (baseChange g F) := by
  intro A _ _ _ _ f
  obtain ⟨h₁, h₂⟩ := h A (f ≫ g)
  refine ⟨fun x y hxy ↦ h₁ x y fun n ↦ ?_, fun s hs ↦ ?_⟩
  · have := congrArg (equiv g F f _) (hxy n)
    rwa [equiv_base, equiv_base] at this
  · obtain ⟨x, hx⟩ := h₂ (fun n ↦ equiv g F f _ (s n)) (fun n ↦ by rw [← equiv_map, hs n])
    exact ⟨x, fun n ↦ (equiv g F f _).injective ((equiv_base g F f _ x).trans (hx n))⟩

theorem artinianLifting (h : ArtinianLifting F) : ArtinianLifting (baseChange g F) := by
  intro A _ _ _ f A' _ _ hinj hlen ξ₀ ξ' hξ
  obtain ⟨ξ, hξ'⟩ := h A (f ≫ g) A' hinj hlen (equiv g F f _ ξ₀) (equiv g F f _ ξ') (by
    rw [← equiv_map, ← equiv_map, hξ])
  exact ⟨ξ, (equiv g F f _).injective ((equiv_base g F f _ ξ).trans hξ')⟩

theorem oneDimensionalLifting (h : OneDimensionalLifting F) :
    OneDimensionalLifting (baseChange g F) := by
  intro A _ _ _ _ hdim hass t ht I hI hIN f ξ' hlift
  obtain ⟨ξ, hξ⟩ := h A hdim hass t ht I hI hIN (f ≫ g) (equiv g F f _ ξ')
    ((liftsTo_iff _ ξ').1 hlift)
  exact ⟨ξ, (equiv g F f _).injective ((equiv_base g F f _ ξ).trans hξ)⟩

theorem genericNonLifting (h : GenericNonLifting F) : GenericNonLifting (baseChange g F) := by
  intro A _ _ t ht I hI hIN f ξ' hno
  obtain ⟨g₀, hne, hg⟩ := h A t ht I hI hIN (f ≫ g) (equiv g F f _ ξ')
    ((noLargerLift_iff _ ξ').1 hno)
  exact ⟨g₀, hne, fun a ha ↦ (noLargerLift_iff _ ξ').2 (hg a ha)⟩

section Sheaf

/-- The sheaf condition for a family of arrows over `S'` follows from the sheaf condition for
an isomorphic family of their images over `S`. -/
lemma isSheafFor_ofArrows {T : Over S'} {ι : Type*} (U : ι → Over S') (π : ∀ i, U i ⟶ T)
    (V : ι → Over S) (π' : ∀ i, V i ⟶ (Over.map g).obj T)
    (e : ∀ i, V i ≅ (Over.map g).obj (U i))
    (he : ∀ i, (e i).hom ≫ (Over.map g).map (π i) = π' i)
    (hF : Presieve.IsSheafFor F (Presieve.ofArrows V π')) :
    Presieve.IsSheafFor (baseChange g F) (Presieve.ofArrows U π) := by
  rw [Presieve.isSheafFor_arrows_iff] at hF ⊢
  intro x hx
  let y : ∀ i, F.obj (op (V i)) := fun i ↦ F.map (e i).hom.op (x i)
  have hy : Presieve.Arrows.Compatible F π' y := by
    intro i j Z gi gj hij
    have hl : (gi ≫ (e i).hom).left ≫ (U i).hom = (gj ≫ (e j).hom).left ≫ (U j).hom := by
      have h₁ := Over.w (π i)
      have h₂ := Over.w (π j)
      have h₃ := congrArg CommaMorphism.left hij
      rw [← he i, ← he j] at h₃
      simp only [Over.comp_left, Over.map_map_left] at h₃
      rw [← h₁, ← h₂]
      simp only [← Category.assoc, Over.comp_left] at h₃ ⊢
      rw [h₃]
    let Z' : Over S' := Over.mk ((gi ≫ (e i).hom).left ≫ (U i).hom)
    let gi' : Z' ⟶ U i := Over.homMk (gi ≫ (e i).hom).left
    let gj' : Z' ⟶ U j := Over.homMk (gj ≫ (e j).hom).left hl.symm
    have hc : gi' ≫ π i = gj' ≫ π j := by
      ext
      have h₃ := congrArg CommaMorphism.left hij
      rw [← he i, ← he j] at h₃
      simpa [gi', gj'] using h₃
    have hcomp := hx i j Z' gi' gj' hc
    let ε : Z ⟶ (Over.map g).obj Z' := Over.homMk (𝟙 Z.left) (by
      have := Over.w (gi ≫ (e i).hom)
      simp only [Z', Over.map_obj_hom, Over.mk_hom, Category.id_comp, Category.assoc]
      rw [← this]
      simp)
    have h₁ : gi ≫ (e i).hom = ε ≫ (Over.map g).map gi' := by ext; simp [ε, gi']
    have h₂ : gj ≫ (e j).hom = ε ≫ (Over.map g).map gj' := by ext; simp [ε, gj']
    show F.map gi.op (F.map (e i).hom.op (x i)) = F.map gj.op (F.map (e j).hom.op (x j))
    calc F.map gi.op (F.map (e i).hom.op (x i))
        = F.map ((e i).hom.op ≫ gi.op) (x i) := (F.map_comp_apply _ _ _).symm
      _ = F.map (((Over.map g).map gi').op ≫ ε.op) (x i) := by rw [← op_comp, h₁, op_comp]
      _ = F.map ε.op (F.map ((Over.map g).map gi').op (x i)) := F.map_comp_apply _ _ _
      _ = F.map ε.op (F.map ((Over.map g).map gj').op (x j)) :=
          congrArg (fun z ↦ F.map ε.op z) hcomp
      _ = F.map (((Over.map g).map gj').op ≫ ε.op) (x j) := (F.map_comp_apply _ _ _).symm
      _ = F.map ((e j).hom.op ≫ gj.op) (x j) := by rw [← op_comp, ← op_comp, h₂]
      _ = F.map gj.op (F.map (e j).hom.op (x j)) := F.map_comp_apply _ _ _
  obtain ⟨t, ht, huniq⟩ := hF y hy
  have key : ∀ i (a b : (baseChange g F).obj (op (U i))),
      F.map (e i).hom.op a = F.map (e i).hom.op b → a = b := by
    intro i a b hab
    exact (F.mapIso (e i).op).toEquiv.injective hab
  refine ⟨t, fun i ↦ key i _ _ ?_, fun t' ht' ↦ huniq t' fun i ↦ ?_⟩
  · change F.map (e i).hom.op (F.map ((Over.map g).map (π i)).op t) = y i
    rw [← Functor.map_comp_apply, ← op_comp, he, ht]
  · have h₁ : (π' i).op = ((Over.map g).map (π i)).op ≫ (e i).hom.op := by rw [← he, op_comp]
    show F.map (π' i).op t' = F.map (e i).hom.op (x i)
    calc F.map (π' i).op t'
        = F.map (((Over.map g).map (π i)).op ≫ (e i).hom.op) t' := by rw [h₁]
      _ = F.map (e i).hom.op (F.map ((Over.map g).map (π i)).op t') := F.map_comp_apply _ _ _
      _ = F.map (e i).hom.op (x i) := congrArg (fun z ↦ F.map (e i).hom.op z) (ht' i)

theorem zariskiSheaf (h : ZariskiSheaf F) : ZariskiSheaf (baseChange g F) := by
  intro T 𝒰
  exact isSheafFor_ofArrows g F _ _ (fun i ↦ Over.mk (𝒰.f i ≫ ((Over.map g).obj T).hom))
    (fun i ↦ Over.homMk (𝒰.f i)) (fun i ↦ Over.isoMk (Iso.refl _) (by simp))
    (fun i ↦ by ext; simp) (h ((Over.map g).obj T) 𝒰)

theorem faithfullyFlatSheaf (h : FaithfullyFlatSheaf F) :
    FaithfullyFlatSheaf (baseChange g F) := by
  intro T' T φ hflat hsurj hqc
  rw [← Presieve.ofArrows_pUnit.{0}]
  refine isSheafFor_ofArrows g F (fun _ ↦ T') (fun _ ↦ φ) (fun _ ↦ (Over.map g).obj T')
    (fun _ ↦ (Over.map g).map φ) (fun _ ↦ Iso.refl _) (fun _ ↦ by simp) ?_
  rw [Presieve.ofArrows_pUnit.{0}]
  exact h ((Over.map g).map φ) hflat hsurj hqc

end Sheaf

end BaseChange

end Langlands.AlgebraicGeometry.UnramifiedFunctor
