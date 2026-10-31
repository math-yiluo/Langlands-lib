import Langlands.AlgebraicGeometry.FieldTwoAxisRigiditySmoothSecondStatement
import Langlands.AlgebraicGeometry.FactorizationOfGlobalFunctionsProof
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # Two-axis rigidity over fields with a smooth, possibly non-proper second factor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

namespace Langlands.AlgebraicGeometry

/-- If `e` is a section of `p`, `p.app V` is an isomorphism and `g` maps `p ⁻¹ᵁ V` into an
affine open `U`, then `g` agrees with `p ≫ e ≫ g` on `p ⁻¹ᵁ V`. -/
private lemma restrict_eq_of_affine {X S T : Scheme.{u}} (p : X ⟶ S) (e : S ⟶ X) (g : X ⟶ T)
    (hep : e ≫ p = 𝟙 S) (V : S.Opens) [IsIso (p.app V)] (U : T.Opens) (hU : IsAffineOpen U)
    (hVU : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ U) :
    (p ⁻¹ᵁ V).ι ≫ g = (p ⁻¹ᵁ V).ι ≫ p ≫ e ≫ g := by
  have : IsAffine U := hU
  have he : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro v hv
    change (e ≫ p) v ∈ V
    rw [hep]
    exact hv
  let pr := p.resLE V (p ⁻¹ᵁ V) le_rfl
  let er := e.resLE (p ⁻¹ᵁ V) V he
  let gr := g.resLE U (p ⁻¹ᵁ V) hVU
  have hep' : er ≫ pr = 𝟙 _ := by
    simp only [er, pr, Scheme.Hom.resLE_comp_resLE, hep]
    exact (Scheme.Hom.resLE_id (X := S) _).trans (Scheme.homOfLE_rfl _ _)
  have hpr : IsIso pr.appTop := by
    simp only [pr, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app]
    infer_instance
  have hinv : er.appTop ≫ pr.appTop = 𝟙 _ := by
    have h1 : pr.appTop ≫ er.appTop = 𝟙 _ := by
      rw [← Scheme.Hom.comp_appTop, hep']
      rfl
    rw [← cancel_epi pr.appTop, reassoc_of% h1, Category.comp_id]
  have key : gr = pr ≫ er ≫ gr := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.comp_appTop, Category.assoc, hinv, Category.comp_id]
  have := congrArg (· ≫ U.ι) key
  simpa [gr, er, pr, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc] using this

/-- The scheme-level form of the rigidity lemma, for the fibre product `Y ×_K Z` with second
projection `p`; no hypothesis on `Z` besides geometric connectedness is used. -/
private lemma rigidity_pullback {K : Type u} [Field K] {Y Z P : Scheme.{u}}
    (a : Y ⟶ Spec (CommRingCat.of K)) (b : Z ⟶ Spec (CommRingCat.of K))
    [Smooth a] [IsProper a] [GeometricallyConnected a] [GeometricallyConnected b]
    (y₀ : Spec (CommRingCat.of K) ⟶ Y) (hy₀ : y₀ ≫ a = 𝟙 _)
    (z₀ : Spec (CommRingCat.of K) ⟶ Z) (hz₀ : z₀ ≫ b = 𝟙 _)
    (q : P ⟶ Spec (CommRingCat.of K)) (p₀ : Spec (CommRingCat.of K) ⟶ P) (hp₀ : p₀ ≫ q = 𝟙 _)
    (g : pullback a b ⟶ P)
    (hy : pullback.lift (b ≫ y₀) (𝟙 Z) (by simp [hy₀]) ≫ g = b ≫ p₀)
    (hz : pullback.lift (𝟙 Y) (a ≫ z₀) (by simp [hz₀]) ≫ g = a ≫ p₀) :
    g = pullback.snd a b ≫ b ≫ p₀ := by
  let p := pullback.snd a b
  let e : Z ⟶ pullback a b := pullback.lift (b ≫ y₀) (𝟙 Z) (by simp [hy₀])
  have hep : e ≫ p = 𝟙 Z := pullback.lift_snd _ _ _
  have hiso : ∀ V : Z.Opens, IsIso (p.app V) :=
    smoothProperConnectedGlobalFunctions _ _ p inferInstance inferInstance inferInstance
  obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hc : ∀ t : Spec (CommRingCat.of K), p₀ t = p₀ s := fun t => by
    rw [Subsingleton.elim t s]
  have hconst : ∀ w : Z, (e ≫ g) w = p₀ s := by
    intro w
    rw [hy, Scheme.Hom.comp_apply]
    exact hc _
  have hclosed : IsClosed ({p₀ s} : Set P) := by
    have := isClosedImmersion_of_comp_eq_id q p₀ hp₀
    convert p₀.isClosedEmbedding.isClosed_range
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_range]
    exact ⟨fun h => ⟨s, h.symm⟩, fun ⟨t, ht⟩ => ht ▸ hc t⟩
  let T : Set Z := {z | ∀ x, p x = z → g x = p₀ s}
  have hTclosed : IsClosed T := by
    have hT : Tᶜ = p '' (g ⁻¹' {p₀ s}ᶜ) := by
      ext z
      simp [T, and_comm]
    rw [← isOpen_compl_iff, hT]
    exact p.isOpenMap _ (hclosed.isOpen_compl.preimage g.continuous)
  have hTopen : IsOpen T := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨U, hU, hcU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (x := p₀ s) (U := ⊤) trivial
    have hF : IsClosed (p '' (g ⁻¹' (U : Set P)ᶜ)) :=
      p.isClosedMap _ (U.isOpen.isClosed_compl.preimage g.continuous)
    let V : Z.Opens := ⟨(p '' (g ⁻¹' (U : Set P)ᶜ))ᶜ, hF.isOpen_compl⟩
    have hVU : p ⁻¹ᵁ V ≤ g ⁻¹ᵁ U := by
      intro x hx
      by_contra h
      exact hx ⟨x, h, rfl⟩
    have hloc := restrict_eq_of_affine p e g hep V U hU hVU
    refine ⟨V, fun w hw x hx => ?_, V.isOpen, ?_⟩
    · have hxV : x ∈ p ⁻¹ᵁ V := by
        change p x ∈ V
        rw [hx]
        exact hw
      have h1 := congrArg (fun f : (p ⁻¹ᵁ V).toScheme ⟶ P => f ⟨x, hxV⟩) hloc
      change g x = (p ≫ e ≫ g) x at h1
      rw [h1, Scheme.Hom.comp_apply]
      exact hconst _
    · rintro ⟨x, hx, rfl⟩
      exact hx (hz x rfl ▸ hcU)
  have hz₀T : z₀ s ∈ T := by
    intro x hx
    have hpb : IsPullback (pullback.lift (𝟙 Y) (a ≫ z₀) (by simp [hz₀])) a p z₀ := by
      refine IsPullback.of_right (h₁₂ := pullback.fst a b) (h₂₂ := b) ?_
        (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback a b)
      rw [pullback.lift_fst, hz₀]
      exact IsPullback.of_id_fst
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hpb x s hx
    rw [← Scheme.Hom.comp_apply, hz, Scheme.Hom.comp_apply]
    exact hc _
  have : ConnectedSpace Z := GeometricallyConnected.connectedSpace_of_subsingleton b
  have hTuniv : T = Set.univ := IsClopen.eq_univ ⟨hTclosed, hTopen⟩ ⟨_, hz₀T⟩
  have hpt : ∀ x, g x = (e ≫ g) (p x) := fun x => by
    rw [hconst]
    exact (hTuniv.symm ▸ Set.mem_univ (p x) : p x ∈ T) x rfl
  have hfac := factorizationOfGlobalFunctions _ _ _ p e g hep hiso hpt
  rw [hfac]
  change p ≫ e ≫ g = p ≫ b ≫ p₀
  rw [hy]

set_option backward.defeqAttrib.useBackward true in
/-- The rigidity lemma in `Over (Spec K)` for the cartesian monoidal product `Y ⊗ Z`. -/
private theorem rigidityTensor (K : Type u) [Field K] (Y Z P : Over (Spec (CommRingCat.of K)))
    [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
    [GeometricallyConnected Z.hom]
    (y₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Z)
    (p₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P)
    (g : Y ⊗ Z ⟶ P)
    (hy : lift (toUnit Z ≫ y₀) (𝟙 Z) ≫ g = toUnit Z ≫ p₀)
    (hz : lift (𝟙 Y) (toUnit Y ≫ z₀) ≫ g = toUnit Y ≫ p₀) :
    g = toUnit (Y ⊗ Z) ≫ p₀ := by
  have hy' := congrArg CommaMorphism.left hy
  have hz' := congrArg CommaMorphism.left hz
  simp only [Over.comp_left, Over.lift_left, Over.toUnit_left] at hy' hz'
  ext
  rw [Over.comp_left, Over.toUnit_left, Over.tensorObj_hom, pullback.condition, Category.assoc]
  exact rigidity_pullback Y.hom Z.hom y₀.left y₀.w z₀.left z₀.w P.hom p₀.left p₀.w g.left hy' hz'

set_option backward.defeqAttrib.useBackward true in
/-- Two-axis rigidity over any field when the first factor is smooth, proper and geometrically
connected and the second factor is smooth and geometrically connected. -/
theorem fieldTwoAxisRigiditySmoothSecond : FieldTwoAxisRigiditySmoothSecondStatement.{u} := by
  intro K _ Y Z P hYS hYP hYC _ hZC _ _ y₀ z₀ p₀ g hy hz
  have := hYS
  have := hYP
  have := hYC
  have := hZC
  let e : Y ⊗ Z ≅ Y ⨯ Z :=
    { hom := prod.lift (fst Y Z) (snd Y Z)
      inv := lift (prod.fst : Y ⨯ Z ⟶ Y) (prod.snd : Y ⨯ Z ⟶ Z)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp
      inv_hom_id := by
        apply prod.hom_ext <;> simp }
  have hterminal (X : Over (Spec (CommRingCat.of K))) :
      toUnit X = Over.mkIdTerminal.from X := toUnit_unique _ _
  have hy' : lift (toUnit Z ≫ y₀) (𝟙 Z) ≫ (e.hom ≫ g) = toUnit Z ≫ p₀ := by
    have he : lift (toUnit Z ≫ y₀) (𝟙 Z) ≫ e.hom =
        prod.lift (Over.mkIdTerminal.from Z ≫ y₀) (𝟙 Z) := by
      apply prod.hom_ext <;> simp [e, hterminal]
    rw [← Category.assoc, he, hy, hterminal]
  have hz' : lift (𝟙 Y) (toUnit Y ≫ z₀) ≫ (e.hom ≫ g) = toUnit Y ≫ p₀ := by
    have he : lift (𝟙 Y) (toUnit Y ≫ z₀) ≫ e.hom =
        prod.lift (𝟙 Y) (Over.mkIdTerminal.from Y ≫ z₀) := by
      apply prod.hom_ext <;> simp [e, hterminal]
    rw [← Category.assoc, he, hz, hterminal]
  have ht := rigidityTensor K Y Z P y₀ z₀ p₀ (e.hom ≫ g) hy' hz'
  have heq := congrArg (fun f : Y ⊗ Z ⟶ P => e.inv ≫ f) ht
  have hconstant : e.inv ≫ toUnit (Y ⊗ Z) =
      Over.mkIdTerminal.from (Y ⨯ Z) := toUnit_unique _ _
  simpa only [← Category.assoc, e.inv_hom_id, Category.id_comp, hconstant] using heq

end Langlands.AlgebraicGeometry
