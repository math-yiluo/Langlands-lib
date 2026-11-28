import Langlands.Global.AdelicLeviPairingExpansion
import Langlands.Global.AdelicEisensteinCuspidalTestStandardizationReduction
import Langlands.Global.AdelicIntertwiningStandardizationProof
import Langlands.Global.AdelicEisensteinConjugateParabolicSeries
import Langlands.Global.AdelicEisensteinParabolicRangeTransport
import Langlands.Global.AdelicEisensteinRegularityPresentationComparison
import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation

/-! # Passage of the cuspidal tests of Eisenstein series to a standard parabolic

The proof of `EisensteinCuspidalTestStandardizationStatement`
(`eisensteinCuspidalTestStandardization`). For a presented parabolic `P = MU`, a standard family
`𝓕` and a maximal compact `K` in good position:

* a rational point `s` conjugates `P` and its Levi onto a standard parabolic `P_I` and its standard
  Levi (`StandardParabolicFamily.exists_standardConjugate`);
* the Eisenstein series of `P` on `φ` is `exp(-⟨λ, H(s)⟩)` times the Eisenstein series of `P_I` on
  `φ(s⁻¹ ·)` at the restricted parameter, where `H` is the height of the conjugated parabolic;
* constant terms and Levi pairings commute with scalar factors
  (`StandardParabolicFamily.constantTerm_const_mul`, `StandardParabolicFamily.leviPairing_const_mul`);
* regularity is transported by `rootPresentationRegularityComparison`, and root forms by the
  comparison `rootPresentationRootFunctionalComparison` proved here: for two root presentations of
  one parabolic the root forms of corresponding roots differ by positive factors. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  RealTorusSpace Langlands.Plancherel

section RootForms

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- On the restriction `f ≫ β` of a character `β` of the presentation torus, the real root form
of a presentation is the Weyl-invariant form of the torus at the restriction of the parameter
through a Levi lift of the torus. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.realRootFunctional_comp_eq
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (hG : IsConnectedReductive G)
    (t : r.data.T.toGrp ⟶ M) (ht : t ≫ l ≫ p = r.data.i) (β : characterLattice r.data.T)
    (x : RealCharacterParameter F P) :
    r.realRootFunctional hA hT (r.data.f ≫ β) x =
      relativeWeylInvariantForm r.data.i hT (realParameterRestriction (t ≫ l) x)
        ((1 : ℝ) ⊗ₜ[ℤ] β) := by
  rw [eisensteinAmbientParameterLift F G P M A p l a r hA hT t hG ht x,
    (weylInducedCharacterForm_compatible hA hT r.data.f r.data.i).2,
    rationalCharacterRestrictReal_tmul]
  rfl

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- Transport through an ambient isomorphism leaves the real root forms unchanged. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.realRootFunctional_compAmbientIso
    {G' : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G'.X.hom]
    (r : ParabolicRootPresentation p l a) (E : G ≅ G')
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    [Mono (r.compAmbientIso E).data.i.hom.hom.left]
    [Fintype (relativeWeylGroup (r.compAmbientIso E).data.i)]
    [Mono (CommGroupScheme.groupHom (r.compAmbientIso E).data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (β : characterLattice A) :
    (r.compAmbientIso E).realRootFunctional hA hT β = r.realRootFunctional hA hT β := by
  let : Mono (r.data.i ≫ E.hom).hom.hom.left :=
    inferInstanceAs (Mono (r.compAmbientIso E).data.i.hom.hom.left)
  let : Fintype (relativeWeylGroup (r.data.i ≫ E.hom)) :=
    inferInstanceAs (Fintype (relativeWeylGroup (r.compAmbientIso E).data.i))
  have hform := weylInducedCharacterForm_comp_ambientIso E r.data.i hA hT r.data.f
  change (weylInducedCharacterForm hA hT r.data.f (r.data.i ≫ E.hom)).flip ((1 : ℝ) ⊗ₜ[ℤ] β) ∘ₗ
      realParameterRestriction (a ≫ l) = _
  rw [hform]
  rfl

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- Transport through an ambient isomorphism leaves the complex root forms unchanged. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.rootFunctional_compAmbientIso
    {G' : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G'.X.hom]
    (r : ParabolicRootPresentation p l a) (E : G ≅ G')
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    [Mono (r.compAmbientIso E).data.i.hom.hom.left]
    [Fintype (relativeWeylGroup (r.compAmbientIso E).data.i)]
    [Mono (CommGroupScheme.groupHom (r.compAmbientIso E).data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp) (β : characterLattice A) :
    (r.compAmbientIso E).rootFunctional hA hT β = r.rootFunctional hA hT β := by
  unfold ParabolicRootPresentation.rootFunctional
  rw [r.realRootFunctional_compAmbientIso E hA hT β]

omit [NumberField F] [LocallyOfFiniteType G.X.hom] in
/-- Transport through an ambient isomorphism leaves the roots in the unipotent radical
unchanged. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.unipotentRoots_compAmbientIso
    {G' : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G'.X.hom]
    (r : ParabolicRootPresentation p l a) (E : G ≅ G') :
    (r.compAmbientIso E).unipotentRoots = r.unipotentRoots := by
  change {α | α ≠ 0 ∧ ∃ χ ∈ positiveRelativeRoots (r.data.i ≫ E.hom) r.data.ν,
    r.data.f ≫ χ = α} = r.unipotentRoots
  rw [positiveRelativeRoots_comp_iso]
  rfl

end RootForms

section TorusForms

variable {F : Type u} [Field F]
  {T T' : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ G}
  [Mono i.hom.hom.left] [Mono j.hom.hom.left]

omit [IsAffineHom G.X.hom] in
/-- An isomorphism of tori over the ambient group carries the real relative Weyl action of the
first torus to that of the second. -/
theorem characterRealCongr_relativeWeylRealCharacterAction (e : T ≅ T')
    (h : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom e.hom ≫ j)
    (w : relativeWeylGroup i) (x : Vstar T) :
    characterRealCongr e (relativeWeylRealCharacterAction i w x) =
      relativeWeylRealCharacterAction j (relativeWeylTransportEquiv e (Iso.refl G) h w)
        (characterRealCongr e x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s χ =>
    simp only [relativeWeylRealCharacterAction_tmul, characterRealCongr_tmul]
    exact congrArg (fun χ' => s ⊗ₜ[ℤ] χ')
      (relativeWeylCharacterAction_transport e (Iso.refl G) h w χ).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Two Weyl-invariant inner products on the real characters of a torus with a root reflection
datum agree up to a positive factor on each root: `C(x, β) = c_β B(x, β)`, by the coroot formula
`⟨x, β^∨⟩ B(β, β) = 2 B(x, β)`. -/
theorem weylInvariantForms_root_proportional
    (D : RelativeRootReflectionData i) (B C : LinearMap.BilinForm ℝ (Vstar T))
    (hB : IsWeylInvariantInnerProduct i B) (hC : IsWeylInvariantInnerProduct i C) :
    ∃ c : relativeRoots i → ℝ, (∀ β, 0 < c β) ∧ ∀ β x,
      C x ((1 : ℝ) ⊗ₜ[ℤ] β.val) = c β * B x ((1 : ℝ) ⊗ₜ[ℤ] β.val) := by
  let b (β : relativeRoots i) : Vstar T := (1 : ℝ) ⊗ₜ[ℤ] β.val
  have hbp (β : relativeRoots i) : 0 < B (b β) (b β) :=
    hB.2.1 _ (D.one_tmul_ne_zero i β)
  refine ⟨fun β => C (b β) (b β) / B (b β) (b β), fun β =>
    div_pos (hC.2.1 _ (D.one_tmul_ne_zero i β)) (hbp β), ?_⟩
  intro β x
  change C x (b β) = C (b β) (b β) / B (b β) (b β) * B x (b β)
  rw [div_mul_eq_mul_div, eq_div_iff (hbp β).ne']
  have hb := D.coroot_mul_form i B hB β x
  have hc := D.coroot_mul_form i C hC β x
  change _ * B (b β) (b β) = 2 * B x (b β) at hb
  change _ * C (b β) (b β) = 2 * C x (b β) at hc
  linear_combination (C (b β) (b β) / 2) * hb - (B (b β) (b β) / 2) * hc

end TorusForms

section TorusComparison

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- Two presentations of one parabolic, Levi and split component whose torus inclusions and
split-component factors are identified by an isomorphism of tori have the same roots in the
unipotent radical, and on each such root their root forms differ by a positive factor. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.rootFunctional_torusComparison
    (r s : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    [Mono s.data.i.hom.hom.left] [Fintype (relativeWeylGroup s.data.i)]
    [Mono (CommGroupScheme.groupHom s.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hT' : IsSplitTorus s.data.T.toGrp) (e : r.data.T ≅ s.data.T)
    (hG : IsConnectedReductive G) (he : r.data.i = CommGroupScheme.groupHom e.hom ≫ s.data.i)
    (hf : s.data.f = r.data.f ≫ e.hom) {α : characterLattice A} (hα : α ∈ r.unipotentRoots) :
    α ∈ s.unipotentRoots ∧ ∃ c : ℝ, 0 < c ∧ ∀ lam : ComplexCharacterParameter F P,
      s.rootFunctional hA hT' α lam = c * r.rootFunctional hA hT α lam := by
  classical
  have hsq : r.data.i ≫ (Iso.refl G).hom =
      CommGroupScheme.groupHom e.hom ≫ s.data.i := by simpa only [Iso.refl_hom, Category.comp_id]
  let := hG.smooth
  have hroots : r.unipotentRoots = s.unipotentRoots := by
    rw [r.unipotentRoots_eq_intrinsicPositiveRoots hG, s.unipotentRoots_eq_intrinsicPositiveRoots hG]
    exact r.intrinsicPositiveRoots_eq s
  obtain ⟨D, -⟩ := relativeRootReflectionExistence F G hG r.data.T r.data.i
    r.isCompatible.maximalSplit
  let B := relativeWeylInvariantForm r.data.i hT
  let C' := relativeWeylInvariantForm s.data.i hT'
  let E := characterRealCongr e
  let C := C'.compl₁₂ E.toLinearMap E.toLinearMap
  have hB : IsWeylInvariantInnerProduct r.data.i B :=
    ⟨relativeWeylInvariantForm_symm r.data.i hT,
      fun _ => relativeWeylInvariantForm_pos r.data.i hT,
      relativeWeylInvariantForm_invariant r.data.i hT⟩
  have hC : IsWeylInvariantInnerProduct r.data.i C := by
    refine ⟨fun x y => relativeWeylInvariantForm_symm s.data.i hT' (E x) (E y), ?_, ?_⟩
    · intro x hx
      exact relativeWeylInvariantForm_pos s.data.i hT'
        (fun h => hx (E.injective (h.trans E.map_zero.symm)))
    · intro w x y
      change C' (E (relativeWeylRealCharacterAction r.data.i w x))
        (E (relativeWeylRealCharacterAction r.data.i w y)) = C' (E x) (E y)
      dsimp only [E]
      rw [characterRealCongr_relativeWeylRealCharacterAction e hsq w x,
        characterRealCongr_relativeWeylRealCharacterAction e hsq w y]
      exact relativeWeylInvariantForm_invariant s.data.i hT' _ _ _
  obtain ⟨c, hc, hscale⟩ := weylInvariantForms_root_proportional D B C hB hC
  obtain ⟨t, _, ht⟩ := r.exists_leviTorusLift
  let t' := CommGroupScheme.groupHom e.inv ≫ t
  have ht' : t' ≫ l ≫ p = s.data.i := by
    dsimp only [t']
    rw [Category.assoc, ht, he, ← Category.assoc]
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ s.data.i = s.data.i
    rw [Iso.inv_hom_id]
    exact Category.id_comp _
  have hrestrict (x : RealCharacterParameter F P) :
      E (realParameterRestriction (t ≫ l) x) = realParameterRestriction (t' ≫ l) x := by
    induction x using TensorProduct.inductionOn with
    | tmul u χ =>
      change E (u ⊗ₜ[ℤ] characterRestrict (t ≫ l) χ) =
        u ⊗ₜ[ℤ] characterRestrict (t' ≫ l) χ
      rw [characterRealCongr_tmul]
      change u ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom e.inv)
          (characterRestrict (t ≫ l) χ) = u ⊗ₜ[ℤ] characterRestrict (t' ≫ l) χ
      rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, Category.assoc]
    | add x y hx hy => simp only [map_add, hx, hy]
  refine ⟨hroots ▸ hα, ?_⟩
  obtain ⟨_, β, hβ, hrβ⟩ := hα
  let root : relativeRoots r.data.i := ⟨β, hβ.1⟩
  let β' : characterLattice s.data.T := e.inv ≫ β
  have hsβ : s.data.f ≫ β' = α := by
    change s.data.f ≫ e.inv ≫ β = α
    rw [hf, Category.assoc, Iso.hom_inv_id_assoc]
    exact hrβ
  have hreal (x : RealCharacterParameter F P) :
      s.realRootFunctional hA hT' α x = c root * r.realRootFunctional hA hT α x := by
    have h1 := s.realRootFunctional_comp_eq hA hT' hG t' ht' β' x
    have h2 := r.realRootFunctional_comp_eq hA hT hG t ht β x
    rw [hsβ] at h1
    rw [hrβ] at h2
    rw [h1, h2, ← hrestrict]
    exact hscale root _
  refine ⟨c root, hc root, fun lam => ?_⟩
  induction lam using TensorProduct.inductionOn with
  | tmul z χ =>
    change z * (s.realRootFunctional hA hT' α ((1 : ℝ) ⊗ₜ[ℤ] χ) : ℂ) =
      c root * (z * (r.realRootFunctional hA hT α ((1 : ℝ) ⊗ₜ[ℤ] χ) : ℂ))
    rw [hreal]
    push_cast
    ring
  | add x y hx hy => simp only [map_add, hx, hy, mul_add]

end TorusComparison

section PresentationComparison

/-- **Root forms do not depend on the root presentation, up to positive factors.** Let `r₁`, `r₂`
be root presentations of parabolics `p₁ : P₁ → G`, `p₂ : P₂ → G` identified by `e : P₂ → P₁`
over `G`, with Levis of the same image. For every root `β₁` of the first split component in the
unipotent radical there are a root `β₂` of the second split component in the unipotent radical
and `c > 0` with `B₁(λ|_{A₁}, β₁) = c · B₂((λ|_{P₂})|_{A₂}, β₂)` for every parameter `λ` of `P₁`. -/
theorem rootPresentationRootFunctionalComparison {F : Type u} [Field F] [NumberField F]
    {G P₁ M₁ P₂ M₂ : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of F))}
    {p₁ : P₁ ⟶ G} {l₁ : M₁ ⟶ P₁} {a₁ : A₁.toGrp ⟶ M₁} (r₁ : ParabolicRootPresentation p₁ l₁ a₁)
    {p₂ : P₂ ⟶ G} {l₂ : M₂ ⟶ P₂} {a₂ : A₂.toGrp ⟶ M₂} (r₂ : ParabolicRootPresentation p₂ l₂ a₂)
    [Mono r₁.data.i.hom.hom.left] [Fintype (relativeWeylGroup r₁.data.i)]
    [Mono (CommGroupScheme.groupHom r₁.data.f).hom.hom.left]
    [Mono r₂.data.i.hom.hom.left] [Fintype (relativeWeylGroup r₂.data.i)]
    [Mono (CommGroupScheme.groupHom r₂.data.f).hom.hom.left]
    (hA₁ : IsSplitTorus A₁.toGrp) (hT₁ : IsSplitTorus r₁.data.T.toGrp)
    (hA₂ : IsSplitTorus A₂.toGrp) (hT₂ : IsSplitTorus r₂.data.T.toGrp)
    (hG : IsConnectedReductive G) (e : P₂ ⟶ P₁) (he : e ≫ p₁ = p₂)
    (hP : SubgroupFunctor.range p₁ = SubgroupFunctor.range p₂)
    (hM : SubgroupFunctor.range (l₁ ≫ p₁) = SubgroupFunctor.range (l₂ ≫ p₂))
    {β₁ : characterLattice A₁} (hβ₁ : β₁ ∈ r₁.unipotentRoots) :
    ∃ β₂ ∈ r₂.unipotentRoots, ∃ c : ℝ, 0 < c ∧ ∀ lam : ComplexCharacterParameter F P₁,
      r₁.rootFunctional hA₁ hT₁ β₁ lam =
        c * r₂.rootFunctional hA₂ hT₂ β₂ (parameterRestrict e lam) := by
  -- the common Levi and the two torus lifts
  have hP₁c : IsClosedSubgroup p₁ := r₁.isCompatible.parabolic.isClosedSubgroup
  have hP₂c : IsClosedSubgroup p₂ := r₂.isCompatible.parabolic.isClosedSubgroup
  have hL₁c : IsClosedSubgroup (l₁ ≫ p₁) :=
    r₁.isCompatible.levi.isClosedSubgroup.comp hP₁c
  have hL₂c : IsClosedSubgroup (l₂ ≫ p₂) :=
    r₂.isCompatible.levi.isClosedSubgroup.comp hP₂c
  let c : M₂ ≅ M₁ := hL₂c.sourceIsoOfRangeEq hL₁c hM.symm
  have hc : c.hom ≫ l₁ ≫ p₁ = l₂ ≫ p₂ := hL₂c.sourceIsoOfRangeEq_hom_comp hL₁c hM.symm
  obtain ⟨t₁, ht₁max, ht₁⟩ := r₁.exists_leviTorusLift
  obtain ⟨t₂, ht₂max, ht₂⟩ := r₂.exists_leviTorusLift
  let : Smooth M₁.X.hom := r₁.isCompatible.levi.isConnectedReductive.smooth
  let : IsAffineHom M₁.X.hom := r₁.isCompatible.levi.isConnectedReductive.isAffineHom
  let : ConnectedSpace M₁.X.left := r₁.isCompatible.levi.isConnectedReductive.connectedSpace
  obtain ⟨z, φ, hφ⟩ := smoothMaximalSplitTorusConjugacy F M₁ r₂.data.T r₁.data.T
    (t₂ ≫ c.hom) t₁ (ht₂max.comp_iso c) ht₁max
  -- the conjugating point of `G`, inside the Levi
  let g : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X := z ≫ (l₁ ≫ p₁).hom.hom
  have hg : r₂.data.i ≫ (G.innerIso g).hom = φ.hom ≫ r₁.data.i := by
    have h1 : (M₁.innerIso z).hom ≫ l₁ ≫ p₁ = (l₁ ≫ p₁) ≫ (G.innerIso g).hom :=
      innerIso_hom_comp (l₁ ≫ p₁) z
    rw [← ht₂, ← ht₁, ← hc]
    calc (t₂ ≫ c.hom ≫ l₁ ≫ p₁) ≫ (G.innerIso g).hom
        = (t₂ ≫ c.hom) ≫ ((l₁ ≫ p₁) ≫ (G.innerIso g).hom) := by simp only [Category.assoc]
      _ = ((t₂ ≫ c.hom) ≫ (M₁.innerIso z).hom) ≫ l₁ ≫ p₁ := by
        rw [← h1]
        simp only [Category.assoc]
      _ = φ.hom ≫ t₁ ≫ l₁ ≫ p₁ := by rw [hφ, Category.assoc]
  -- the second presentation transported by the inner automorphism
  let E := G.innerIso g
  let r₂' := r₂.compAmbientIso E
  have : Mono (r₂.data.i ≫ E.hom).hom.hom.left := by
    let : IsIso E.hom.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso E)).hom)
    change Mono (r₂.data.i.hom.hom.left ≫ E.hom.hom.hom.left)
    infer_instance
  let : Fintype (relativeWeylGroup (r₂.data.i ≫ E.hom)) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup _ r₂'.isCompatible.maximalSplit)
  -- ranges are unchanged by conjugation with a point of the Levi
  have hPg : SubgroupFunctor.range (p₂ ≫ E.hom) = SubgroupFunctor.range p₁ := by
    rw [(SubgroupFunctor.range_comp_iso_eq_iff p₂ p₁ E).mpr hP.symm]
    have h := range_comp_innerIso_of_mem p₁ (z ≫ l₁.hom.hom)
    simpa only [g, E, Grp.comp_hom_hom, Category.assoc] using h
  have hMg : SubgroupFunctor.range (l₂ ≫ p₂ ≫ E.hom) = SubgroupFunctor.range (l₁ ≫ p₁) := by
    have h1 := (SubgroupFunctor.range_comp_iso_eq_iff (l₂ ≫ p₂) (l₁ ≫ p₁) E).mpr hM.symm
    rw [Category.assoc, Category.assoc] at h1
    rw [h1]
    simpa only [Category.assoc] using range_comp_innerIso_of_mem (l₁ ≫ p₁) z
  -- the transported torus isomorphism, in commutative group schemes
  let ψ : r₁.data.T ≅ r₂.data.T := (CommGroupScheme.isoOfGroupIso φ).symm
  have hψ : CommGroupScheme.groupHom ψ.hom ≫ r₂.data.i ≫ E.hom = r₁.data.i := by
    change φ.inv ≫ r₂.data.i ≫ E.hom = r₁.data.i
    rw [hg, Iso.inv_hom_id_assoc]
  have : Mono (CommGroupScheme.groupHom (r₁.data.f ≫ ψ.hom)).hom.hom.left := by
    let : IsIso φ.inv.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso φ.symm)).hom)
    change Mono ((CommGroupScheme.groupHom r₁.data.f).hom.hom.left ≫ φ.inv.hom.hom.left)
    infer_instance
  -- the second presentation, read as a presentation of the first parabolic
  have hsc : ParabolicRootPresentationData.IsCompatible
      ⟨r₂.data.T, r₂.data.i ≫ E.hom, r₂.data.ν, r₂.data.J, r₁.data.f ≫ ψ.hom⟩ p₁ l₁ a₁ := by
    obtain ⟨ζ, hζ, hζP, hζM⟩ := r₂'.isCompatible.realization
    exact {
      parabolic := r₁.isCompatible.parabolic
      levi := r₁.isCompatible.levi
      splitComponent := r₁.isCompatible.splitComponent
      maximalSplit := r₂'.isCompatible.maximalSplit
      generic := r₂'.isCompatible.generic
      subset_simpleRoots := r₂'.isCompatible.subset_simpleRoots
      parabolic_eq := hPg.symm.trans r₂'.isCompatible.parabolic_eq
      levi_eq := hMg.symm.trans r₂'.isCompatible.levi_eq
      factor_comp := by
        change (CommGroupScheme.groupHom r₁.data.f ≫ CommGroupScheme.groupHom ψ.hom) ≫
          r₂.data.i ≫ E.hom = a₁ ≫ l₁ ≫ p₁
        rw [Category.assoc, hψ, r₁.isCompatible.factor_comp]
      minimal := r₂'.isCompatible.minimal
      minimal_le := hPg ▸ r₂'.isCompatible.minimal_le
      realization := ⟨ζ, hζ, hPg.symm.trans hζP, hMg.symm.trans hζM⟩ }
  let s : ParabolicRootPresentation p₁ l₁ a₁ := ⟨_, hsc⟩
  -- comparison of the first presentation with `s`
  obtain ⟨hβs, κ, hκ, hκs⟩ := r₁.rootFunctional_torusComparison s hA₁ hT₁ hT₂ ψ hG hψ.symm rfl
    hβ₁
  obtain ⟨hβ0, χ, hχ, hχβ⟩ := hβs
  have hχ₂ : χ ∈ positiveRelativeRoots r₂.data.i r₂.data.ν := by
    have h := hχ
    change χ ∈ positiveRelativeRoots (r₂.data.i ≫ E.hom) r₂.data.ν at h
    rwa [positiveRelativeRoots_comp_iso] at h
  -- the parabolic map carrying the second parabolic onto the first
  let j : P₂ ⟶ P₁ := e ≫ (P₁.innerIso (z ≫ l₁.hom.hom)).hom
  have hj : j ≫ p₁ = p₂ ≫ E.hom := by
    change (e ≫ (P₁.innerIso (z ≫ l₁.hom.hom)).hom) ≫ p₁ = p₂ ≫ (G.innerIso g).hom
    rw [Category.assoc, innerIso_hom_comp p₁ (z ≫ l₁.hom.hom), ← Category.assoc, he]
    simp only [g, Grp.comp_hom_hom, Category.assoc]
  refine ⟨r₂.data.f ≫ χ, ⟨fun h0 => hβ0 ?_, χ, hχ₂, rfl⟩, κ⁻¹, inv_pos.mpr hκ, fun lam => ?_⟩
  · rw [← hχβ]
    exact (s.restrict_positiveRoot_eq_zero_iff hχ).mpr
      ((r₂.restrict_positiveRoot_eq_zero_iff hχ₂).mp h0)
  · have h2 := rootFunctional_parameterRestrict_eq_of_comp_eq hsc r₂'.isCompatible hA₁ hA₂ hT₂ hG
      j hj χ lam
    have : Mono (r₂.compAmbientIso E).data.i.hom.hom.left :=
      inferInstanceAs (Mono (r₂.data.i ≫ E.hom).hom.hom.left)
    let : Fintype (relativeWeylGroup (r₂.compAmbientIso E).data.i) :=
      inferInstanceAs (Fintype (relativeWeylGroup (r₂.data.i ≫ E.hom)))
    have : Mono (CommGroupScheme.groupHom (r₂.compAmbientIso E).data.f).hom.hom.left :=
      inferInstanceAs (Mono (CommGroupScheme.groupHom r₂.data.f).hom.hom.left)
    have h3 : (r₂.compAmbientIso E).rootFunctional hA₂ hT₂ (r₂.data.f ≫ χ) =
        r₂.rootFunctional hA₂ hT₂ (r₂.data.f ≫ χ) :=
      r₂.rootFunctional_compAmbientIso E hA₂ hT₂ _
    have h4 : s.rootFunctional hA₁ hT₂ β₁ lam = r₂.rootFunctional hA₂ hT₂ (r₂.data.f ≫ χ)
        (parameterRestrict e lam) := by
      rw [← parameterRestrict_comp_innerIso_hom e (z ≫ l₁.hom.hom) lam, ← h3, ← hχβ]
      exact h2.symm
    rw [← h4, hκs lam, ← mul_assoc]
    push_cast
    rw [inv_mul_cancel₀ (by exact_mod_cast hκ.ne'), one_mul]

end PresentationComparison

section ScalarTests

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- Constant terms along standard parabolics commute with multiplication by a scalar. -/
theorem StandardParabolicFamily.constantTerm_const_mul (𝓕 : StandardParabolicFamily F G)
    (J : StandardIndex F G 𝓕.i 𝓕.ν) (c : ℂ) (f : AdelicGroupPoints F G → ℂ) :
    𝓕.constantTerm J (fun x => c * f x) = fun x => c * 𝓕.constantTerm J f x := by
  funext x
  unfold StandardParabolicFamily.constantTerm subgroupConstantTerm
  exact MeasureTheory.integral_const_mul c _

end ScalarTests

section Main

attribute [local instance] StandardParabolicFamily.isClosedImmersion_p

/-- **Passage of the cuspidal tests of Eisenstein series to a standard parabolic.** The proof of
`EisensteinCuspidalTestStandardizationStatement`: a rational point `s` conjugates `P` and its
Levi onto a standard parabolic `P_I` and its standard Levi; the Eisenstein series of `P` is a
height scalar at `s` times the Eisenstein series of `P_I` on the left translate `φ(s⁻¹ ·)` at the
restricted parameter; constant terms and Levi pairings are linear in the function. -/
theorem eisensteinCuspidalTestStandardization :
    EisensteinCuspidalTestStandardizationStatement.{u} := by
  classical
  intro F _ _ G P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU 𝓕 K hK h₀ hLevi N d rho hsmooth
    hcalc φ hKmax hrho hφ
  have hp : IsParabolicSubgroup p := r.isCompatible.parabolic
  have hl : IsRationalLeviSubgroup l := r.isCompatible.levi
  -- a rational conjugate of `P` is standard, compatibly with the Levis
  obtain ⟨I, s, eP, κ, heP, hκ, hUrange⟩ := 𝓕.exists_standardConjugate p iU l hp hU hl
  have : IsClosedImmersion (p ≫ (G.innerIso s).hom).hom.hom.left :=
    hp.isClosedSubgroup.comp_iso (G.innerIso s)
  have heP' : eP.inv ≫ 𝓕.p I = p ≫ (G.innerIso s).hom := by
    rw [← heP, Iso.inv_hom_id_assoc]
  have hrange : SubgroupFunctor.range (𝓕.p I) =
      SubgroupFunctor.range (p ≫ (G.innerIso s).hom) :=
    le_antisymm (SubgroupFunctor.range_le_of_factor eP.hom heP)
      (SubgroupFunctor.range_le_of_factor eP.inv heP')
  have hMrange : SubgroupFunctor.range (𝓕.l I ≫ 𝓕.p I) =
      SubgroupFunctor.range (l ≫ p ≫ (G.innerIso s).hom) := by
    have h1 : κ.hom ≫ l ≫ p ≫ (G.innerIso s).hom = 𝓕.l I ≫ 𝓕.p I := by
      rw [reassoc_of% hκ, heP]
    have h2 : κ.inv ≫ 𝓕.l I ≫ 𝓕.p I = l ≫ p ≫ (G.innerIso s).hom := by
      rw [← h1, Iso.inv_hom_id_assoc]
    exact le_antisymm (SubgroupFunctor.range_le_of_factor κ.hom h1)
      (SubgroupFunctor.range_le_of_factor κ.inv h2)
  have hK' : IsIwasawaCompact (p ≫ (G.innerIso s).hom) K :=
    (𝓕.isIwasawaCompact_of_minimal h₀ I).of_range_eq hrange
  -- the parameter map and the new inducing function
  let iota : ComplexCharacterParameter F P ≃ₗ[ℂ] ComplexCharacterParameter F (𝓕.P I) :=
    parameterRestrictIsoEquiv eP
  have hinv (lam : ComplexCharacterParameter F P) : parameterRestrict eP.inv (iota lam) = lam :=
    iota.symm_apply_apply lam
  have hφ' : 𝓕.IsAutomorphicOn hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho I
      (fun x => φ ((innerAdelicPoint F G s)⁻¹ * x)) := by
    have h := IsAutomorphicFunctionOn.leftTranslate hcalc hφ (innerAdelicPoint F G s)⁻¹
    rw [inv_inv, ← parabolicQuotientSubgroup_conjugate s,
      parabolicQuotientSubgroup_eq_of_range_eq hUrange hMrange.symm] at h
    exact h
  -- the series of `P` is a height scalar times the series of `P_I`
  have hseries (lam : ComplexCharacterParameter F P) : hK.eisensteinSeries φ lam =
      fun g => hK'.heightPower (-lam) (innerAdelicPoint F G s) *
        (𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries
          (fun x => φ ((innerAdelicPoint F G s)⁻¹ * x)) (iota lam) g := by
    funext g
    have h1 := hK.eisensteinSeries_conjugate_parabolic s hK' hl hU hφ.1 lam g
    have h2 := hK'.eisensteinSeries_eq_of_range_eq (𝓕.isIwasawaCompact_of_minimal h₀ I) eP.hom
      heP hrange.symm (fun x => φ ((innerAdelicPoint F G s)⁻¹ * x)) lam g
    change _ = _ * (𝓕.isIwasawaCompact_of_minimal h₀ I).eisensteinSeries
      (fun x => φ ((innerAdelicPoint F G s)⁻¹ * x)) (parameterRestrict eP.hom lam) g
    rw [← h2, h1, ← mul_assoc, hK'.heightPower_neg_mul, one_mul]
  -- the instances of the standard presentation
  have hmonoF : ∀ J, Mono (CommGroupScheme.groupHom (𝓕.f J)).hom.hom.left := by
    intro J
    let := (𝓕.isCompatible J).splitComponent.1.isSplitSubtorus.mono
    let := (𝓕.isCompatible J).levi.isClosedSubgroup.mono
    let := (𝓕.isCompatible J).parabolic.isClosedSubgroup.mono
    have : Mono (𝓕.a J ≫ 𝓕.l J ≫ 𝓕.p J).hom.hom.left := by
      change Mono ((𝓕.a J).hom.hom.left ≫ (𝓕.l J).hom.hom.left ≫ (𝓕.p J).hom.hom.left)
      infer_instance
    exact mono_of_mono_fac
      (congrArg (fun z => z.hom.hom.left) (𝓕.isCompatible J).factor_comp)
  let instW : Fintype (relativeWeylGroup 𝓕.i) :=
    @Fintype.ofFinite _ (hG.finite_relativeWeylGroup _ 𝓕.maximalSplit)
  have := hmonoF I
  -- the presentation of `P` transported by the inner automorphism of `s`
  have : IsIso (G.innerIso s).hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso (G.innerIso s))).hom)
  have : Mono (r.compAmbientIso (G.innerIso s)).data.i.hom.hom.left := by
    change Mono (r.data.i.hom.hom.left ≫ (G.innerIso s).hom.hom.hom.left)
    infer_instance
  let instW' : Fintype (relativeWeylGroup (r.compAmbientIso (G.innerIso s)).data.i) :=
    @Fintype.ofFinite _
      (hG.finite_relativeWeylGroup _ (r.compAmbientIso (G.innerIso s)).isCompatible.maximalSplit)
  have : Mono (CommGroupScheme.groupHom (r.compAmbientIso (G.innerIso s)).data.f).hom.hom.left :=
    inferInstanceAs (Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
  have hAI := (𝓕.isCompatible I).splitComponent.isCentralSplitTorus.1.1
  have hTI := 𝓕.maximalSplit.isSplitSubtorus.1
  refine ⟨I, iota, 1, fun _ lam => hK'.heightPower (-lam) (innerAdelicPoint F G s),
    fun _ x => φ ((innerAdelicPoint F G s)⁻¹ * x), fun _ => hφ', fun _ n e => ?_, instW, hmonoF,
    fun R => ?_, fun β' hβ' => ?_, 0, fun lam _ J ψ _ g => ?_⟩
  · -- the coefficient is the exponential of a linear form
    exact (((complexParameterPairing F P).flip (hK'.height (innerAdelicPoint F G s))).comp
      (-e.toLinearMap)).toContinuousLinearMap.differentiable.cexp
  · -- regularity transport
    obtain ⟨R', hR'⟩ := rootPresentationRegularityComparison F G (𝓕.P I) (𝓕.M I) P M (𝓕.A I) A
      (𝓕.p I) (𝓕.l I) (𝓕.a I) (𝓕.rootPresentation I) (p ≫ (G.innerIso s).hom) l a
      (r.compAmbientIso (G.innerIso s)) hAI hTI hA hT hG eP.inv heP' hrange hMrange R
    refine ⟨R', fun lam hlam => hR' (iota lam) ?_⟩
    rw [hinv]
    exact (eisensteinRegularityAmbientTransport F G G P M A p l a r (G.innerIso s) hA hT R'
      lam).mpr hlam
  · -- root forms
    obtain ⟨β, hβ, c, hc, hcf⟩ := rootPresentationRootFunctionalComparison
      (𝓕.rootPresentation I) (r.compAmbientIso (G.innerIso s)) hAI hTI hA hT hG eP.inv heP'
      hrange hMrange hβ'
    refine ⟨β, (r.unipotentRoots_compAmbientIso (G.innerIso s)) ▸ hβ, (c : ℂ),
      Complex.ofReal_ne_zero.mpr hc.ne', LinearMap.ext fun lam => ?_⟩
    rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, hcf, hinv,
      r.rootFunctional_compAmbientIso (G.innerIso s) hA hT β]
  · -- the tested identity
    rw [hseries lam, 𝓕.constantTerm_const_mul, 𝓕.leviPairing_const_mul, Fin.sum_univ_one]

end Main

end Langlands.Global
