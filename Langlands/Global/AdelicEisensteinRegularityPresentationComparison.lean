import Langlands.Global.AdelicEisensteinRegularityPresentationComparisonStatement
import Langlands.Global.AdelicEisensteinRegularityTorusComparison
import Langlands.Global.AdelicEisensteinRegularityAmbientTransport
import Langlands.Global.AdelicEisensteinRegularityParabolicTransport
import Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport
import Langlands.GroupScheme.Rational.RelativeWeylRootKernel
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Regularity thresholds of two root presentations of one parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

section Restrict

variable {F : Type u} [Field F] {H H' : GroupScheme (Spec (CommRingCat.of F))}

/-- Restriction of complex parameters along an inner automorphism is the identity, because
rational characters are invariant under conjugation. -/
theorem parameterRestrict_innerIso_hom (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ H.X)
    (lam : ComplexCharacterParameter F H) :
    parameterRestrict (H.innerIso n).hom lam = lam := by
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    change s ⊗ₜ[ℤ] characterRestrict (H.innerIso n).hom χ = s ⊗ₜ[ℤ] χ
    congr 1
    exact congrArg Additive.ofMul (rationalCharacters.comp_innerIso_hom χ n)
  | add x y hx hy => rw [map_add, hx, hy]

/-- Restriction along `e` followed by an inner automorphism of the target agrees with
restriction along `e`. -/
theorem parameterRestrict_comp_innerIso_hom (e : H' ⟶ H)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ H.X)
    (lam : ComplexCharacterParameter F H) :
    parameterRestrict (e ≫ (H.innerIso n).hom) lam = parameterRestrict e lam := by
  have h : parameterRestrict (F := F) (e ≫ (H.innerIso n).hom) =
      (parameterRestrict e).comp (parameterRestrict (H.innerIso n).hom) := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a χ => simp [parameterRestrict, characterRestrict_comp]
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  rw [h, LinearMap.comp_apply, parameterRestrict_innerIso_hom]

end Restrict

/-- **Regularity does not depend on the root presentation, up to the threshold.** The proof
conjugates the second presentation torus onto the first by a rational point of the common Levi
(`smoothMaximalSplitTorusConjugacy`), transports the second presentation through that inner
automorphism (`eisensteinRegularityAmbientTransport`), reads it as a presentation of the first
parabolic with the first split component (`eisensteinRegularityParabolicTransport`), and
compares two presentations of one parabolic with isomorphic tori
(`eisensteinRegularityTorusComparison`). -/
theorem rootPresentationRegularityComparison :
    RootPresentationRegularityComparisonStatement.{u} := by
  intro F _ _ G P₁ M₁ P₂ M₂ _ _ A₁ A₂ p₁ l₁ a₁ r₁ p₂ l₂ a₂ r₂ _ _ _ _ _ _ hA₁ hT₁ hA₂ hT₂
    hG e he hP hM R
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
  have : Mono (CommGroupScheme.groupHom r₂.data.f).hom.hom.left := inferInstance
  -- comparison of the first presentation with `s`
  obtain ⟨S, hS⟩ := eisensteinRegularityTorusComparison F G P₁ M₁ A₁ p₁ l₁ a₁ r₁ s hA₁ hT₁ hT₂
    ψ hG hψ.symm rfl R
  refine ⟨S, fun lam hreg => hS lam ?_⟩
  -- the parabolic map carrying the second parabolic onto the first
  let j : P₂ ⟶ P₁ := e ≫ (P₁.innerIso (z ≫ l₁.hom.hom)).hom
  have hj : j ≫ p₁ = p₂ ≫ E.hom := by
    change (e ≫ (P₁.innerIso (z ≫ l₁.hom.hom)).hom) ≫ p₁ = p₂ ≫ (G.innerIso g).hom
    rw [Category.assoc, innerIso_hom_comp p₁ (z ≫ l₁.hom.hom), ← Category.assoc, he]
    simp only [g, Grp.comp_hom_hom, Category.assoc]
  have hjlam : parameterRestrict j lam = parameterRestrict e lam :=
    parameterRestrict_comp_innerIso_hom e _ lam
  have htrans := eisensteinRegularityParabolicTransport F G P₁ M₁ P₂ M₂ r₂.data.T A₁ A₂
    (r₂.data.i ≫ E.hom) r₂.data.ν r₂.data.J (r₁.data.f ≫ ψ.hom) r₂.data.f p₁ l₁ a₁
    (p₂ ≫ E.hom) l₂ a₂ hsc r₂'.isCompatible hA₁ hA₂ hT₂ hG j hj S lam
  refine htrans.mp ?_
  rw [hjlam]
  have : Mono (r₂.compAmbientIso E).data.i.hom.hom.left :=
    inferInstanceAs (Mono (r₂.data.i ≫ E.hom).hom.hom.left)
  let : Fintype (relativeWeylGroup (r₂.compAmbientIso E).data.i) :=
    inferInstanceAs (Fintype (relativeWeylGroup (r₂.data.i ≫ E.hom)))
  exact (eisensteinRegularityAmbientTransport F G G P₂ M₂ A₂ p₂ l₂ a₂ r₂ E hA₂ hT₂ S
    (parameterRestrict e lam)).mpr hreg

end Langlands.Global
