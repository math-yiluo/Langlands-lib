/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.PointOfDerivation

/-!
# The infinitesimal points of a group scheme are its Lie algebra

The bridge from infinitesimal points to the Lie algebra is a bijection
(`AlgebraicGeometry.GrpObj.toLie_bijective`), turning the group law into the addition
(`AlgebraicGeometry.GrpObj.lieEquiv`).
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry
section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace GrpObj

omit [GrpObj G] in
/-- A derivation `𝒪_G → g_*𝒪_S` is a morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S`. -/
theorem homOfDerivation_bijective (g : S ⟶ G.left) :
    Function.Bijective (homOfDerivation G g) := by
  refine (Equiv.bijective _).comp ((Equiv.bijective _).comp ⟨fun D₁ D₂ h ↦ ?_, fun φ ↦ ?_⟩)
  · rw [← (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).fac D₁,
      ← (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).fac D₂]
    exact congrArg _ h
  · refine ⟨(PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' _).postcomp φ, ?_⟩
    apply (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' _).postcomp_injective
    rw [PresheafOfModulesOfCommRing.Derivation.Universal.fac]

/-- The morphisms `ω_{G/S} ⟶ 𝒪_S` attached to derivations along two morphisms `g₁ = g₂ = e` agree
only if the derivations do. -/
theorem heq_of_pullbackCongr_inv_comp_homOfDerivation_eq {g₁ g₂ : S ⟶ G.left}
    (h₁ : g₁ = unitSection G) (h₂ : g₂ = unitSection G)
    (D₁ : ((Scheme.Modules.pushforward g₁).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (D₂ : ((Scheme.Modules.pushforward g₂).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom)
    (h : (Scheme.Modules.pullbackCongr h₁).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₁ D₁ =
      (Scheme.Modules.pullbackCongr h₂).inv.app G.hom.cotangentSheaf ≫
        homOfDerivation G g₂ D₂) {V : (TopologicalSpace.Opens G.left)ᵒᵖ}
    (a : Γ(G.left, V.unop)) : D₁.d a ≍ D₂.d a := by
  subst h₁ h₂
  obtain rfl := (homOfDerivation_bijective G _).1 ((cancel_epi _).1 h)
  rfl

/-- The bridge is a bijection: a morphism `ω_{G/S} ⟶ 𝒪_S` is a derivation `d : 𝒪_G → e_*𝒪_S`, and
`a ↦ e^♯(a) + ε d(a)` is a morphism of schemes `S[ε] ⟶ G` over `S` reducing to the identity, since
its stalk maps are local, their reductions modulo `ε` being the local maps `e^♯`. -/
theorem toLie_bijective : Function.Bijective (toLie G) := by
  refine ⟨fun v w h ↦ ?_, fun φ ↦ ?_⟩
  · apply Subtype.ext
    apply Over.OverMorphism.ext
    rw [← pointOfDerivation_infDerivation G v.1, ← pointOfDerivation_infDerivation G w.1]
    exact pointOfDerivation_congr G
      ((ι_comp_left_eq G v.2).trans (ι_comp_left_eq G w.2).symm)
      (heq_of_pullbackCongr_inv_comp_homOfDerivation_eq G _ _ _ _ h)
  · obtain ⟨D, hD⟩ := (homOfDerivation_bijective G (unitSection G)).2
      ((Scheme.Modules.pullbackCongr (rfl : unitSection G = unitSection G)).hom.app
        G.hom.cotangentSheaf ≫ φ)
    -- Keep `v` opaque, which stops the kernel from unfolding it. (`generalize` would do the same,
    -- but it cannot elaborate the `Over.homMk` without an expected type.)
    obtain ⟨v, hvdef⟩ : ∃ v : Scheme.dualNumbersOver S ⟶ G,
        v = Over.homMk (pointOfDerivation G (unitSection G) D)
          (pointOfDerivation_comp_hom G _ D (unitSection_comp_hom G)) := ⟨_, rfl⟩
    have hv : v ∈ infPoints G := by
      subst hvdef
      rw [mem_infPoints]
      apply Over.OverMorphism.ext
      exact (ι_comp_pointOfDerivation G _ D).trans (one_left G).symm
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [toLie, omegaHom_eq_homOfDerivation, pullbackCongr_inv_comp_homOfDerivation G
      (ι_comp_left_eq G hv) rfl _ D (fun a ↦ by
        subst hvdef
        exact heq_of_eq (zero_add _)), hD,
      Iso.inv_hom_id_app_assoc]

/-- The infinitesimal points of `G` are its Lie algebra. (blueprint:
`def-wf-lie-algebra-derivation`) -/
noncomputable def lieEquiv : infPoints G ≃ Lie G :=
  Equiv.ofBijective _ (toLie_bijective G)

/-! ### The group law is the addition -/

omit [GrpObj G] in
/-- The derivation `𝒪_G → g_*𝒪_S` attached to a morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S`: the inverse of
`homOfDerivation`. -/
noncomputable def derivationOfHom (g : S ⟶ G.left)
    (φ : (Scheme.Modules.pullback g).obj G.hom.cotangentSheaf ⟶ Scheme.Modules.unitModule S) :
    ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom :=
  (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' _).postcomp
    (PresheafOfModules.sheafificationHomEquiv (𝟙 _)
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv G.hom.cotangentSheaf
        (Scheme.Modules.unitModule S) φ))

omit [GrpObj G] in
theorem derivationOfHom_homOfDerivation (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) :
    derivationOfHom G g (homOfDerivation G g D) = D := by
  rw [derivationOfHom, homOfDerivation, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact PresheafOfModulesOfCommRing.Derivation.Universal.fac _ _

omit [GrpObj G] in
theorem homOfDerivation_derivationOfHom (g : S ⟶ G.left)
    (φ : (Scheme.Modules.pullback g).obj G.hom.cotangentSheaf ⟶ Scheme.Modules.unitModule S) :
    homOfDerivation G g (derivationOfHom G g φ) = φ := by
  obtain ⟨D, rfl⟩ := (homOfDerivation_bijective G g).2 φ
  rw [derivationOfHom_homOfDerivation]

omit [GrpObj G] in
theorem derivationOfHom_add_d (g : S ⟶ G.left)
    (φ ψ : (Scheme.Modules.pullback g).obj G.hom.cotangentSheaf ⟶ Scheme.Modules.unitModule S)
    {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)) :
    (derivationOfHom G g (φ + ψ)).d a =
      (derivationOfHom G g φ).d a + (derivationOfHom G g ψ).d a := by
  rfl

omit [GrpObj G] in
theorem derivationOfHom_injective (g : S ⟶ G.left) :
    Function.Injective (derivationOfHom G g) := fun φ ψ h ↦ by
  rw [← homOfDerivation_derivationOfHom G g φ, h, homOfDerivation_derivationOfHom]

/-- Transporting a morphism `g^*Ω¹_{G/S} ⟶ 𝒪_S` along `g = e` restricts its derivation along
`e⁻¹V = g⁻¹V`. -/
theorem derivationOfHom_pullbackCongr_comp {g : S ⟶ G.left} (h : g = unitSection G)
    (φ : (Scheme.Modules.pullback g).obj G.hom.cotangentSheaf ⟶ Scheme.Modules.unitModule S)
    {V : (TopologicalSpace.Opens G.left)ᵒᵖ} (a : Γ(G.left, V.unop)) :
    (derivationOfHom G (unitSection G)
        ((Scheme.Modules.pullbackCongr h).inv.app G.hom.cotangentSheaf ≫ φ)).d a =
      S.presheaf.map (eqToHom (by rw [h])).op ((derivationOfHom G g φ).d a) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- The values of the derivation of the tangent vector `toLie v` are the `ε`-parts of `v^♯`,
restricted along `e⁻¹V = v⁻¹V`. -/
theorem derivationOfHom_toLie_d (v : infPoints G) {V : (TopologicalSpace.Opens G.left)ᵒᵖ}
    (a : Γ(G.left, V.unop)) :
    (derivationOfHom G (unitSection G) (toLie G v)).d a =
      S.presheaf.map (eqToHom (by rw [← ι_comp_left_eq G v.2]; rfl)).op
        (v.1.left.app V.unop a).snd := by
  rw [toLie, derivationOfHom_pullbackCongr_comp, omegaHom_eq_homOfDerivation,
    derivationOfHom_homOfDerivation]
  rfl

theorem dualNumbersιεOver_comp_mul (v w : infPoints G) :
    Scheme.dualNumbersιεOver S ≫
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1)) = v.1 := by
  rw [MonObj.comp_mul, Scheme.dualNumbersιεOver_comp_projεOver_assoc,
    Scheme.dualNumbersιεOver_comp_projδOver_assoc, (mem_infPoints G).1 w.2, MonObj.comp_one,
    mul_one]

theorem dualNumbersιδOver_comp_mul (v w : infPoints G) :
    Scheme.dualNumbersιδOver S ≫
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1)) = w.1 := by
  rw [MonObj.comp_mul, Scheme.dualNumbersιδOver_comp_projδOver_assoc,
    Scheme.dualNumbersιδOver_comp_projεOver_assoc, (mem_infPoints G).1 v.2, MonObj.comp_one,
    one_mul]

theorem dualNumbersFoldOver_comp_mul (v w : infPoints G) :
    Scheme.dualNumbersFoldOver S ≫
      ((Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1)) =
        (v * w).1 := by
  rw [MonObj.comp_mul, Scheme.dualNumbersFoldOver_comp_projεOver_assoc,
    Scheme.dualNumbersFoldOver_comp_projδOver_assoc]
  rfl

/-- The `ε`-part of `f^♯(a)` for a morphism `f : S[ε] ⟶ G` restricting to the identity section,
as a section over `e⁻¹V`. -/
noncomputable def epsPart (f : S.dualNumbers ⟶ G.left) (hf : S.dualNumbersι ≫ f = unitSection G)
    (V : G.left.Opens) (a : Γ(G.left, V)) : Γ(S, unitSection G ⁻¹ᵁ V) :=
  S.presheaf.map (eqToHom (by rw [hf]) :
    unitSection G ⁻¹ᵁ V ⟶ (S.dualNumbersι ≫ f) ⁻¹ᵁ V).op
    (TrivSqZeroExt.snd (R := Γ(S, (S.dualNumbersι ≫ f) ⁻¹ᵁ V))
      (M := Γ(S, (S.dualNumbersι ≫ f) ⁻¹ᵁ V)) (f.app V a))

/-- The `ε`-part of `g^♯(a)` for a morphism `g : S[ε][δ] ⟶ G` restricting to the identity
section, as a section over `e⁻¹V`. -/
noncomputable def epsPart₁₀ (g : S.dualNumbers.dualNumbers ⟶ G.left)
    (hg : S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g = unitSection G)
    (V : G.left.Opens) (a : Γ(G.left, V)) : Γ(S, unitSection G ⁻¹ᵁ V) :=
  S.presheaf.map (eqToHom (by rw [hg]) :
    unitSection G ⁻¹ᵁ V ⟶ (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g) ⁻¹ᵁ V).op
    (TrivSqZeroExt.snd (R := Γ(S, (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g) ⁻¹ᵁ V))
      (M := Γ(S, (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g) ⁻¹ᵁ V)) (g.app V a).fst)

/-- The `δ`-part of `g^♯(a)` for a morphism `g : S[ε][δ] ⟶ G` restricting to the identity
section, as a section over `e⁻¹V`. -/
noncomputable def epsPart₀₁ (g : S.dualNumbers.dualNumbers ⟶ G.left)
    (hg : S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g = unitSection G)
    (V : G.left.Opens) (a : Γ(G.left, V)) : Γ(S, unitSection G ⁻¹ᵁ V) :=
  S.presheaf.map (eqToHom (by rw [hg]) :
    unitSection G ⁻¹ᵁ V ⟶ (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g) ⁻¹ᵁ V).op
    (TrivSqZeroExt.fst (R := Γ(S, (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g) ⁻¹ᵁ V))
      (M := Γ(S, (S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g) ⁻¹ᵁ V)) (g.app V a).snd)

theorem epsPart_congr {f f' : S.dualNumbers ⟶ G.left} (h : f = f')
    (hf : S.dualNumbersι ≫ f = unitSection G) (hf' : S.dualNumbersι ≫ f' = unitSection G)
    (V : G.left.Opens) (a : Γ(G.left, V)) : epsPart G f hf V a = epsPart G f' hf' V a := by
  subst h
  rfl

theorem epsPart_fold_comp (g : S.dualNumbers.dualNumbers ⟶ G.left)
    (h : S.dualNumbersι ≫ S.dualNumbersFold ≫ g = unitSection G)
    (hg : S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g = unitSection G)
    (V : G.left.Opens) (a : Γ(G.left, V)) :
    epsPart G (S.dualNumbersFold ≫ g) h V a = epsPart₁₀ G g hg V a + epsPart₀₁ G g hg V a := by
  rw [epsPart, epsPart₁₀, epsPart₀₁, ← map_add]
  rfl

theorem epsPart_ιε_comp (g : S.dualNumbers.dualNumbers ⟶ G.left)
    (h : S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g = unitSection G)
    (V : G.left.Opens) (a : Γ(G.left, V)) :
    epsPart G (S.dualNumbers.dualNumbersι ≫ g) h V a = epsPart₁₀ G g h V a :=
  rfl

theorem epsPart_ιδ_comp (g : S.dualNumbers.dualNumbers ⟶ G.left)
    (h : S.dualNumbersι ≫ S.dualNumbersι.dualNumbers ≫ g = unitSection G)
    (hg : S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ g = unitSection G)
    (V : G.left.Opens) (a : Γ(G.left, V)) :
    epsPart G (S.dualNumbersι.dualNumbers ≫ g) h V a = epsPart₀₁ G g hg V a := by
  simp only [epsPart, epsPart₀₁, Scheme.Hom.comp_app, CommRingCat.comp_apply]
  erw [CommRingCat.snd_dualNumber_map]
  rfl

/-- The `ε`-part of the product of two infinitesimal points is the sum of their `ε`-parts: write
`v w` as `v_ε w_δ` with `δ` set equal to `ε`. -/
theorem epsPart_mul (v w : infPoints G) (V : G.left.Opens) (a : Γ(G.left, V)) :
    epsPart G (v * w).1.left (ι_comp_left_eq G (v * w).2) V a =
      epsPart G v.1.left (ι_comp_left_eq G v.2) V a +
        epsPart G w.1.left (ι_comp_left_eq G w.2) V a := by
  set z := (Scheme.dualNumbersProjεOver S ≫ v.1) * (Scheme.dualNumbersProjδOver S ≫ w.1)
  have hvw := congrArg Over.Hom.left (dualNumbersFoldOver_comp_mul G v w)
  have hv := congrArg Over.Hom.left (dualNumbersιεOver_comp_mul G v w)
  have hw := congrArg Over.Hom.left (dualNumbersιδOver_comp_mul G v w)
  have hz : S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ z.left = unitSection G := by
    have := ι_comp_left_eq G v.2
    rwa [← hv] at this
  have h₁ : S.dualNumbersι ≫ S.dualNumbersFold ≫ z.left = unitSection G := by
    have := ι_comp_left_eq G (v * w).2
    rwa [← hvw] at this
  have h₂ : S.dualNumbersι ≫ S.dualNumbersι.dualNumbers ≫ z.left = unitSection G := by
    have := ι_comp_left_eq G w.2
    rwa [← hw] at this
  rw [epsPart_congr G hvw.symm _ h₁, epsPart_congr G hv.symm _ hz, epsPart_congr G hw.symm _ h₂]
  have e₁ := epsPart_fold_comp G z.left h₁ hz V a
  rw [← epsPart_ιε_comp G z.left hz V a, ← epsPart_ιδ_comp G z.left h₂ hz V a] at e₁
  exact e₁

/-- The bridge turns the group law of the infinitesimal points into the addition of `Lie(G)`. -/
theorem lieEquiv_mul (v w : infPoints G) : lieEquiv G (v * w) = lieEquiv G v + lieEquiv G w := by
  apply derivationOfHom_injective G (unitSection G)
  ext V a : 3
  rw [derivationOfHom_add_d]
  change (derivationOfHom G (unitSection G) (toLie G (v * w))).d a =
    (derivationOfHom G (unitSection G) (toLie G v)).d a +
      (derivationOfHom G (unitSection G) (toLie G w)).d a
  rw [derivationOfHom_toLie_d, derivationOfHom_toLie_d, derivationOfHom_toLie_d]
  exact epsPart_mul G v w V.unop a

theorem lieEquiv_one : lieEquiv G 1 = 0 := by
  have h := lieEquiv_mul G 1 1
  rw [mul_one] at h
  exact (add_eq_left.mp h.symm)


/-- The infinitesimal points form a commutative group: their group law is the addition of tangent
vectors. -/
theorem isMulCommutative_infPoints : IsMulCommutative (infPoints G) :=
  ⟨⟨fun v w ↦ (lieEquiv G).injective (by rw [lieEquiv_mul, lieEquiv_mul, add_comm])⟩⟩

theorem lieEquiv_symm_add (x y : Lie G) :
    (lieEquiv G).symm (x + y) = (lieEquiv G).symm x * (lieEquiv G).symm y :=
  (lieEquiv G).injective (by simp [lieEquiv_mul])

end GrpObj

end InfPoints

end AlgebraicGeometry
