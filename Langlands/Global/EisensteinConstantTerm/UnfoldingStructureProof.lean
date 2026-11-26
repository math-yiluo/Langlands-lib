import Langlands.Global.EisensteinConstantTerm.UnfoldingIdentification
import Langlands.Global.EisensteinConstantTerm.UnfoldingAdelic

/-! # The subgroup structure of the unfolding identity from the dynamic description -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite NumberField
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.GroupScheme.Dynamic AdelicGroupPoints
  Langlands.Automorphic.GroupSchemeFunctions

section Abstract

variable {𝒢 : Type*} [Group 𝒢]

/-- A semidirect decomposition `H = K ⋊ A` of subgroups of `𝒢` compatible with a subgroup `R`:
`K` is normal in `H`, `K ∩ A = 1`, `H = K A`, and the `A`-component of an element of `H ∩ R`
lies in `R`. -/
def IsRationalSemidirect (R H K A : Subgroup 𝒢) : Prop :=
  K ≤ H ∧ A ≤ H ∧ (∀ x ∈ H, ∀ k ∈ K, x * k * x⁻¹ ∈ K) ∧ (∀ a ∈ A, a ∈ K → a = 1) ∧
    (∀ x ∈ H, ∃ k ∈ K, ∃ a ∈ A, k * a = x) ∧
    (∀ x ∈ H, x ∈ R → ∀ k ∈ K, ∀ a ∈ A, k * a = x → a ∈ R)

/-- Semidirect decompositions are carried by group automorphisms preserving `R`. -/
theorem IsRationalSemidirect.map {R H K A : Subgroup 𝒢} (h : IsRationalSemidirect R H K A)
    (c : 𝒢 ≃* 𝒢) (hc : ∀ x, c x ∈ R ↔ x ∈ R) :
    IsRationalSemidirect R (H.map c.toMonoidHom) (K.map c.toMonoidHom) (A.map c.toMonoidHom) := by
  obtain ⟨hKH, hAH, hn, hd, hdec, hrat⟩ := h
  simp only [IsRationalSemidirect, Subgroup.mem_map_equiv]
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx k hk => ?_, fun a ha hak => ?_,
    fun x hx => ?_, fun x hx hxR k hk a ha hka => ?_⟩
  · rw [Subgroup.mem_map_equiv]; exact hKH ((Subgroup.mem_map_equiv).mp hx)
  · rw [Subgroup.mem_map_equiv]; exact hAH ((Subgroup.mem_map_equiv).mp hx)
  · simpa [map_mul, map_inv] using hn _ hx _ hk
  · have := hd _ ha hak
    simpa using congrArg c this
  · obtain ⟨k, hk, a, ha, hka⟩ := hdec _ hx
    refine ⟨c k, by simpa using hk, c a, by simpa using ha, ?_⟩
    rw [← map_mul, hka, c.apply_symm_apply]
  · have := hrat _ hx ((hc _).mp (by simpa using hxR)) _ hk _ ha
      (by rw [← map_mul, hka])
    have h2 := (hc _).mpr this
    rwa [c.apply_symm_apply] at h2

end Abstract

section Functor

variable (F : Type u) [Field F] [NumberField F] {G H : GroupScheme (Spec (CommRingCat.of F))}

/-- The rational-to-adelic map on points of a subgroup functor. -/
theorem rational_mem_carrier (W : SubgroupFunctor G) {x : RationalGroupPoints F G}
    (hx : x ∈ AdelicSubgroupPoints.rationalPoints F G W) :
    AdelicGroupPoints.rational F G x ∈ AdelicSubgroupPoints.adelicPoints F G W :=
  (AdelicSubgroupPoints.rational F G W ⟨x, hx⟩).property

/-- Adelic points of the range of `j` followed by the inverse inner automorphism of `w`. -/
theorem mem_adelicPoints_range_comp_innerIso_inv (j : H ⟶ G)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (x : AdelicGroupPoints F G) :
    x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (j ≫ (G.innerIso w).inv)) ↔
      innerAdelicPoint F G w * x * (innerAdelicPoint F G w)⁻¹ ∈
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) := by
  have h := MultiplicativeTypeGaloisExactness.range_comp_iso_hom j (G.innerIso w).symm
  rw [Iso.symm_hom, Iso.symm_inv] at h
  change x ∈ (SubgroupFunctor.range (j ≫ (G.innerIso w).inv)).carrier _ ↔ _
  rw [h, SubgroupFunctor.mem_comap, comp_innerIso_hom]
  rfl

variable [IsSeparated G.X.hom] (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (M W : SubgroupFunctor G)

/-- **The rational semidirect decomposition from a dynamic product.** If on every test scheme
`W = (Z(χ) ∩ M) U(χ)` with `U(χ) ⊆ W ⊆ P(χ)`, and every rational point of `W(𝔸)` comes from
`W(F)`, then `W(𝔸) = U(χ)(𝔸) ⋊ (Z(χ) ∩ M)(𝔸)` compatibly with the rational points. -/
theorem isRationalSemidirect_of_dynamic
    (hprod : ∀ X : Over (Spec (CommRingCat.of F)),
      (↑(W.carrier X) : Set (X ⟶ G.X)) =
        (↑((centralizer χ ⊓ M).carrier X) : Set (X ⟶ G.X)) *
          (↑((unipotent χ).carrier X) : Set (X ⟶ G.X)))
    (hUW : unipotent χ ≤ W) (hWP : W ≤ parabolic χ)
    (hdesc : ∀ x ∈ AdelicSubgroupPoints.adelicPoints F G W,
      x ∈ AdelicGroupPoints.rationalSubgroup F G →
        ∃ x₀ ∈ AdelicSubgroupPoints.rationalPoints F G W, AdelicGroupPoints.rational F G x₀ = x) :
    IsRationalSemidirect (AdelicGroupPoints.rationalSubgroup F G)
      (AdelicSubgroupPoints.adelicPoints F G W)
      (AdelicSubgroupPoints.adelicPoints F G (unipotent χ))
      (AdelicSubgroupPoints.adelicPoints F G (centralizer χ ⊓ M)) := by
  have hA := hprod ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (AdeleRing (𝓞 F) F))))
  have hF := hprod ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F F)))
  have huniq : ∀ (T : Over (Spec (CommRingCat.of F))) (g l l' : T ⟶ G.X),
      HasLimit χ g l → HasLimit χ g l' → l = l' := fun _ _ _ _ h h' => h.unique χ h'
  have hdisj : ∀ a ∈ AdelicSubgroupPoints.adelicPoints F G (centralizer χ ⊓ M),
      a ∈ AdelicSubgroupPoints.adelicPoints F G (unipotent χ) → a = 1 :=
    fun a ha hak => eq_one_of_mem_centralizer_of_mem_unipotent χ huniq ha.1 hak
  have hAW : ∀ a ∈ AdelicSubgroupPoints.adelicPoints F G (centralizer χ ⊓ M),
      a ∈ AdelicSubgroupPoints.adelicPoints F G W := by
    intro a ha
    exact (Set.ext_iff.mp hA a).mpr (Set.mem_mul.mpr ⟨a, ha, 1, Subgroup.one_mem _, mul_one a⟩)
  have hnorm : ∀ x ∈ AdelicSubgroupPoints.adelicPoints F G W,
      ∀ k ∈ AdelicSubgroupPoints.adelicPoints F G (unipotent χ),
        x * k * x⁻¹ ∈ AdelicSubgroupPoints.adelicPoints F G (unipotent χ) :=
    fun x hx k hk => conj_mem_unipotent χ (hWP _ hx) hk
  have hdec' : ∀ x ∈ AdelicSubgroupPoints.adelicPoints F G W,
      ∃ a ∈ AdelicSubgroupPoints.adelicPoints F G (centralizer χ ⊓ M),
        ∃ k ∈ AdelicSubgroupPoints.adelicPoints F G (unipotent χ), a * k = x := by
    intro x hx
    exact Set.mem_mul.mp ((Set.ext_iff.mp hA x).mp hx)
  refine ⟨hUW _, hAW, hnorm, hdisj, fun x hx => ?_, fun x hx hxR k hk a ha hka => ?_⟩
  · obtain ⟨a, ha, k, hk, rfl⟩ := hdec' x hx
    exact ⟨a * k * a⁻¹, hnorm a (hAW a ha) k hk, a, ha, by group⟩
  · obtain ⟨x₀, hx₀, rfl⟩ := hdesc x hx hxR
    obtain ⟨a₀, ha₀, u₀, hu₀, rfl⟩ := Set.mem_mul.mp ((Set.ext_iff.mp hF x₀).mp hx₀)
    have hra : AdelicGroupPoints.rational F G a₀ ∈
        AdelicSubgroupPoints.adelicPoints F G (centralizer χ ⊓ M) := rational_mem_carrier F _ ha₀
    have hru : AdelicGroupPoints.rational F G u₀ ∈
        AdelicSubgroupPoints.adelicPoints F G (unipotent χ) := rational_mem_carrier F _ hu₀
    rw [map_mul] at hka
    have hk' : (AdelicGroupPoints.rational F G a₀ * AdelicGroupPoints.rational F G u₀ *
        (AdelicGroupPoints.rational F G a₀)⁻¹)⁻¹ * k ∈
        AdelicSubgroupPoints.adelicPoints F G (unipotent χ) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hnorm _ (hAW _ hra) _ hru)) hk
    have heq : (AdelicGroupPoints.rational F G a₀ * AdelicGroupPoints.rational F G u₀ *
        (AdelicGroupPoints.rational F G a₀)⁻¹)⁻¹ * k =
        AdelicGroupPoints.rational F G a₀ * a⁻¹ := by
      rw [show k = AdelicGroupPoints.rational F G a₀ * AdelicGroupPoints.rational F G u₀ * a⁻¹ by
        rw [← hka, mul_inv_cancel_right]]
      group
    rw [heq] at hk'
    have h1 := hdisj _ (Subgroup.mul_mem _ hra (Subgroup.inv_mem _ ha)) hk'
    have : a = AdelicGroupPoints.rational F G a₀ := by
      rw [mul_inv_eq_one] at h1; exact h1.symm
    rw [this]
    exact ⟨a₀, rfl⟩

end Functor

section Assembly

variable (F : Type u) [Field F] [NumberField F]
  {G P U Q V P' U' Q' V' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- Conjugation by `w` carries the adelic points of `j` followed by the inverse inner
automorphism of `w` onto the adelic points of `j`. -/
theorem map_conj_adelicPoints_range_comp_innerIso_inv {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : H ⟶ G) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (j ≫ (G.innerIso w).inv))).map
        (MulAut.conj (innerAdelicPoint F G w)).toMonoidHom =
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_adelicPoints_range_comp_innerIso_inv]
  simp [MulAut.conj_symm_apply, mul_assoc]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Adelic points of a closed subgroup functor with an affine closed representative are closed. -/
theorem isClosed_adelicPoints_of_isRepresentedBy {W : SubgroupFunctor G}
    {H : GroupScheme (Spec (CommRingCat.of F))} {j : H ⟶ G} (hW : W.IsRepresentedBy j)
    (hj : IsClosedSubgroup j) :
    IsClosed (AdelicSubgroupPoints.adelicPoints F G W : Set (AdelicGroupPoints F G)) := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffine H.X.left := isAffine_of_isAffineHom j.hom.hom.left
  rw [← hW.2]
  exact AdelicSubgroupPoints.isClosed_adelicPoints_range F G j

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem rationalImage_le_adelicPoints_range {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : H ⟶ G) : rationalImage F j ≤
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨_, rfl⟩

variable [IsAffine P.X.left] [IsAffine V.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  (q : Q ⟶ G) (iV : V ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (f : P' ⟶ P) (iU' : U' ⟶ P') (g' : Q' ⟶ Q) (iV' : V' ⟶ Q')
  [IsClosedImmersion (iU' ≫ f ≫ p).hom.hom.left]
  [IsClosedImmersion (iV' ≫ g' ≫ q).hom.hom.left]

/-- **The subgroup structure of the unfolding identity.** Under the hypotheses of
`GeometricLemmaUnfoldingStatement`, the subgroup facts `UnfoldingSubgroupStructure` hold. -/
theorem unfoldingSubgroupStructure_of_datum (hG : IsConnectedReductive G)
    (hP : IsParabolicSubgroup p) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hQ : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hP' : IsParabolicSubgroup (f ≫ p)) (hU' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hQ' : IsParabolicSubgroup (g' ≫ q)) (hV' : LeviSubgroup.IsGeometricUnipotentRadical iV')
    (hDat : IsGeometricLemmaDatum p iU q iV f g' w) :
    UnfoldingSubgroupStructure F p iU q iV w f iU' g' iV' := by
  have := hG.isSeparated
  obtain ⟨χ, τ, ψ, θ, hψ, hθ, hUPψ, hPχ, hUχ, hPτ, hUτ, hPψ, hUψ, hPθ, hUθ⟩ :=
    exists_dynamic_unfolding_data F p iU q iV w f iU' g' iV' hG hP hU hQ hV hP' hU' hQ' hV' hDat
  have hw : innerAdelicPoint F G w ∈ AdelicGroupPoints.rationalSubgroup F G := by
    rw [innerAdelicPoint_eq_rational]; exact ⟨_, rfl⟩
  have hjU' : IsClosedSubgroup (iU' ≫ f ≫ p) :=
    (inferInstance : IsClosedImmersion (iU' ≫ f ≫ p).hom.hom.left)
  have hjV' : IsClosedSubgroup ((iV' ≫ g' ≫ q) ≫ (G.innerIso w).inv) := by
    have h := (show IsClosedSubgroup (iV' ≫ g' ≫ q) from
      (inferInstance : IsClosedImmersion (iV' ≫ g' ≫ q).hom.hom.left)).comp_iso (G.innerIso w).symm
    rwa [Iso.symm_hom] at h
  have hVa : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) :
      Set (AdelicGroupPoints F G)) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G _
  have hUτclosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G (unipotent τ) :
      Set (AdelicGroupPoints F G)) := by
    have : (AdelicSubgroupPoints.adelicPoints F G (unipotent τ) : Set (AdelicGroupPoints F G)) =
        (fun x => innerAdelicPoint F G w * x * (innerAdelicPoint F G w)⁻¹) ⁻¹'
          (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) := by
      ext x
      rw [← hUτ, ← Category.assoc]
      exact mem_adelicPoints_range_comp_innerIso_inv F (iV ≫ q) w x
    rw [this]
    exact hVa.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hUχclosed : IsClosed (AdelicSubgroupPoints.adelicPoints F G (unipotent χ) :
      Set (AdelicGroupPoints F G)) := by
    have : IsClosedImmersion iU.hom.hom.left := hU.1.isClosedSubgroup
    have : IsAffine U.X.left := isAffine_of_isAffineHom iU.hom.hom.left
    have : IsClosedImmersion (iU ≫ p).hom.hom.left :=
      hU.1.isClosedSubgroup.comp (inferInstance : IsClosedImmersion p.hom.hom.left)
    rw [← hUχ]
    exact AdelicSubgroupPoints.isClosed_adelicPoints_range F G _
  have hZclosed : ∀ ξ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G,
      IsClosed (AdelicSubgroupPoints.adelicPoints F G (centralizer ξ) :
        Set (AdelicGroupPoints F G)) := fun ξ =>
    isClosed_adelicPoints_of_isRepresentedBy F (Affine.isRepresentedBy_centralizerHom ξ)
      (Affine.isClosedSubgroup_centralizerHom ξ)
  have hconjR : ∀ x, MulAut.conj (innerAdelicPoint F G w) x ∈
      AdelicGroupPoints.rationalSubgroup F G ↔ x ∈ AdelicGroupPoints.rationalSubgroup F G := by
    intro x
    have := LeftCosetSpace.conj_mem_iff (Subgroup.inv_mem _ hw) x
    simpa [MulAut.conj_apply] using this
  have hUa : AdelicGroupPoints.parabolicUnipotentImage F p iU =
      AdelicSubgroupPoints.adelicPoints F G (unipotent χ) := by
    rw [← hUχ]; rfl
  refine ⟨?_, ?_, ?_⟩
  · -- the rational stabilizer lies in the conjugate of `U'`
    intro v hv _ hvP
    have h1 : (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w ∈
        AdelicSubgroupPoints.adelicPoints F G (unipotent τ) := by
      rw [← hUτ, ← Category.assoc, mem_adelicPoints_range_comp_innerIso_inv]
      simpa [mul_assoc] using hv
    have h2 : (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w ∈
        AdelicSubgroupPoints.adelicPoints F G (parabolic χ) := by
      rw [← hPχ]; exact rationalImage_le_adelicPoints_range F p hvP
    have h3 := hUPψ _ ⟨h1, h2⟩
    rw [← hUψ] at h3
    exact h3
  · -- the decomposition of `U'`
    obtain ⟨hKH, hAH, hn, hd, hdec, hrat⟩ := isRationalSemidirect_of_dynamic F χ (unipotent τ)
      (unipotent ψ) hψ.2.2.2.1 hψ.2.2.1 ((unipotent_le_parabolic ψ).trans hψ.1) (by
        rintro x hx ⟨x₀, rfl⟩
        refine ⟨x₀, ?_, rfl⟩
        rw [← hUψ] at hx ⊢
        exact (AdelicGroupPoints.rational_mem_adelicPoints_range_iff hjU' x₀).mp hx)
    rw [hUa, hUψ]
    refine ⟨AdelicSubgroupPoints.adelicPoints F G (centralizer χ ⊓ unipotent τ),
      (hZclosed χ).inter hUτclosed, hAH, fun a ha => ?_, hKH, hn, hd, hdec, hrat⟩
    have h : a ∈ AdelicSubgroupPoints.adelicPoints F G (unipotent τ) := ha.2
    rw [← hUτ, ← Category.assoc, mem_adelicPoints_range_comp_innerIso_inv] at h
    exact h
  · -- the decomposition of `V'`
    have hpkg := (isRationalSemidirect_of_dynamic F τ (unipotent χ) (unipotent θ) hθ.2.2.2.1
      hθ.2.2.1 ((unipotent_le_parabolic θ).trans hθ.1) (by
        rintro x hx ⟨x₀, rfl⟩
        refine ⟨x₀, ?_, rfl⟩
        rw [← hUθ, show iV' ≫ g' ≫ q ≫ (G.innerIso w).inv =
          (iV' ≫ g' ≫ q) ≫ (G.innerIso w).inv by simp only [Category.assoc]] at hx ⊢
        exact (AdelicGroupPoints.rational_mem_adelicPoints_range_iff hjV' x₀).mp hx)).map
      (MulAut.conj (innerAdelicPoint F G w)) hconjR
    have hV'map : (AdelicSubgroupPoints.adelicPoints F G (unipotent θ)).map
        (MulAut.conj (innerAdelicPoint F G w)).toMonoidHom =
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV' ≫ g' ≫ q)) := by
      rw [← hUθ, show iV' ≫ g' ≫ q ≫ (G.innerIso w).inv =
        (iV' ≫ g' ≫ q) ≫ (G.innerIso w).inv by simp only [Category.assoc],
        map_conj_adelicPoints_range_comp_innerIso_inv]
    have hVmap : (AdelicSubgroupPoints.adelicPoints F G (unipotent τ)).map
        (MulAut.conj (innerAdelicPoint F G w)).toMonoidHom =
        AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) := by
      rw [← hUτ, ← Category.assoc, map_conj_adelicPoints_range_comp_innerIso_inv]
    rw [hV'map, hVmap] at hpkg
    obtain ⟨hKH, hAH, hn, hd, hdec, hrat⟩ := hpkg
    have hBclosed : IsClosed (((AdelicSubgroupPoints.adelicPoints F G
        (centralizer τ ⊓ unipotent χ)).map (MulAut.conj (innerAdelicPoint F G w)).toMonoidHom :
        Subgroup (AdelicGroupPoints F G)) : Set (AdelicGroupPoints F G)) := by
      have : (((AdelicSubgroupPoints.adelicPoints F G (centralizer τ ⊓ unipotent χ)).map
          (MulAut.conj (innerAdelicPoint F G w)).toMonoidHom : Subgroup (AdelicGroupPoints F G)) :
            Set (AdelicGroupPoints F G)) =
          (fun x => (innerAdelicPoint F G w)⁻¹ * x * innerAdelicPoint F G w) ⁻¹'
            (AdelicSubgroupPoints.adelicPoints F G (centralizer τ ⊓ unipotent χ)) := by
        ext x
        rw [SetLike.mem_coe, Subgroup.mem_map_equiv]
        simp [MulAut.conj_symm_apply]
      rw [this]
      exact ((hZclosed τ).inter hUχclosed).preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    refine ⟨_, hBclosed, hAH, fun b hb => ?_, hKH, hn, hd, hdec, hrat⟩
    rw [Subgroup.mem_map_equiv] at hb
    rw [hUa]
    have h2 : (MulAut.conj (innerAdelicPoint F G w)).symm b ∈
        AdelicSubgroupPoints.adelicPoints F G (unipotent χ) := hb.2
    simpa [MulAut.conj_symm_apply] using h2

end Assembly

end Langlands.Global
